#!/usr/bin/env -S python3 -u
"""Extract admissible subformulas for synthesis."""
import argparse
import os
from pathlib import Path

import z3

from converter import NNFConverter


def find_smtlib_files(root_path: str):
    """Find all SMT files anywhere in the root_path tree."""
    smtlib_files = []
    root = Path(root_path)
    if not root.exists():
        print(f"Error: Path '{root_path}' does not exist")
        return []
    for file_path in root.rglob("*"):
        if file_path.is_file() and file_path.suffix.lower() == ".smt2":
            smtlib_files.append(str(file_path))
    return smtlib_files


class Formula:
    def __init__(self):
        self._is_ground_cache = {}
        self._has_quantifier_cache = {}

    def _is_func(self, expr):
        return z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED

    def _is_const(self, expr):
        return self._is_func(expr) and expr.decl().arity == 0

    def _is_arith_op(self, expr):
        return z3.is_add(expr) or z3.is_sub(expr)

    def _is_select(self, expr):
        return z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_SELECT

    def _is_store(self, expr):
        return z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_STORE

    def _is_ground(self, expr):
        expr_id = expr.get_id()
        if expr_id in self._is_ground_cache:
            return self._is_ground_cache[expr_id]
        if z3.is_var(expr):
            return False
        result = all(self._is_ground(child) for child in expr.children())
        self._is_ground_cache[expr_id] = result
        return result


class SubformulaFilter(Formula):
    def __init__(self, formula):
        super().__init__()
        self.formula = formula

    def _offset_vars_ground(self, children):
        vars = []
        ground = []
        for c in children:
            if self._is_ground(c):
                ground.append(c)
            elif z3.is_var(c):
                vars.append(c)
            else:
                return [], []
        return vars, ground

    def _is_offset_term(self, expr):
        if z3.is_var(expr):
            return True
        if not (z3.is_add(expr) or z3.is_sub(expr)):
            return False
        children = list(expr.children())
        vars, ground = self._offset_vars_ground(children)
        if len(vars) == 0 and len(ground) == 0:
            return False
        if len(vars) == 1:
            return True
        return False

    def _check_func_args(self, args):
        """All function arguments must be offset terms."""
        return all(self._is_offset_term(arg) for arg in args)

    def _filter_helper(self, expr):
        """Filter a quantified assertion."""
        if z3.is_quantifier(expr):
            # Disallow nested quantifiers
            return None
        if self._is_ground(expr):
            return expr
        if z3.is_var(expr):
            return expr
        if self._is_func(expr):
            args = [expr.arg(i) for i in range(expr.num_args())]
            if self._check_func_args(args):
                return expr
            else:
                return None
        if self._is_select(expr) or self._is_store(expr):
            index = expr.arg(1)
            if self._is_offset_term(index):
                return expr
            else:
                return None
        if z3.is_and(expr):
            filtered_children = []
            for child in expr.children():
                filtered = self._filter_helper(child)
                if filtered is None:
                    filtered_children.append(z3.BoolVal(True, ctx=expr.ctx))
                else:
                    filtered_children.append(filtered)
            return z3.And(*filtered_children)
        if z3.is_or(expr):
            filtered_children = []
            for child in expr.children():
                filtered = self._filter_helper(child)
                if filtered is None:
                    filtered_children.append(z3.BoolVal(False, ctx=expr.ctx))
                else:
                    filtered_children.append(filtered)
            return z3.Or(*filtered_children)
        if z3.is_not(expr):
            filtered = self._filter_helper(expr.arg(0))
            if filtered is None:
                return None
            return z3.Not(filtered)
        if z3.is_app(expr):
            filtered_children = [
                self._filter_helper(child) for child in expr.children()
            ]
            if any(c is None for c in filtered_children):
                return None
            return expr

        return None

    def filter(self):
        """Filter a quantified subformula."""
        result = self._filter_helper(self.formula)
        return result


class Filter(Formula):
    def __init__(self, filepath, base_path):
        super().__init__()
        self.filepath = filepath
        self.base_path = base_path
        self._filter_cache = {}

    def filter(self, expr):
        expr_id = expr.get_id()
        if expr_id in self._filter_cache:
            return self._filter_cache[expr_id]

        result = None

        if z3.is_quantifier(expr):
            num_vars = expr.num_vars()
            if num_vars != 1:
                self._filter_cache[expr_id] = None
                return None

            sub_filter = SubformulaFilter(expr.body())
            new_body = sub_filter.filter()
            if new_body is None:
                return None

            var_names = [expr.var_name(i) for i in range(num_vars)]
            var_sorts = [expr.var_sort(i) for i in range(num_vars)]

            bound_vars = [z3.Const(var_names[i], var_sorts[i]) for i in range(num_vars)]
            new_body_with_consts = z3.substitute_vars(new_body, *reversed(bound_vars))
            if expr.is_forall():
                result = z3.ForAll(
                    bound_vars,
                    new_body_with_consts,
                )
            else:
                result = z3.Exists(
                    bound_vars,
                    new_body_with_consts,
                )
        elif z3.is_and(expr):
            filtered_children = [self.filter(child) for child in expr.children()]
            not_none_filter = [c for c in filtered_children if c is not None]
            if not_none_filter:
                result = z3.And(*not_none_filter)
        elif z3.is_or(expr):
            filtered_children = [self.filter(child) for child in expr.children()]
            not_none_filter = [c for c in filtered_children if c is not None]
            if not_none_filter:
                result = z3.Or(*not_none_filter)
        elif z3.is_not(expr):
            filtered = self.filter(expr.arg(0))
            if filtered is not None:
                result = z3.Not(filtered)
        else:
            result = expr

        self._filter_cache[expr_id] = result
        return result

    def process_assertion(self, formula):
        self._filter_cache = {}
        nnf_conv = NNFConverter(formula)
        formula = nnf_conv.convert()
        filtered_assertion = self.filter(formula)
        if filtered_assertion is None:
            return None, True
        is_ground = self._is_ground(filtered_assertion)
        filtered_assertion = z3.simplify(filtered_assertion, no_let=True)
        return filtered_assertion, is_ground

    def process_file(self, output_dir):
        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        solver.from_file(self.filepath)

        filtered_solver = z3.Solver(ctx=ctx)
        processed = [
            self.process_assertion(assertion) for assertion in solver.assertions()
        ]

        if all(is_ground for _, is_ground in processed):
            print("  -> Skipped: No quantified assertions remain after filtering")
            return
        for filtered_assertion, _ in processed:
            if filtered_assertion is not None:
                filtered_solver.add(filtered_assertion)

        input_path = Path(self.filepath)
        relative_path = input_path.relative_to(self.base_path)
        output_path = output_dir / relative_path
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, "w") as f:
            f.write(filtered_solver.to_smt2())
        print(f"  -> Written to: {output_path}")


def main():
    parser = argparse.ArgumentParser(
        description="Filter assertions in SMT files for synthesis."
    )
    parser.add_argument(
        "input_path", nargs="+", help="Input directory or file path to analyze"
    )
    args = parser.parse_args()

    smtlib_files = []
    base_path = None

    if os.path.isfile(args.input_path[0]):
        smtlib_files = [args.input_path[0]]
        base_path = Path(args.input_path[0]).parent
    else:
        for path in args.input_path:
            smtlib_files += find_smtlib_files(path)
        base_path = Path(args.input_path[0])

    if not smtlib_files:
        print("No SMT-LIB files found in the specified path.")
        return

    output_dir = Path(str(base_path) + "_filtered")
    output_dir.mkdir(exist_ok=True)
    print(f"Output directory: {output_dir}")

    print(f"Found {len(smtlib_files)} SMT-LIB files to analyze.")
    for i, filepath in enumerate(smtlib_files):
        print(f"Processing file {i+1}/{len(smtlib_files)}: {filepath}")
        try:
            filter = Filter(filepath, base_path)
            filter.process_file(output_dir)
        except Exception as e:
            print(f"  -> Error processing file: {e}")


if __name__ == "__main__":
    main()
