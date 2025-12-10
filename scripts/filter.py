#!/usr/bin/env -S python3 -u
"""Extract admissible UFLIA subformulas for synthesis."""
import argparse
import sys
from functools import lru_cache
from pathlib import Path

import z3

from converter import NNFConverter

VERBOSE = 2


def log(severity, message):
    if severity > VERBOSE:
        return
    print(message, flush=True)


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

    def _is_ground(self, expr):
        expr_id = expr.get_id()
        if expr_id in self._is_ground_cache:
            return self._is_ground_cache[expr_id]
        if z3.is_var(expr):
            return False
        result = all(self._is_ground(child) for child in expr.children())
        self._is_ground_cache[expr_id] = result
        return result

    def _offset_vars_ground(self, children):
        vs = []
        # ground = []
        for c in children:
            # if self._is_ground(c):
            #     ground.append(c)
            if z3.is_var(c):
                vs.append(c)
            # else:
            #     return [], []
        return vs  # , ground

    def _is_offset_term(self, expr):
        if z3.is_var(expr):
            return True
        if not (z3.is_add(expr) or z3.is_sub(expr)):
            return False
        children = list(expr.children())
        vs = self._offset_vars_ground(children)
        if len(vs) == 1:
            return True
        return False


class SubformulaFilter(Formula):
    """Filter a quantified subformula"""

    def __init__(self, formula):
        super().__init__()
        self.formula = formula

    def _check_func_args(self, args):
        """All function arguments must be offset terms."""
        if len(args) > 1:
            return False  # Mikolas fix
        return all(self._is_offset_term(arg) for arg in args)

    def _filter_helper(self, expr):
        if z3.is_quantifier(expr):
            return None  # disallow nested quantifiers
        if self._is_ground(expr):
            return expr
        if z3.is_var(expr):
            return expr
        if self._is_func(expr):
            if expr.sort() != z3.IntSort():
                return None  # only integer functions
            args = [expr.arg(i) for i in range(expr.num_args())]
            if self._check_func_args(args):
                return expr
            else:
                return None
        if z3.is_and(expr):
            filtered_children = []
            for child in expr.children():
                filtered = self._filter_helper(child)
                if filtered is not None:
                    filtered_children.append(filtered)
            if not filtered_children:
                return None
            return z3.And(*filtered_children)
        if z3.is_or(expr):
            filtered_children = []
            for child in expr.children():
                filtered = self._filter_helper(child)
                if filtered is not None:
                    filtered_children.append(filtered)
            if not filtered_children:
                return None
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
    def __init__(self):
        super().__init__()
        self._filter_cache = {}

    @lru_cache(maxsize=None)
    def _contains_entity(self, expr):
        """Check if filtered quantifier body contains any entities"""
        if self._is_func(expr):
            if self._is_ground(expr):
                return False
            if self._is_offset_term(expr.arg(0)):
                return True
        return any(self._contains_entity(child) for child in expr.children())

    @lru_cache(maxsize=None)
    def _contains_entity_addition(self, expr):
        if self._is_arith_op(expr):
            return self._contains_entity(expr)
        else:
            return any(
                self._contains_entity_addition(child) for child in expr.children()
            )

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
                self._filter_cache[expr_id] = None
                return None
            assert isinstance(new_body, z3.ExprRef)
            if not self._contains_entity(new_body):
                self._filter_cache[expr_id] = None
                return None

            var_names = [expr.var_name(i) for i in range(num_vars)]
            var_sorts = [expr.var_sort(i) for i in range(num_vars)]

            bound_vars = [z3.Const(var_names[i], var_sorts[i]) for i in range(num_vars)]
            new_body_with_consts = z3.substitute_vars(
                new_body, *reversed(bound_vars)
            )  # de bruijn
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


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Filter assertions in a single SMT file for synthesis"
    )
    parser.add_argument("input_file", help="Input SMT file to filter")
    parser.add_argument(
        "--output-dir",
        help="Base directory to preserve relative structure (default: parent of input file)",
    )
    args = parser.parse_args()

    input_path = Path(args.input_file).resolve()

    if not input_path.exists():
        log(1, f"Error: File '{args.input_file}' does not exist")
        return 1

    if not input_path.suffix.lower() == ".smt2":
        log(1, "Error: File must have .smt2 extension")
        return 1

    log(2, f"Processing file '{args.input_file}'")

    base_dir = input_path.parent
    if args.output_dir:
        output_dir = Path(args.output_dir).resolve()
    else:
        output_dir = Path(str(base_dir) + "_filtered")
    relative_path = input_path.relative_to(base_dir)
    output_path = output_dir / relative_path

    output_path.parent.mkdir(parents=True, exist_ok=True)

    try:
        solver = z3.Solver()
        solver.from_file(str(input_path))

        filter_obj = Filter()
        filtered_solver = z3.Solver()
        processed = [
            filter_obj.process_assertion(assertion) for assertion in solver.assertions()
        ]

        if all(is_ground for _, is_ground in processed):
            log(2, "  -> Skipped: No quantified assertions remain after filtering")
            return 0

        for filtered_assertion, _ in processed:
            if filtered_assertion is not None:
                filtered_solver.add(filtered_assertion)

        with open(output_path, "w") as f:
            f.write(filtered_solver.to_smt2())
        log(2, f"  -> Written to: {output_path}")
        return 0
    except Exception as e:
        log(0, f"  -> Error processing file '{args.input_file}'\n{e}")
        import traceback

        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
