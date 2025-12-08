#!/usr/bin/env -S python3 -u
"""Rename variables and constants in SMT files so that they are easier to read."""
import argparse
import os
from pathlib import Path

import z3

from converter import NNFConverter
from printer import BoolStructPrinter


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


def name_generator(prefix_chars, fallback_prefix):
    """Generator that yields names from a list of characters, then numbered names."""
    for char in prefix_chars:
        yield char
    counter = 0
    while True:
        yield f"{fallback_prefix}{counter}"
        counter += 1


class Renamer:
    def __init__(self, filepath, base_path, nnf):
        self.filepath = filepath
        self.base_path = base_path
        self.constant_map = {}
        self.function_map = {}
        self.nnf = nnf

        self.const_gen = name_generator("abcde", "c_")
        self.func_gen = name_generator("fgh", "f_")
        self.var_gen = None

        self.collect_cache = set()
        self.rename_cache = {}

    def is_const(self, expr):
        return (
            z3.is_app(expr)
            and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
            and expr.decl().arity() == 0
        )

    def is_func(self, expr):
        return (
            z3.is_app(expr)
            and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
            and expr.decl().arity() > 0
        )

    def collect_symbols(self, expr):
        """Walk the expression and collect all constants and functions to rename."""
        expr_id = expr.get_id()
        if expr_id in self.collect_cache:
            return

        self.collect_cache.add(expr_id)
        if self.is_const(expr):
            const_decl = expr.decl()
            new_name = next(self.const_gen)
            new_const = z3.Const(new_name, expr.sort())
            self.constant_map[const_decl] = (expr, new_const)
        elif self.is_func(expr):
            func_decl = expr.decl()
            new_name = next(self.func_gen)
            arity = func_decl.arity()
            domain = [func_decl.domain(i) for i in range(arity)]
            range_sort = func_decl.range()
            new_func = z3.Function(new_name, *domain, range_sort)
            var_list = [z3.Var(i, func_decl.domain(i)) for i in range(arity)]
            new_expr = new_func(*var_list)
            self.function_map[func_decl] = new_expr
        for child in expr.children():
            self.collect_symbols(child)

    def rename_quantifiers(self, expr):
        """Recursively rename quantifier variables."""
        expr_id = expr.get_id()
        if expr_id in self.rename_cache:
            return self.rename_cache[expr_id]

        result = None
        if z3.is_quantifier(expr):
            num_vars = expr.num_vars()
            assert self.var_gen is not None
            new_var_names = [next(self.var_gen) for _ in range(num_vars)]
            new_body = self.rename_quantifiers(expr.body())
            var_sorts = [expr.var_sort(i) for i in range(num_vars)]
            new_bound_vars = [
                z3.Const(new_var_names[i], var_sorts[i]) for i in range(num_vars)
            ]
            new_body = z3.substitute_vars(new_body, *reversed(new_bound_vars))
            if expr.is_forall():
                result = z3.ForAll(new_bound_vars, new_body)
            else:
                result = z3.Exists(new_bound_vars, new_body)
        elif z3.is_app(expr):
            new_children = [self.rename_quantifiers(child) for child in expr.children()]
            if new_children:
                result = expr.decl()(*new_children)
            else:
                result = expr
        else:
            result = expr
        self.rename_cache[expr_id] = result
        return result

    def process_formula(self, formula):
        """Process a single formula and return renamed version."""
        if self.nnf:
            converter = NNFConverter(formula)
            formula = converter.convert()

        self.collect_symbols(formula)

        if self.constant_map:
            const_subs = [(old, new) for old, new in self.constant_map.values()]
            formula = z3.substitute(formula, *const_subs)

        if self.function_map:
            func_subs = [
                (old_func, new_expr) for old_func, new_expr in self.function_map.items()
            ]
            formula = z3.substitute_funs(formula, *func_subs)

        self.rename_cache = {}
        self.var_gen = name_generator("xyzv", "x_")
        formula = self.rename_quantifiers(formula)

        return z3.simplify(formula, no_let=True)

    def process_file(self):
        s = z3.Solver()
        s.from_file(self.filepath)

        renamed_assertions = []
        for assertion in s.assertions():
            renamed_assertion = self.process_formula(assertion)
            renamed_assertions.append(renamed_assertion)
        return renamed_assertions

    def write(self, output_dir, assertions):
        renamed_solver = z3.Solver()
        renamed_solver.add(assertions)

        input_path = Path(self.filepath)
        relative_path = input_path.relative_to(self.base_path)
        output_path = output_dir / relative_path
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, "w") as f:
            f.write(renamed_solver.to_smt2())
        print(f"  -> Written to: {output_path}")

    def to_dotformat(self, output_dir, assertions):
        input_path = Path(self.filepath)
        relative_path = input_path.relative_to(self.base_path)
        output_path = output_dir / relative_path
        output_path = output_path.with_suffix(".dot")
        output_path.parent.mkdir(parents=True, exist_ok=True)

        printer = BoolStructPrinter(assertions)
        with open(output_path, "w") as f:
            f.write(printer.to_dotformat())
        print(f"  -> DOT written to: {output_path}")


def main():
    parser = argparse.ArgumentParser(
        description="Rename variable names in SMT files using Z3"
    )
    parser.add_argument("input_path", help="Input directory or file path to rename")
    parser.add_argument("--nnf", help="Convert to nnf", action="store_true")
    parser.add_argument("--dot", help="Generate dotformat", action="store_true")
    args = parser.parse_args()

    smtlib_files = []
    base_path = None

    if os.path.isfile(args.input_path):
        smtlib_files = [args.input_path]
        base_path = Path(args.input_path).parent
    else:
        smtlib_files = find_smtlib_files(args.input_path)
        base_path = Path(args.input_path)

    if not smtlib_files:
        print("No SMT-LIB files found in the specified path.")
        return

    output_dir = Path(str(base_path) + "_renamed")
    output_dir.mkdir(exist_ok=True)
    print(f"Output directory: {output_dir}")

    print(f"Found {len(smtlib_files)} SMT-LIB files to analyze.")
    for i, filepath in enumerate(smtlib_files):
        print(f"Processing file {i+1}/{len(smtlib_files)}: {filepath}")
        # try:
        renamer = Renamer(filepath, base_path, args.nnf)
        assertions = renamer.process_file()
        renamer.write(output_dir, assertions)
        if args.dot:
            renamer.to_dotformat(output_dir, assertions)
        # except Exception as e:
        #     print(f"  -> Error processing file: {e}")


if __name__ == "__main__":
    main()
