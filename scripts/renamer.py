#!/usr/bin/env -S python3 -u
"""Rename variables and constants in SMT files so that they are easier to read."""
import argparse
import os
from pathlib import Path

import z3

from converter import NNFConverter
from printer import BoolStructPrinter

CONSTANTS = list("abcdefghijklm")
VARIABLES = list("xyzvwnopqrstu")


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


class Renamer:
    def __init__(self, filepath, base_path, nnf):
        self.filepath = filepath
        self.base_path = base_path
        self.constant_subs = []
        self.constant_map = {}
        self.var_counter = 0
        self.const_counter = 0
        self.cache = {}
        self.nnf = nnf

    def is_const(self, expr):
        return (
            z3.is_app(expr)
            and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
            and expr.decl().arity() == 0
        )

    def rename_const(self, const):
        const_decl = const.decl()
        if const_decl in self.constant_map:
            return self.constant_map[const_decl]
        if len(self.constant_subs) < len(CONSTANTS):
            new_name = CONSTANTS[len(self.constant_subs)]
        else:
            new_name = f"const_{self.const_counter}"
            self.const_counter += 1
        new_const = z3.Const(new_name, const.sort())
        self.constant_map[const_decl] = new_const
        self.constant_subs.append((const, new_const))
        return new_const

    def rename_quantifier(self, quantifier):
        num_vars = quantifier.num_vars()
        new_var_counter = self.var_counter + num_vars
        if new_var_counter <= len(VARIABLES):
            new_var_names = VARIABLES[self.var_counter : new_var_counter]
        else:
            new_var_names = [f"var_{self.var_counter + i}" for i in range(num_vars)]
        self.var_counter = new_var_counter

        new_body = self.rename_expr(quantifier.body())

        var_sorts = [quantifier.var_sort(i) for i in range(num_vars)]
        new_bound_vars = [
            z3.Const(new_var_names[i], var_sorts[i]) for i in range(num_vars)
        ]
        if quantifier.is_forall():
            return z3.ForAll(
                new_bound_vars,
                new_body,
            )
        return z3.Exists(
            new_bound_vars,
            new_body,
        )

    def rename_expr(self, expr):
        """Recursively rename an expression, rebuilding quantifiers with new names."""
        expr_id = expr.get_id()
        if expr_id in self.cache:
            return self.cache[expr_id]
        result = None
        if self.is_const(expr):
            result = self.rename_const(expr)
        elif z3.is_var(expr):
            result = expr
        elif z3.is_quantifier(expr):
            result = self.rename_quantifier(expr)
        elif z3.is_app(expr):
            new_children = [self.rename_expr(child) for child in expr.children()]
            if new_children:
                result = expr.decl()(*new_children)
            else:
                result = expr
        else:
            result = expr
        self.cache[expr_id] = result
        return result

    def process_formula(self, formula):
        """Process a single formula and return renamed version."""
        self.var_counter = 0
        self.cache = {}
        if self.nnf:
            converter = NNFConverter(formula)
            formula = converter.convert()
        pre_simplify = self.rename_expr(formula)
        return z3.simplify(pre_simplify, no_let=True)

    def process_file(self, output_dir):
        """Process the SMT file and write renamed version."""
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
        try:
            renamer = Renamer(filepath, base_path, args.nnf)
            assertions = renamer.process_file(output_dir)
            renamer.write(output_dir, assertions)
            if args.dot:
                renamer.to_dotformat(output_dir, assertions)
        except Exception as e:
            print(f"  -> Error processing file: {e}")


if __name__ == "__main__":
    main()
