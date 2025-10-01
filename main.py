#!/usr/bin/env python3

"""Function synthesis project"""

import sys
import argparse
import z3
from formula import Formula


def test_var_chain(formula):
    return formula.get_var_chain(formula.formula, formula.formula.body().arg(1), [])


def parse_command_line() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Tool for function synthesis")
    parser.add_argument(
        "filename",
        help="Filename with input formula",
        default="-",
        nargs="?",
        type=str,
    )
    parser.add_argument(
        "-v", "--verbose", help="Show all messages", action="store_true"
    )
    args = parser.parse_args()
    return args


def display_formula(formula, message=None) -> None:
    if message is not None:
        print(f"{message} {formula}", flush=True)
    else:
        print(formula, flush=True)


def display_constraints(constraints, message=None) -> None:
    for constraint in constraints:
        display_formula(constraint, message)


def parse_input_file(file_path: str):
    s = z3.Solver()
    input_path = "examples/test.smt2" if file_path == "-" else file_path
    s.from_file(input_path)
    constraints = s.assertions()
    return constraints


def main():
    args = parse_command_line()
    constraints = parse_input_file(args.filename)
    for cons in constraints:
        f = Formula(cons)
        display_formula(f.formula)
        print()
        f.test_deskolemize(f.formula)


if __name__ == "__main__":
    sys.exit(main())
