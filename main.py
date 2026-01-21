#!/usr/bin/env python3

"""Function synthesis project"""

import argparse
import sys

import z3


def divide_constraints(constraints):
    ground = []
    quantified = []
    for cons in constraints:
        if z3.is_quantifier(cons):
            quantified.append(cons)
        else:
            ground.append(cons)
    return ground, quantified


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
        "-v",
        "--verbosity",
        default=0,
        type=int,
        choices=range(0, 4),
        help="Verbosity level for main module (0–3)",
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
    input_path = "examples/test2.smt2" if file_path == "-" else file_path
    s.from_file(input_path)
    constraints = s.assertions()
    return constraints


def _set_verbosity(lvl):
    global VERBOSITY
    VERBOSITY = lvl


def main():
    args = parse_command_line()
    _set_verbosity(args.verbosity)


if __name__ == "__main__":
    sys.exit(main())
