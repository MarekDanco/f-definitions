#!/usr/bin/env python3

"""Function synthesis project"""

import argparse
import sys
from typing import Iterable, cast

import z3

from formula import Ground, Quantified


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
    input_path = "examples/test2.smt2" if file_path == "-" else file_path
    s.from_file(input_path)
    constraints = s.assertions()
    return constraints


def test(ground, quantified):
    print("===Ground===")
    for formula in ground:
        display_formula(formula.formula)

    print("===Quantified===")
    for formula in quantified:
        display_formula(formula.formula)
        conjuncts = formula.conjuncts
        for conj in conjuncts:
            print("Conjunct: ", conj.conjunct)
            print("Cells", conj.cells)
            print("     maximal offset: ", conj.max_offset)
            print("     minimal offset: ", conj.min_offset)
            print("Rewritten around 0 up: ", conj.normalize(0, "up"))
            print("Rewritten around 0 down: ", conj.normalize(0, "down"))


def main():
    args = parse_command_line()
    constraints = list(cast(Iterable, parse_input_file(args.filename)))
    display_constraints(constraints)
    ground, quantified = divide_constraints(constraints)
    ground = list(map(Ground, ground))
    quantified = list(map(Quantified, quantified))
    test(ground, quantified)


if __name__ == "__main__":
    sys.exit(main())
