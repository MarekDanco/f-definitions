#!/usr/bin/env -S python3 -u
"""Module for testing ReqPivot condition"""

import argparse
from functools import cache
from typing import Literal

import z3

from utils import has_quantifiers, is_func, is_ground, is_offset_term


@cache
def _get_entities_recursive(expr):
    """Recursively extract entities from a Z3 expression."""
    if is_ground(expr):
        return frozenset()
    if is_func(expr):
        assert expr.decl().arity() == 1, f"Function {expr} has arity greater than 1"
        assert is_offset_term(
            expr.arg(0)
        ), f"The argument of {expr} is not an offset term"
        return frozenset({expr})

    res = set()
    for child in expr.children():
        res |= _get_entities_recursive(child)

    return frozenset(res)


class ReqPivot:
    def __init__(self, formula):
        self.formula = formula
        self.entities = []

    def _normalize(self, direction: Literal["up", "down"]):
        # TODO deal with conjunction and disjunction
        if z3.is_and(self.formula) or z3.is_or(self.formula):
            assert False, "Not implemented"
        return self.formula

    def _bigger_offset(self, a, b, direction: Literal["up", "down"]):
        # TODO extract offsets and compare
        assert False, "Not implemented"

    def _split_entities(self, direction: Literal["up", "down"]):
        existential, target = [], self.entities[0]
        for e in self.entities:
            if self._bigger_offset(e, target, direction):
                existential.append(target)
                target = e
            else:
                existential.append(e)
        return existential, target

    def test(self, direction: Literal["up", "down"]):
        self.entities = list(_get_entities_recursive(self.formula))
        assert self.entities, "Found no entities"
        # norm_entities = self._normalize(direction)
        existential, target = self._split_entities(direction)
        existential_consts = [z3.FreshConst(e.sort()) for e in existential]
        existential_subs = [
            (e, e_const) for e, e_const in zip(existential, existential_consts)
        ]
        target_const = z3.FreshConst(target.sort())
        target_sub = [(target, target_const)]

        test_body = z3.substitute(self.formula, existential_subs + target_sub)
        test_formula = z3.Exists(existential_consts, z3.ForAll(target_const, test_body))

        # TODO create a solver and solve test_formula


def main():
    parser = argparse.ArgumentParser(
        description="Test whether assertions in an SMT file satisfy ReqPivot"
    )
    parser.add_argument("input_file", help="Input SMT file to test")
    args = parser.parse_args()

    s = z3.Solver()
    s.from_file(args.input_file)
    print(f"input: {args.input_file}")
    assertions = [a for a in s.assertions() if has_quantifiers(a)]  # type: ignore
    for a in assertions:
        print(a)
        rp = ReqPivot(a)
        print("up", rp.test("up"))
        print("down", rp.test("down"))


if __name__ == "__main__":
    main()
