#!/usr/bin/env -S python3 -u
"""Module for testing ReqPivot condition"""

import argparse
from typing import Literal

import z3

from conjunct import ConjunctionsManager
from utils import get_entities, has_quantifiers, simplify, split_entities


class ReqPivot:
    def __init__(self):
        self.model: None | z3.ModelRef = None  # ground model

    def _get_subs(self, entities):
        """Get entity substitutions"""
        constants = [z3.FreshConst(e.sort()) for e in entities]
        return constants, [(e, c) for e, c in zip(entities, constants)]

    def _process(self, assertion, direction: Literal["up", "down"]):
        assert z3.is_quantifier(assertion), f"{assertion} is not quantified"
        matrix = assertion.body()
        if not z3.is_and(matrix):
            return simplify(matrix), list(get_entities(matrix))
        conj_manager = ConjunctionsManager(matrix, direction)
        return conj_manager.manage()

    def test(self, assertion, direction: Literal["up", "down"]):
        formula, self.entities = self._process(assertion, direction)
        assert self.entities, "Found no entities"
        existential, target = split_entities(self.entities, direction)

        existential_consts, existential_subs = self._get_subs(existential)
        target_const, target_sub = self._get_subs(target)

        test_body = z3.substitute(formula, existential_subs + target_sub)
        test_formula = z3.ForAll(existential_consts, z3.Exists(target_const, test_body))

        lia_solver = z3.SolverFor("LIA")
        lia_solver.add(test_formula)

        res = lia_solver.check()
        if res == z3.sat:
            return True
        if res == z3.unsat:
            return False
        assert False, "Solver returned unknown on LIA problem"


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
        rp = ReqPivot()
        print("up", rp.test(a, "up"))
        print("down", rp.test(a, "down"))


if __name__ == "__main__":
    main()
