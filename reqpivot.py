#!/usr/bin/env -S python3 -u
"""Module for testing ReqPivot condition"""

import argparse
from functools import cache
from typing import Literal

import z3

from utils import (
    contains_const_func,
    has_quantifiers,
    is_func,
    is_ground,
    is_offset_term,
    offset_vars_ground,
)


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
        self.model: None | z3.ModelRef = None

    def _normalize(self, direction: Literal["up", "down"]):
        # TODO deal with conjunction and disjunction
        if z3.is_and(self.formula.body()) or z3.is_or(self.formula.body()):
            print("WARNING: testing without normalizing")
        return self.entities

    def _get_offset(self, entity) -> int:
        assert is_offset_term(entity.arg(0)), f"Expression {entity} is not an entity"
        entity = z3.simplify(entity, som=True)
        _, ground = offset_vars_ground(list(entity.arg(0).children()))

        if self.model is not None:
            result = self.model.eval(sum(ground), model_completion=True)
        else:
            for g in ground:
                if contains_const_func(g):
                    assert False, "Not implemented"
            result = sum(g.as_long() for g in ground)

        if isinstance(result, int):
            return result

        assert z3.is_int_value(result), f"{entity}, {ground}, {result}, {type(result)}"
        return result.as_long()  # type: ignore

    def _is_target(self, e, target, direction: Literal["up", "down"]):
        """Compare entity e to the current target"""
        e_offset = self._get_offset(e)
        target_offset = self._get_offset(target)
        if direction == "down":
            return e_offset < target_offset
        return e_offset > target_offset

    def _split_entities(self, entities, direction: Literal["up", "down"]):
        target = entities[0]
        for e in entities[1:]:
            if self._is_target(e, target, direction):
                target = e
        existential = [e for e in entities if e is not target]
        return existential, [target]

    def _get_subs(self, entities):
        constants = [z3.FreshConst(e.sort()) for e in entities]
        return constants, [(e, c) for e, c in zip(entities, constants)]

    def test(self, direction: Literal["up", "down"]):
        self.entities = list(_get_entities_recursive(self.formula))
        assert self.entities, "Found no entities"
        norm_entities = self._normalize(direction)
        existential, target = self._split_entities(norm_entities, direction)

        existential_consts, existential_subs = self._get_subs(existential)
        target_const, target_sub = self._get_subs(target)

        test_body = z3.substitute(self.formula.body(), existential_subs + target_sub)
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
        rp = ReqPivot(a)
        print("up", rp.test("up"))
        print("down", rp.test("down"))


if __name__ == "__main__":
    main()
