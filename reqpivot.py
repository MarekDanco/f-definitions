#!/usr/bin/env -S python3 -u
"""Module for testing ReqPivot condition"""

import argparse
from typing import Literal

import z3

from conjunct import ConjunctionsManager
from utils import has_quantifiers, res_matrix_entities, split_entities


class ReqPivot:
    """Tests whether a quantified formula satisfies the ReqPivot condition.

    ReqPivot checks if, for a given direction (up/down), there exists an assignment
    to the "target" entity such that all "existential" entities can be satisfied.
    The target is the entity with the min (down) or max (up) offset.
    """

    def __init__(self):
        self.model: None | z3.ModelRef = None  # ground model (unused currently)

    def _get_subs(self, entities):
        """Create fresh constants and substitution pairs for de Bruijn indexed entities.

        Args:
            entities: List of Z3 expressions (function applications with offset terms)

        Returns:
            Tuple of (fresh_constants, substitution_pairs) where substitution_pairs
            can be passed to z3.substitute to replace entities with fresh constants.
        """
        constants = [z3.FreshConst(e.sort()) for e in entities]
        return constants, [(e, c) for e, c in zip(entities, constants)]

    def _process(self, assertion, direction: Literal["up", "down"]):
        """Extract and normalize the matrix of a quantified assertion.

        For conjunctions, shifts all conjuncts so their target entities align at offset 0.
        This normalization enables uniform handling of the ReqPivot test.

        Args:
            assertion: A Z3 quantified formula
            direction: "up" (max offset is target) or "down" (min offset is target)

        Returns:
            Tuple of (simplified_matrix, list_of_entities)
        """
        assert z3.is_quantifier(assertion), f"{assertion} is not quantified"
        matrix = assertion.body()
        if not z3.is_and(matrix):
            # Single literal or non-conjunction: no shifting needed
            return res_matrix_entities(matrix)
        # For conjunctions, normalize offsets via ConjunctionsManager
        conj_manager = ConjunctionsManager(matrix, direction)
        return res_matrix_entities(conj_manager.manage())

    def test(self, assertion, direction: Literal["up", "down"]):
        """Test if the assertion satisfies ReqPivot in the given direction.

        Constructs the formula: ForAll(existential_vars, Exists(target_var, body))
        and checks satisfiability. If SAT, ReqPivot holds.

        Args:
            assertion: A Z3 quantified formula to test
            direction: "up" or "down" - determines which entity becomes the target

        Returns:
            True if ReqPivot holds, False otherwise

        Raises:
            AssertionError: If no entities found or solver returns unknown
        """
        formula, entities = self._process(assertion, direction)
        assert entities, "Found no entities"
        # Split: target is the entity with extreme offset (min for down, max for up)
        existential, target = split_entities(entities, direction)

        # Create fresh constants to replace de Bruijn indexed variables
        existential_consts, existential_subs = self._get_subs(existential)
        target_const, target_sub = self._get_subs(target)

        # Build test formula: ∀ existential. ∃ target. body
        test_body = z3.substitute(formula, existential_subs + target_sub)
        test_formula = z3.ForAll(existential_consts, z3.Exists(target_const, test_body))

        # Use LIA solver for decidability on linear integer arithmetic
        lia_solver = z3.SolverFor("LIA")
        lia_solver.add(test_formula)

        res = lia_solver.check()
        if res == z3.sat:
            return True
        if res == z3.unsat:
            return False
        assert False, "Solver returned unknown on LIA problem"


def main():
    """Entry point: test ReqPivot on all quantified assertions in an SMT file."""
    parser = argparse.ArgumentParser(
        description="Test whether assertions in an SMT file satisfy ReqPivot"
    )
    parser.add_argument("input_file", help="Input SMT file to test")
    args = parser.parse_args()

    # Load SMT file using Z3 solver's parser
    s = z3.Solver()
    s.from_file(args.input_file)
    print(f"input: {args.input_file}")

    # Filter to only quantified assertions (skip ground assertions)
    assertions = [a for a in s.assertions() if has_quantifiers(a)]  # type: ignore

    # Test each assertion in both directions
    for a in assertions:
        print(a)
        rp = ReqPivot()
        print("up", rp.test(a, "up"))
        print("down", rp.test(a, "down"))


if __name__ == "__main__":
    main()
