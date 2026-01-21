"""Module for handling conjunction of literals for ReqPivot.

This module provides classes to normalize conjunctions by aligning their
target entities to a common offset (0), enabling uniform ReqPivot
testing.
"""

import z3

from utils import get_entities, get_offset, split_entities


class Conjunct:
    """Represents a single conjunct and identifies its target entity.

    The target is the entity with the extreme offset in the given
    direction (minimum for "down", maximum for "up").
    """

    def __init__(self, conjunction, direction):
        """Extract entities from a conjunct and identify the target.

        Args:
            conjunction: A Z3 expression (single conjunct from an And)
            direction: "up" or "down" - determines target selection
        """
        entities = list(get_entities(conjunction))
        assert entities, f"No entities in conjunct: {conjunction}"
        _, self.target = split_entities(entities, direction)


class ConjunctionsManager:
    """Manages normalization of conjunctions for ReqPivot testing.

    Shifts each conjunct's de Bruijn variable so that all target
    entities align at offset 0. This normalization is essential for
    correct ReqPivot testing when the formula is a conjunction of
    multiple literals.
    """

    def __init__(self, formula, direction):
        """Initialize with a conjunction formula.

        Args:
            formula: A Z3 And expression
            direction: "up" or "down" - determines which entity is the target

        Raises:
            AssertionError: If formula is not a conjunction
        """
        assert z3.is_and(formula), f"{formula} is not conjunction"
        self.conjunctions = formula.children()
        self.conj_obj = [Conjunct(c, direction) for c in self.conjunctions]
        self.direction = direction

    def manage(self):
        """Shift conjunctions to normalize target offsets to 0.

        Each conjunct is shifted by subtracting its target's offset, so all
        targets align at offset 0. This uses Z3's substitute_vars to perform
        the arithmetic shift on de Bruijn variable 0.

        Returns:
            Z3 And expression with all conjuncts shifted to align targets at offset 0

        Note:
            BUG: Assumes de Bruijn variable index is always 0. This may fail
            for formulas with nested quantifiers where the relevant variable
            has a different index.
        """
        # Extract target entity from each conjunct (always at index 0 of target list)
        targets = [c.target[0] for c in self.conj_obj]

        # Calculate current offset of each target
        target_offsets = [get_offset(t) for t in targets]

        # Compute delta needed to shift each target to offset 0
        offset_deltas = [0 - offset for offset in target_offsets]

        # Apply shift: substitute Var(0) with Var(0) + delta in each conjunct
        # This effectively shifts f(i+k) to f(i+k+delta) = f(i) when delta = -k
        res_conjunctions = [
            z3.substitute_vars(c, z3.Var(0, z3.IntSort()) + z3.IntVal(d))
            for c, d in zip(self.conjunctions, offset_deltas)
        ]

        return z3.And(res_conjunctions)
