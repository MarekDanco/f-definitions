"""Module for handling conjunction of literals for ReqPivot"""

import z3

from utils import get_entities, get_offset, split_entities


class Conjunct:
    def __init__(self, conjunction, direction):
        entities = list(get_entities(conjunction))
        _, self.target = split_entities(entities, direction)


class ConjunctionsManager:
    def __init__(self, formula, direction):
        assert z3.is_and(formula), f"{formula} is not conjunction"
        self.conjunctions = formula.children()
        self.conj_obj = [Conjunct(c, direction) for c in self.conjunctions]
        self.direction = direction

    def manage(self):
        """Returns a formula with shifted conjunctions"""
        targets = [c.target[0] for c in self.conj_obj]
        target_offsets = [get_offset(t) for t in targets]
        offset_deltas = [0 - offset for offset in target_offsets]  # normalize to 0

        res_conjunctions = [
            z3.substitute_vars(c, z3.Var(0, z3.IntSort()) + z3.IntVal(d))
            for c, d in zip(self.conjunctions, offset_deltas)
        ]
        # res_entities = set().union(*(get_entities(c) for c in res_conjunctions))
        return z3.And(res_conjunctions)
