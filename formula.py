"""
Module for handling formulas. Assumes quantified formulas are all universal in prenex
form i.e. no quantifiers are nested.
"""

import z3


class Ground:
    def __init__(self, formula) -> None:
        self.formula = formula


class Quantified:
    def __init__(self, formula) -> None:
        self.formula = formula
        self.conjuncts = list(
            map(lambda x: Conjunct(self.formula, x), self._get_conjuncts())
        )

    def _get_conjuncts(self):
        matrix = self.formula.body()
        if z3.is_and(matrix):
            return list(matrix.children())
        return [matrix]


class Conjunct:
    def __init__(self, formula, conjunct):
        self.formula = formula
        self.conjunct = conjunct
        self.cells = set()
        self.max_offset = None
        self.min_offset = None
        self.collect_symbs_cache = set()
        self._collect_symbs(self.conjunct)

    def _set_max_min(self, offset):
        if self.max_offset is None:
            self.max_offset = offset
        if self.min_offset is None:
            self.min_offset = offset
        elif offset > self.max_offset:
            self.max_offset = offset
        elif offset < self.min_offset:
            self.min_offset = offset

    def _is_offset_term(self, expr):
        if z3.is_var(expr):
            self._set_max_min(0)
            return True
        if not (z3.is_add(expr) or z3.is_sub(expr)):
            return False
        children = expr.children()
        if not len(children) == 2:
            return False
        child_1, child_2 = children
        if z3.is_var(child_1) and z3.is_int_value(child_2):
            self._set_max_min(child_2.as_long())
            return True
        if z3.is_var(child_2) and z3.is_int_value(child_1):
            self._set_max_min(child_1.as_long())
            return True
        return False

    def _collect_symbs_args(self, expr):
        for arg in expr.children():
            assert self._is_offset_term(arg), f"Argument {arg} is not an offset term"
        self.cells.add(expr)

    def _collect_symbs(self, expr):
        """Extract all variables/constants from a Z3 formula"""
        expr_id = expr.get_id()
        if expr_id in self.collect_symbs_cache:
            return
        if z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            if expr.decl().arity() > 0:
                self._collect_symbs_args(expr)
        self.collect_symbs_cache.add(expr_id)
        for child in expr.children():
            self._collect_symbs(child)

    def _compute_delta(self, guide, offset):
        delta = abs(offset - guide)
        if offset >= guide:
            delta *= -1
        return delta

    def normalize(self, guide, direction):
        assert direction in {"up", "down"}
        if direction == "up":
            assert self.max_offset is not None, "self.max_offset is not set"
            delta = self._compute_delta(guide, self.max_offset)
        else:
            assert self.min_offset is not None, "self.min_offset is not set"
            delta = self._compute_delta(guide, self.min_offset)
        num_vars = self.formula.num_vars()
        var_subs = [
            (z3.Var(i, z3.IntSort()), z3.Var(i, z3.IntSort()) + delta)
            for i in range(num_vars)
        ]
        return z3.simplify(z3.substitute(self.conjunct, var_subs))
