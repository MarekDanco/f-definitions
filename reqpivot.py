"""Module for testing ReqPivot condition"""

import z3


class ReqPivot:
    def __init__(self, formula):
        self.formula = formula
        self.max_offset = None
        self.min_offset = None

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

    def _get_entities(self):
        pass

    def test(self):
        entities = self._get_entities()
        return False
