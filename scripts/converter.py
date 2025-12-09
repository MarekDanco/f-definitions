"""Various normal form converter classes."""

import z3


class NNFConverter:
    def __init__(self, assertion):
        self.assertion = assertion
        self._nnf_cache = {}
        self._check_cache = {}

    def _check_correct(self, expr, seen_not):
        expr_id = expr.get_id()
        if expr_id in self._check_cache:
            return self._check_cache[expr_id]
        if z3.is_quantifier(expr):
            if seen_not:
                return False
        if z3.is_not(expr):
            seen_not = True
        res = all(self._check_correct(c, seen_not) for c in expr.children())
        self._check_cache[expr_id] = res
        return res

    def convert(self):
        out = self._to_nnf(self.assertion, False)
        # assert self._check_correct(out, False), "Conversion did not go correctly."
        return out

    def _to_nnf(self, expr, negate):
        cache_key = (expr.get_id(), negate)
        if cache_key in self._nnf_cache:
            return self._nnf_cache[cache_key]
        result = None
        if z3.is_not(expr):
            result = self._to_nnf(expr.arg(0), not negate)
        elif z3.is_and(expr):
            if negate:
                result = z3.Or([self._to_nnf(child, True) for child in expr.children()])
            else:
                result = z3.And(
                    [self._to_nnf(child, False) for child in expr.children()]
                )
        elif z3.is_or(expr):
            if negate:
                result = z3.And(
                    [self._to_nnf(child, True) for child in expr.children()]
                )
            else:
                result = z3.Or(
                    [self._to_nnf(child, False) for child in expr.children()]
                )
        elif z3.is_implies(expr):
            if negate:
                result = z3.And(
                    self._to_nnf(expr.arg(0), False), self._to_nnf(expr.arg(1), True)
                )
            else:
                result = z3.Or(
                    self._to_nnf(expr.arg(0), True), self._to_nnf(expr.arg(1), False)
                )
        elif z3.is_quantifier(expr):
            num_vars = expr.num_vars()
            var_names = [expr.var_name(i) for i in range(num_vars)]
            var_sorts = [expr.var_sort(i) for i in range(num_vars)]

            bound_vars = [z3.Const(var_names[i], var_sorts[i]) for i in range(num_vars)]

            body = expr.body()
            body_with_consts = z3.substitute_vars(body, *reversed(bound_vars))

            new_body = self._to_nnf(body_with_consts, negate)
            if negate:
                if expr.is_forall():
                    result = z3.Exists(bound_vars, new_body)
                else:
                    result = z3.ForAll(bound_vars, new_body)
            else:
                if expr.is_forall():
                    result = z3.ForAll(bound_vars, new_body)
                else:
                    result = z3.Exists(bound_vars, new_body)
        elif z3.is_eq(expr) and all(z3.is_bool(child) for child in expr.children()):
            child_0 = expr.arg(0)
            child_1 = expr.arg(1)
            implies_0 = z3.Implies(child_0, child_1)
            implies_1 = z3.Implies(child_1, child_0)
            rewrite = z3.And(implies_0, implies_1)
            result = self._to_nnf(rewrite, negate)
        else:
            if negate:
                result = z3.Not(expr)
            else:
                result = expr
        self._nnf_cache[cache_key] = result
        return result
