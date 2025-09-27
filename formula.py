import z3


class Formula:
    def __init__(self, formula) -> None:
        self.formula = formula
        self.symbol_args = {}
        self.collect_symbs_cache = {}
        self.symbols = self.collect_symbs(formula, [])

    def _translate_var_id(self, var, scope):
        var_id = z3.get_var_index(var)
        for quant in reversed(scope):
            num_vars = quant.num_vars()
            if num_vars - 1 < var_id:
                var_id -= num_vars
            else:
                var_name = quant.var_name(num_vars - 1 - var_id)
                return z3.Const(var_name, var.sort())

    def _find_vars(self, expr):
        if z3.is_var(expr):
            return {expr}
        vs = set()
        for arg in expr.children():
            vs |= self._find_vars(arg)
        return vs

    def _add_arg(self, symbol, scope, arg_vector):
        if not symbol in self.symbol_args:
            self.symbol_args[symbol] = {}
            self.symbol_args[symbol][scope] = {arg_vector}
            return
        if not scope in self.symbol_args[symbol]:
            self.symbol_args[symbol][scope] = {arg_vector}
            return
        self.symbol_args[symbol][scope].add(arg_vector)

    def _collect_symbs_args(self, expr, scope):
        arg_vector = []
        for arg in expr.children():
            vs = self._find_vars(arg)
            var_subs = [(v, self._translate_var_id(v, scope)) for v in vs]
            new_arg = z3.substitute(arg, var_subs)
            arg_vector.append(z3.simplify(new_arg))
        self._add_arg(expr.decl(), tuple(scope), tuple(arg_vector))

    def collect_symbs(self, expr, scope):
        """Extract all variables/constants from a Z3 formula"""
        expr_id = expr.get_id()
        if z3.is_quantifier(expr):
            scope.append(expr)
        if expr_id in self.collect_symbs_cache:
            return self.collect_symbs_cache[expr_id]
        symbs = set()
        if z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            symbs.add(expr.decl())
            if scope and expr.decl().arity() > 0:
                self._collect_symbs_args(expr, scope)
        for child in expr.children():
            symbs |= self.collect_symbs(child, scope)
        self.collect_symbs_cache[expr_id] = symbs
        return symbs

    def is_single_invocation(self, symbol, scope=None) -> bool:
        """Check if symbol is single invocation within the scope of a quantifier."""
        assert symbol in self.symbol_args, f"Symbol {symbol!r} not found in symbol_args"
        if scope is not None:
            return len(self.symbol_args[symbol][scope]) == 1
        for _, args in self.symbol_args[symbol].items():
            if len(args) > 1:
                return False
        return True

    def deskolemize(self, scope, symbol):
        """Deskolemize a single invocation function symbol."""
        assert self.is_single_invocation(
            symbol, scope
        ), f"{symbol!r} is not single invocation within the scope of {scope!r}"
        assert z3.is_quantifier(scope)
        # TODO check the universally quantified variables used in arguments
        # TODO place an existential variable after the last such universal variable
        # TODO substitute
