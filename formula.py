import z3


class Formula:
    def __init__(self, formula) -> None:
        self.formula = self._to_nnf(formula)
        self.symbol_args = {}
        self.symbol_expr = {}
        self.collect_symbs_cache = {}
        self.symbols = self.collect_symbs(self.formula, [])

    def _to_nnf(self, formula):
        nnf_tactic = z3.Tactic("nnf")
        nnf_goal = nnf_tactic(formula)
        return nnf_goal.as_expr()

    def _translate_var_id(self, var, scope):
        var_id = z3.get_var_index(var)
        for quant in reversed(scope):
            num_vars = quant.num_vars()
            if num_vars - 1 < var_id:
                var_id -= num_vars
            else:
                var_name = quant.var_name(num_vars - 1 - var_id)
                break
        return z3.Const(var_name, var.sort())

    def _find_vars(self, expr):
        if z3.is_var(expr):
            return {expr}
        vs = set()
        for arg in expr.children():
            vs |= self._find_vars(arg)
        return vs

    def _add_arg(self, symbol, scope, arg_vector, expr):
        if not symbol in self.symbol_args:
            self.symbol_args[symbol] = {}
            self.symbol_args[symbol][scope] = {arg_vector}
            self.symbol_expr[symbol] = {}
            self.symbol_expr[symbol][scope] = {expr}
            return
        if not scope in self.symbol_args[symbol]:
            self.symbol_args[symbol][scope] = {arg_vector}
            self.symbol_expr[symbol][scope] = {expr}
            return
        self.symbol_args[symbol][scope].add(arg_vector)
        self.symbol_expr[symbol][scope].add(expr)

    def _collect_symbs_args(self, expr, scope):
        arg_vector = []
        new_expr = expr
        for arg in expr.children():
            vs = self._find_vars(arg)
            var_subs = [(v, self._translate_var_id(v, scope)) for v in vs]
            new_arg = z3.substitute(arg, var_subs)
            new_expr = z3.substitute(new_expr, var_subs)
            arg_vector.append(new_arg)
        self._add_arg(expr.decl(), scope[-1], tuple(arg_vector), expr)

    def get_id(self, expr, scope):
        """Include scope in the id to patch de Bruijn collisions."""
        expr_id = expr.get_id()
        return (expr_id, tuple(scope))

    def collect_symbs(self, expr, scope):
        """Extract all variables/constants from a Z3 formula"""
        expr_id = self.get_id(expr, scope)
        if z3.is_quantifier(expr):
            new_scope = scope + [expr]
        else:
            new_scope = scope
        if expr_id in self.collect_symbs_cache:
            return self.collect_symbs_cache[expr_id]
        symbs = set()
        if z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            symbs.add(expr.decl())
            if scope and expr.decl().arity() > 0:
                self._collect_symbs_args(expr, new_scope)
        for child in expr.children():
            symbs |= self.collect_symbs(child, new_scope)
        self.collect_symbs_cache[expr_id] = symbs
        return symbs

    def is_single_invocation(self, symbol, scope=None) -> bool:
        """Check if symbol is single invocation within the scope of a quantifier."""
        assert symbol in self.symbol_args, f"Symbol {symbol!r} not found in symbol_args"
        if scope is not None:
            return len(self.symbol_args[symbol][scope]) == 1
        return all(len(args) == 1 for _, args in self.symbol_args[symbol].items())

    def get_var_chain(self, formula, scope, chain):
        """Return chain of (name, sort) tuples for quantified variables until scope is reached."""
        vs = []
        if z3.is_quantifier(formula):
            vs = [
                (formula.var_name(i), formula.var_sort(i))
                for i in range(formula.num_vars())
            ]
        if formula.get_id() == scope.get_id():
            return chain + vs
        for c in formula.children():
            result = self.get_var_chain(c, scope, chain + vs)
            if result is not None:
                return result
        return None

    def get_deskolem_var(self, symbol, scope):
        args = list(self.symbol_args[symbol][scope])[0]
        var_name = f"deskolem_{symbol.name()}_{hash(args) % 10000}"
        return z3.Const(var_name, symbol.range())

    def deskolemize(self, symbol, scope):
        expr = list(self.symbol_expr[symbol][scope])[0]
        deskolem_var = self.get_deskolem_var(symbol, scope)
        sub = [(expr, deskolem_var)]
        f_deskolem = z3.substitute(scope.body(), sub)
        var_chain = self.get_var_chain(self.formula, scope, [])
        assert var_chain is not None, f"Could not find {scope} in {self.formula}"
        shift_sub = []
        for i, (_, var_sort) in enumerate(var_chain):
            shift_sub.append((z3.Var(i, var_sort), z3.Var(i + 1, var_sort)))
        f_deskolem_shifted = z3.substitute(f_deskolem, shift_sub)
        exist_f_deskolem = z3.Exists([deskolem_var], f_deskolem_shifted)
        vs = [
            z3.Const(scope.var_name(i), scope.var_sort(i))
            for i in range(scope.num_vars())
        ]
        new_scope = z3.ForAll(vs, exist_f_deskolem)
        return new_scope

    def test_deskolemize(self, formula):
        for scope in formula.children():
            self.test_deskolemize(scope)
        if z3.is_quantifier(formula):
            print(f"scope {formula}")
            for symbol in self.symbols:
                res = self.is_single_invocation(symbol, formula)
                print(f"{symbol} is single invocation? {res}")
                if res:
                    print(f"new scope {self.deskolemize(symbol, formula)}")
            print()
