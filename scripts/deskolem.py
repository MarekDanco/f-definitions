"""Module with old deskolemization methods"""

import z3


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


def is_single_invocation(self, symbol, scope=None) -> bool:
    """Check if symbol is single invocation within the scope of a quantifier."""
    assert symbol in self.symbol_args, f"Symbol {symbol!r} not found in symbol_args"
    if scope is not None:
        return len(self.symbol_args[symbol][scope]) == 1
    return all(len(args) == 1 for _, args in self.symbol_args[symbol].items())


def get_deskolem_var(self, symbol, scope):
    args = list(self.symbol_args[symbol][scope])[0]
    var_name = f"deskolem_{symbol.name()}_{hash(args) % 10000}"
    return z3.Const(var_name, symbol.range())


def deskolemize(self, symbol, scope):
    """Deskolemize a single invocation symbol within the given scope."""
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
        z3.Const(scope.var_name(i), scope.var_sort(i)) for i in range(scope.num_vars())
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
