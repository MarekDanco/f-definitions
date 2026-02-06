from collections import defaultdict
import z3


def flatten(ls):
    return [item for subls in ls for item in subls]


class Formula:
    def __init__(self, b):
        self.b = b
        self.argF = defaultdict(set)
        self.recurse(self.b.F)

    def get_func_interp(self, f, model, bmax, consts):
        args = (
            set(z3.IntVal(i) for i in range(bmax + 1))
            | set(c() for c in consts)
            | self.argF[f]
        )
        return {arg: model.eval(f(arg)) for arg in args}

    def print_func_interp(self, f, model, bmax, consts):
        interp = self.get_func_interp(f, model, bmax, consts)
        for arg, val in interp.items():
            print(f"    {arg} -> {val}")

    def add_argF(self, f, arg):
        self.argF[f].add(arg)

    def get_argF(self):
        return self.argF

    def recurse(self, expr):
        if z3.is_app(expr) and expr.num_args() == 1:
            self.add_argF(expr.decl(), expr.arg(0))
            return
        for c in expr.children():
            self.recurse(c)
