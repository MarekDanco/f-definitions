from functools import cache

import z3


def is_func(expr):
    return z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED


def is_const(expr):
    return is_func(expr) and expr.decl().arity == 0


def is_arith_op(expr):
    return z3.is_add(expr) or z3.is_sub(expr)


@cache
def is_ground(expr):
    if z3.is_var(expr):
        return False
    return all(is_ground(child) for child in expr.children())
