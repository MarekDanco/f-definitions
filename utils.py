from functools import cache

import z3


@cache
def has_quantifiers(expr):
    if z3.is_quantifier(expr):
        return True
    return any(has_quantifiers(c) for c in expr.children())


def is_func(expr):
    """Check if expr is uninterpreted function symbol with arity > 0"""
    return (
        z3.is_app(expr)
        and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
        and expr.decl().arity() > 0
    )


def is_const(expr):
    """Check if expr is uninterpreted function symbol with arity 0"""
    return (
        z3.is_app(expr)
        and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
        and expr.decl().arity() == 0
    )


def is_arithmetic_op(expr):
    return z3.is_add(expr) or z3.is_sub(expr)


@cache
def is_ground(expr):
    if z3.is_var(expr):
        return False
    return all(is_ground(child) for child in expr.children())


def _offset_vars_ground(children):
    vs, ground = [], []
    for c in children:
        if is_ground(c):
            ground.append(c)
        elif z3.is_var(c):
            vs.append(c)
        else:
            return [], []
    return vs, ground


@cache
def is_offset_term(expr):
    if z3.is_var(expr):
        return True
    if is_ground(expr):
        return True
    if not is_arithmetic_op(expr):
        return False
    children = list(expr.children())
    vs, _ = _offset_vars_ground(children)
    if len(vs) == 1:
        return True
    return False
