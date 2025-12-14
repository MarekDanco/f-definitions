"""Utility functions"""

from functools import cache
from typing import Literal

import z3


def simplify(expr):
    return z3.simplify(expr, som=True)


@cache
def get_entities(expr):
    """Recursively extract entities from a Z3 expression."""
    if is_ground(expr):
        return frozenset()
    if is_func(expr):
        assert expr.decl().arity() == 1, f"Function {expr} has arity greater than 1"
        assert is_offset_term(
            expr.arg(0)
        ), f"The argument of {expr} is not an offset term"
        return frozenset({simplify(expr)})

    res = set()
    for child in expr.children():
        res |= get_entities(child)
    return frozenset(res)


def get_offset(entity, model: None | z3.ModelRef = None) -> int:
    assert is_offset_term(entity.arg(0)), f"Expression {entity} is not an entity"
    entity = simplify(entity)
    _, ground = offset_vars_ground(list(entity.arg(0).children()))

    if model is not None:
        result = model.eval(sum(ground), model_completion=True)
    else:
        if any(contains_const_func(g) for g in ground):
            assert False, "Not implemented"
        result = sum(g.as_long() for g in ground)

    if isinstance(result, int):
        return result

    assert z3.is_int_value(result), (
        "entity, ground, result, result type:",
        f"{entity}, {ground}, {result}, {type(result)}",
        "result type expected to be integer",
    )
    return result.as_long()  # type: ignore


def is_target(e, target, direction: Literal["up", "down"]):
    """Compare entity e to the current target"""
    e_offset = get_offset(e)
    target_offset = get_offset(target)
    if direction == "down":
        return e_offset < target_offset
    return e_offset > target_offset


def split_entities(entities, direction: Literal["up", "down"]):
    target = entities[0]
    for e in entities[1:]:
        if is_target(e, target, direction):
            target = e
    existential = [e for e in entities if e is not target]
    return existential, [target]


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


def contains_const_func(expr):
    if is_const(expr) or is_func(expr):
        return True
    return any(contains_const_func(c) for c in expr.children())


def is_arithmetic_op(expr):
    return z3.is_add(expr) or z3.is_sub(expr)


def is_ground(expr):
    if z3.is_var(expr):
        return False
    return all(is_ground(child) for child in expr.children())


def offset_vars_ground(children):
    vs, ground = [], []
    for c in children:
        if is_ground(c):
            ground.append(c)
        elif z3.is_var(c):
            vs.append(c)
        else:
            return [], []
    return vs, ground


def is_offset_term(expr):
    expr = simplify(expr)
    if z3.is_var(expr):
        return True
    if is_ground(expr):
        return True
    if not is_arithmetic_op(expr):
        return False
    children = list(expr.children())
    vs, _ = offset_vars_ground(children)
    if len(vs) == 1:
        return True
    return False
