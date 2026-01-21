"""Utility functions for Z3 expression manipulation and entity extraction.

This module provides utilities for working with Z3 expressions in the context
of ReqPivot testing, including entity extraction, offset computation, and
expression classification.

Key concepts:
- Entity: A function application f(offset_term) where offset_term is of the form
  Var(i) + constant, representing indexed array-like accesses.
- Offset: The constant part of an entity's argument (the "k" in f(i+k)).
- Ground: An expression containing no de Bruijn variables.
"""

from functools import cache
from typing import Literal

import z3


def simplify(expr):
    """Simplify a Z3 expression using sum-of-monomials form.

    Args:
        expr: Z3 expression to simplify

    Returns:
        Simplified Z3 expression with arithmetic normalized to som form
    """
    return z3.simplify(expr, som=True)


def res_matrix_entities(matrix):
    """Extract simplified matrix and its entities.

    Args:
        matrix: The body (matrix) of a quantified formula

    Returns:
        Tuple of (simplified_matrix, list_of_entities)
    """
    return simplify(matrix), list(get_entities(matrix))


@cache
def get_entities(expr):
    """Recursively extract entities from a Z3 expression.

    An entity is a unary function application f(offset_term) where the argument
    is a linear expression in a single de Bruijn variable (e.g., Var(0) + 3).

    Args:
        expr: Z3 expression to extract entities from

    Returns:
        Frozenset of simplified entity expressions found in expr

    Raises:
        AssertionError: If a function has arity > 1 or non-offset argument
    """
    if is_ground(expr):
        return frozenset()
    if is_func(expr):
        # Entity found: validate it matches expected form f(var + const)
        assert expr.decl().arity() == 1, f"Function {expr} has arity greater than 1"
        assert is_offset_term(expr.arg(0)), (
            f"The argument of {expr} is not an offset term"
        )
        return frozenset({simplify(expr)})

    # Recursively collect entities from subexpressions
    res = set()
    for child in expr.children():
        res |= get_entities(child)
    return frozenset(res)


def get_offset(entity, model: None | z3.ModelRef = None) -> int:
    """Extract the integer offset from an entity's argument.

    For an entity f(Var(0) + k), returns k. Can optionally use a model
    to evaluate symbolic constants.

    Args:
        entity: A Z3 function application f(offset_term)
        model: Optional Z3 model for evaluating symbolic constants

    Returns:
        Integer offset value

    Raises:
        AssertionError: If entity is malformed or offset cannot be determined
    """
    assert is_offset_term(entity.arg(0)), f"Expression {entity} is not an entity"
    entity = simplify(entity)
    # Separate the argument into variable and ground (constant) parts
    _, ground = offset_vars_ground(list(entity.arg(0).children()))

    if model is not None:
        # Use model to evaluate any symbolic constants in offset
        result = model.eval(sum(ground), model_completion=True)
    else:
        # No model: ground terms must be concrete integers
        if any(contains_const_func(g) for g in ground):
            assert False, f"Cannot determine value of offset {sum(ground)}"
        # Note: sum([]) returns 0, which handles the case of no ground terms
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
    """Check if entity e should replace current target based on direction.

    Args:
        e: Candidate entity to compare
        target: Current target entity
        direction: "down" means smaller offset wins, "up" means larger offset wins

    Returns:
        True if e has a more extreme offset than target in the given direction
    """
    e_offset = get_offset(e)
    target_offset = get_offset(target)
    if direction == "down":
        return e_offset < target_offset
    return e_offset > target_offset


def split_entities(entities, direction: Literal["up", "down"]):
    """Split entities into existential variables and target.

    Finds the entity with the extreme offset (min for "down", max for "up")
    and designates it as the target. All other entities become existential.

    Args:
        entities: List of entity expressions (must be non-empty)
        direction: "down" (min offset is target) or "up" (max offset is target)

    Returns:
        Tuple of (existential_list, [target]) where target is in a singleton list

    Note:
        Uses identity comparison (is not) which relies on Z3's expression caching.
        This works because entities come from get_entities() which returns
        simplified, cached expressions.
    """
    # Start with first entity as initial target candidate
    target = entities[0]
    for e in entities[1:]:
        if is_target(e, target, direction):
            target = e
    # TODO: changing to not eq, from is not
    existential = [e for e in entities if not e.eq(target)]
    return existential, [target]


@cache
def has_quantifiers(expr):
    """Check if a Z3 expression contains any quantifiers.

    Args:
        expr: Z3 expression to check

    Returns:
        True if expr or any subexpression is a quantifier
    """
    if z3.is_quantifier(expr):
        return True
    return any(has_quantifiers(c) for c in expr.children())


def is_func(expr):
    """Check if expr is an uninterpreted function application (arity > 0).

    Uninterpreted functions with arity > 0 represent array-like accesses
    in this context (e.g., f(i) represents an array element).

    Args:
        expr: Z3 expression to check

    Returns:
        True if expr is an uninterpreted function call with at least one argument
    """
    return (
        z3.is_app(expr)
        and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
        and expr.decl().arity() > 0
    )


# TODO: different from z3 is_const?
def is_const(expr):
    """Check if expr is an uninterpreted constant (function with arity 0).

    Args:
        expr: Z3 expression to check

    Returns:
        True if expr is an uninterpreted constant (nullary function)
    """
    return (
        z3.is_app(expr)
        and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
        and expr.decl().arity() == 0
    )


def contains_const_func(expr):
    """Check if expr contains any uninterpreted symbols (constants or
    functions).

    Args:
        expr: Z3 expression to check

    Returns:
        True if expr contains any uninterpreted symbol
    """
    if is_const(expr) or is_func(expr):
        return True
    return any(contains_const_func(c) for c in expr.children())


def is_arithmetic_op(expr):
    """Check if expr is an addition or subtraction operation.

    Args:
        expr: Z3 expression to check

    Returns:
        True if expr is Add or Sub
    """
    return z3.is_add(expr) or z3.is_sub(expr)


def is_ground(expr):
    """Check if expr contains no de Bruijn variables.

    A ground expression can be evaluated without binding any quantified variables.

    Args:
        expr: Z3 expression to check

    Returns:
        True if expr contains no Var references
    """
    if z3.is_var(expr):
        return False
    return all(is_ground(child) for child in expr.children())


def offset_vars_ground(children):
    """Partition children into de Bruijn variables and ground terms.

    Used to decompose an offset term like (Var(0) + 3 + k) into its
    variable part [Var(0)] and ground part [3, k].

    Args:
        children: List of Z3 expressions (children of an arithmetic op)

    Returns:
        Tuple of (vars_list, ground_list). Returns ([], []) if any child
        is neither a variable nor ground (e.g., nested arithmetic).
    """
    vs, ground = [], []
    for c in children:
        if is_ground(c):
            ground.append(c)
        elif z3.is_var(c):
            vs.append(c)
        else:
            # Child is neither ground nor a simple variable - unsupported form
            return [], []
    return vs, ground


def is_offset_term(expr):
    """Check if expr is a valid offset term for an entity argument.

    Valid offset terms are:
    - A single de Bruijn variable: Var(i)
    - A ground expression: 3, k, k+1
    - Arithmetic with exactly one variable: Var(0) + 3, Var(0) + k

    Args:
        expr: Z3 expression to check

    Returns:
        True if expr is a valid offset term
    """
    expr = simplify(expr)
    if z3.is_var(expr):
        return True
    if is_ground(expr):
        return True
    if not is_arithmetic_op(expr):
        return False
    # For arithmetic ops, require exactly one de Bruijn variable
    children = list(expr.children())
    vs, _ = offset_vars_ground(children)
    if len(vs) == 1:
        return True
    return False
