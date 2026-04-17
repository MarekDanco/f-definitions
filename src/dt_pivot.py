#!/usr/bin/env python3
"""Pivot solver for quantified datatype problems.

Checks satisfiability of quantified formulas over algebraic datatypes by
identifying pivot terms and transforming the problem into a quantifier-
over-integers problem.
"""

import sys

from z3 import (
    Z3_OP_UNINTERPRETED,
    Const,
    DatatypeSortRef,
    Exists,
    ForAll,
    Int,
    IntSort,
    Solver,
    is_app,
    is_quantifier,
    parse_smt2_file,
    sat,
    substitute,
    substitute_vars,
)


def bail(msg):
    print(f"BAIL-OUT: {msg}", file=sys.stderr)
    sys.exit(1)


def parse_and_validate(filename):
    """Parse SMT2 file, separate ground/quantified assertions, validate
    constraints.

    Returns (ground_asserts, qbody, f_decl, datatype_sort, qvar).
    """
    assertions = parse_smt2_file(filename)

    ground = []
    quantified = []
    for a in assertions:
        if is_quantifier(a) and a.is_forall():
            quantified.append(a)
        else:
            ground.append(a)

    if len(quantified) != 1:
        bail(f"expected exactly 1 forall quantifier, got {len(quantified)}")

    quant = quantified[0]
    if quant.num_vars() != 1:
        bail(f"expected exactly 1 quantified variable, got {quant.num_vars()}")

    var_sort = quant.var_sort(0)
    if not isinstance(var_sort, DatatypeSortRef):
        bail(f"quantified variable sort {var_sort} is not a datatype")

    var_name = quant.var_name(0)
    qvar = Const(var_name, var_sort)
    qbody = substitute_vars(quant.body(), qvar)

    # Find the unique uninterpreted function f: T -> Int
    f_decl = _find_f_decl(assertions, var_sort)

    return ground, qbody, f_decl, var_sort, qvar


def _find_f_decl(assertions, datatype_sort):
    """Find a unique uninterpreted function f: datatype_sort -> Int."""
    candidates = set()
    for a in assertions:
        _scan_for_f(a, datatype_sort, candidates)

    if len(candidates) == 0:
        bail("no function f: T -> Int found")
    if len(candidates) > 1:
        names = [d.name() for d in candidates]
        bail(f"multiple f: T -> Int candidates found: {names}")

    return candidates.pop()


def _scan_for_f(expr, datatype_sort, candidates):
    """Recursively scan expression for uninterpreted functions T -> Int."""
    if is_quantifier(expr):
        _scan_for_f(expr.body(), datatype_sort, candidates)
        return
    if not is_app(expr):
        return
    d = expr.decl()
    if (
        d.arity() == 1
        and d.domain(0) == datatype_sort
        and d.range() == IntSort()
        and d.kind() == Z3_OP_UNINTERPRETED
    ):
        candidates.add(d)
    for i in range(expr.num_args()):
        _scan_for_f(expr.arg(i), datatype_sort, candidates)


def collect_f_apps(expr, f_decl):
    """Collect all unique f-applications in expr, deduped by sexpr()."""
    seen = set()
    result = []
    stack = [expr]
    while stack:
        e = stack.pop()
        if is_quantifier(e):
            stack.append(e.body())
            continue
        if not is_app(e):
            continue
        if e.decl().name() == f_decl.name() and e.decl().arity() == f_decl.arity():
            key = e.sexpr()
            if key not in seen:
                seen.add(key)
                result.append(e)
        for i in range(e.num_args()):
            stack.append(e.arg(i))
    return result


def find_pivot_smt(f_apps, datatype_sort, qvar):
    """Identify which f-applications are pivots using SMT checks.

    For each pair (i,j) and each constructor C of the datatype:
    create fresh variables for non-recursive slots, check if t_i == C(..., t_j, ...).
    If SAT, f(t_i) is a pivot.

    Returns set of indices into f_apps that are pivots.
    """
    pivot_idxs = set()

    # Collect constructors with arity > 0 (skip nullary constructors like nil)
    constructors = []
    for ci in range(datatype_sort.num_constructors()):
        c = datatype_sort.constructor(ci)
        if c.arity() == 0:
            continue
        if c.arity() > 2:
            bail(f"constructor {c.name()} has arity {c.arity()} > 2")
        # Find which argument position is recursive (has datatype_sort)
        rec_positions = []
        for ai in range(c.arity()):
            acc = datatype_sort.accessor(ci, ai)
            if acc.range() == datatype_sort:
                rec_positions.append(ai)
        constructors.append((c, ci, rec_positions))

    for i in range(len(f_apps)):
        t_i = f_apps[i].arg(0)
        for j in range(len(f_apps)):
            if i == j:
                continue
            t_j = f_apps[j].arg(0)
            for c, ci, rec_positions in constructors:
                for rec_pos in rec_positions:
                    # Build C(..., t_j, ...) with fresh vars for non-recursive slots
                    args = []
                    for ai in range(c.arity()):
                        if ai == rec_pos:
                            args.append(t_j)
                        else:
                            acc = datatype_sort.accessor(ci, ai)
                            fresh = Const(f"__pivot_Y_{ci}_{ai}", acc.range())
                            args.append(fresh)
                    constructed = c(*args)

                    s = Solver()
                    s.add(t_i == constructed)
                    if s.check() == sat:
                        pivot_idxs.add(i)

    return pivot_idxs


def transform(qbody, f_apps, pivot_idxs, non_pivot_idxs, ground):
    """Replace f-applications with fresh Int variables.

    Non-pivots -> universal variables, pivots -> existential variables.
    Returns the full formula (ground + transformed quantified part).
    """
    if not f_apps:
        bail("no f-applications found in quantified body")

    subs = []
    univ_vars = []
    exist_vars = []

    for idx, fapp in enumerate(f_apps):
        if idx in pivot_idxs:
            v = Int(f"_pivot_{idx}")
            exist_vars.append(v)
        else:
            v = Int(f"_base_{idx}")
            univ_vars.append(v)
        subs.append((fapp, v))

    new_body = substitute(qbody, subs)

    # Build quantified formula
    if univ_vars and exist_vars:
        qformula = ForAll(univ_vars, Exists(exist_vars, new_body))
    elif univ_vars:
        qformula = ForAll(univ_vars, new_body)
    elif exist_vars:
        Exists(exist_vars, new_body)
        qformula = Exists(exist_vars, new_body)
    else:
        qformula = new_body

    return list(ground) + [qformula]


def solve(filename):
    """Orchestrate: parse -> collect -> find pivots -> transform -> check sat."""
    ground, qbody, f_decl, datatype_sort, qvar = parse_and_validate(filename)

    f_apps = collect_f_apps(qbody, f_decl)
    if not f_apps:
        bail("no f-applications found in quantified body")

    print(f"Function: {f_decl.name()} : {datatype_sort} -> Int")
    print(f"Quantified body: {qbody}")
    print(f"f-applications ({len(f_apps)}):")
    for i, fa in enumerate(f_apps):
        print(f"  [{i}] {fa}")

    pivot_idxs = find_pivot_smt(f_apps, datatype_sort, qvar)
    non_pivot_idxs = set(range(len(f_apps))) - pivot_idxs

    if not pivot_idxs:
        bail("no pivot found")

    print(f"Pivots: {sorted(pivot_idxs)}")
    print(f"Non-pivots: {sorted(non_pivot_idxs)}")

    formula_parts = transform(qbody, f_apps, pivot_idxs, non_pivot_idxs, ground)

    print("Transformed formula:")
    for p in formula_parts:
        print(f"  {p}")

    s = Solver()
    s.add(formula_parts)
    result = s.check()
    print(result)
    return result


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <smt2-file>", file=sys.stderr)
        sys.exit(1)
    solve(sys.argv[1])
