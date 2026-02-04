#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# current restrictions:
# maximally two occurrences of function symbol in quantified part
# positive indices only


import argparse

# import functools
# import operator
import itertools

from z3 import *

from benchmarks import Incr, IncrConst, IncrConstArg, Incr2Functions, Test
from smt2_loader import load_smt2
from sygus import process_formula


def get_func_interp(f, model, bmax, consts):
    args = set(range(bmax + 1)) | set(model.eval(c()).as_long() for c in consts)
    return {arg: model.eval(f(arg)) for arg in args}


def print_func_interp(interp):
    for arg, val in interp.items():
        print(f"    {arg} -> {val}")


def flatten(ls):  # flatten a list of lists
    # return functools.reduce(operator.concat, l)
    return [item for subls in ls for item in subls]


def maximality_i(i, b):
    if len(b.offsets[i]) == 2:
        return [
            Or(
                Not(p[i][0]), Not(p[i][1]), b.offsets[i][0] == b.offsets[i][1]
            ),  # equality
            Or(Not(p[i][0]), p[i][1], b.offsets[i][0] > b.offsets[i][1]),  # rest
            Or(Not(p[i][1]), p[i][0], b.offsets[i][1] > b.offsets[i][0]),
        ]
    elif len(b.offsets[i]) == 1:
        return []  # if there just one occurrence the maximality condition is vacuously true
    else:
        raise Exception(f"larger offset not yet implemented {b.offsets[i]}")


def maximality(b):
    return flatten([maximality_i(i, b) for i in range(0, num_f)])


def get_bitvectors(k):
    # repeat=k ensures we get vectors of length k
    return list(itertools.product([False, True], repeat=k))


def reqpivot_case(bl, b):
    pl = flatten(p)
    occl = flatten(b.occ)
    assert len(bl) == len(pl) and len(pl) == len(occl)
    univ_vars = [b.x] + [occl[i] for i in range(len(bl)) if not bl[i]]
    exist_vars = [occl[i] for i in range(len(bl)) if bl[i]]
    boolguard = [Not(pl[i]) if bl[i] else pl[i] for i in range(len(bl))]
    if exist_vars == []:
        return Or(boolguard + [ForAll(univ_vars, b.Qp)])
    else:
        return Or(boolguard + [ForAll(univ_vars, Exists(exist_vars, b.Qp))])


def reqpivot(b):
    return list(map(lambda t: reqpivot_case(t, b), get_bitvectors(len(flatten(p)))))
    # res = list(map(lambda t: reqpivot_case(t, b), get_bitvectors(len(flatten(p)))))
    # for r in res:
    #     print(r)
    # return res


def reqpivot_2(b):  # old implementation of special case
    assert len(p) == 1 and len(p[0]) == 2
    return [
        (
            Or(
                p[0][0],
                p[0][1],
                ForAll(b.x, ForAll(b.occ[0][0], ForAll(b.occ[0][1], b.Qp))),
            )
        ),
        (
            Or(
                p[0][0],
                Not(p[0][1]),
                ForAll(b.x, ForAll(b.occ[0][0], Exists(b.occ[0][1], b.Qp))),
            )
        ),
        (
            Or(
                Not(p[0][0]),
                p[0][1],
                ForAll(b.x, ForAll(b.occ[0][1], Exists(b.occ[0][0], b.Qp))),
            )
        ),
        (
            Or(
                Not(p[0][0]),
                Not(p[0][1]),
                Exists(b.x, Exists(b.occ[0][1], ForAll(b.occ[0][0], b.Qp))),
            )
        ),
    ]


def clash(b):
    return [
        Or(Not(p[i][j]), b.argF[0][arg] <= bmax + b.offsets[i][j])
        for i in range(0, num_f)
        for arg in range(0, len(b.argF[i]))
        for j in range(0, len(b.offsets[i]))
    ]


def clash_2(i, b):  # old implementation of special case
    assert len(b.offsets[i]) == 2
    return [
        (
            Or(
                Not(p[i][0]),
                And(
                    [
                        b.argF[0][arg] <= bmax + b.offsets[i][0]
                        for arg in range(0, len(b.argF[i]))
                    ]
                ),
            )
        ),
        (
            Or(
                Not(p[i][1]),
                And(
                    [
                        b.argF[0][arg] <= bmax + b.offsets[i][1]
                        for arg in range(0, len(b.argF[i]))
                    ]
                ),
            )
        ),
    ]


################################################################################################


parser = argparse.ArgumentParser()
parser.add_argument("benchmark")
parser.add_argument(
    "-smt",
    "--smtlib",
    help="print benchmark problem in smtlib format and leave",
    action="store_true",
)
parser.add_argument(
    "-b",
    "--bounded",
    type=int,
    metavar="<ub>",
    help="add bounds to the problem (with nonstrict lower bound 0 and strict upper bound <ub>)",
)
args = parser.parse_args()

if args.benchmark.endswith(".smt2"):
    b = load_smt2(args.benchmark)
else:
    b = globals().get(args.benchmark)  # choose the benchmark here
    if not b:
        print("benchmark not found")
        exit(1)

if args.bounded:
    lb = 0  # non-strict
    ub = args.bounded  # strict
    Q = Or(b.x < lb, b.x >= ub, b.Q)
    Qp = Or(b.x < lb, b.x >= ub, b.Qp)
else:
    Q = b.Q
    Qp = b.Qp

print("input:")
print(b.F)
print(b.Q)
# print(b.Qp)
# print(b.x)
# print(b.occ)
# print(b.offsets)
print("===")
num_f = len(b.offsets)
assert len(b.occ) == num_f
assert len(b.argF) == num_f
assert all(len(b.offsets[i]) == len(b.occ[i]) for i in range(len(b.offsets)))

solver = z3.SolverFor("UFLIA")
# solver.set(mbqi=True)

if args.smtlib:
    print("(set-logic UFLIA)")
    solver.add(b.F)
    solver.add(ForAll(b.x, Q))
    print(solver.to_smt2())
else:
    # p = list(map(lambda l: list(map(lambda v: Bool(f"{v}p"), l)), b.occ))
    # print(p)
    p = [[Bool(f"{offset}p") for offset in func] for func in b.occ]  # is a pivot

    bmax = 0
    solver.add(b.F)
    solver.add(substitute(Q, (b.x, IntVal(0))))
    while solver.check() != unsat:
        solver.reset()
        solver.add(*maximality(b))
        solver.add(*reqpivot(b))
        # print(clash())
        solver.add(*clash(b))
        subs = [
            (b.x, IntVal(i)) for i in range(0, bmax + 1)
        ]  # list of wanted substitutions
        # print(subs)
        # print(list(map(lambda x : substitute(Q, x), subs)))
        solver.add(b.F)
        solver.add(list(map(lambda x: substitute(Q, x), subs)))
        res = solver.check()
        if res == sat:
            # print(solver)
            # print(solver.model())
            print("model:")
            model = solver.model()
            funcs = [f for f in model.decls() if f.arity() > 0]
            consts = [
                c for c in model.decls() if c.arity() == 0 if c.range() == IntSort()
            ]
            for c in consts:
                print(f"{c} -> {model.eval(c())}")
            for f in funcs:
                print(f)
                # print(model.get_interp(f))
                print_func_interp(get_func_interp(f, model, bmax, consts))
            cvc5_sygus = process_formula(b, flatten(p), funcs, consts, model)
            print("otherwise defined recursively as:")
            print(f"    {cvc5_sygus}")
            break

        bmax = bmax + 1
        solver.reset()
        solver.add(b.F)
        solver.add(list(map(lambda x: substitute(Q, x), subs)))
        print(res)
        print("Interval: ", [0, bmax])
        # TODO: print information on which cells have fixed values due to this

        # solver.add(F)
        # print(solver.to_smt2())
    else:
        print("final: unsat")
