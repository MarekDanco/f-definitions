"""Small examples encoded in python classes.

The following notation is used:
    x = the quantified variable
    f, g, ... = function symbols
    offsets = the offsets of function symbols f, g, ...
    occ = variables for occurrences of function symbols (u, v in the paper)
    argF = arguments of uninterpreted function symbols in F
    F = ground part
    Q = quantified part
    Qp = propagator of Q
"""

from z3 import *


class Incr:
    x = Int("x")
    f = Function("f", IntSort(), IntSort())
    offsets = [[1, 0]]

    occ = [[Int("occf1"), Int("occf2")]]
    argF = [[0]]
    F = f(argF[0][0]) == 0
    Q = f(x + offsets[0][0]) == f(x + offsets[0][1]) + IntVal(1)
    Qp = occ[0][0] == occ[0][1] + 1


class IncrConst:
    x = Int("x")
    f = Function("f", IntSort(), IntSort())
    c = Int("c")
    offsets = [[1, 0]]

    occ = [[Int("occf1"), Int("occf2")]]
    argF = [[c]]
    F = f(argF[0][0]) == c
    Q = f(x + offsets[0][0]) == f(x + offsets[0][1]) + IntVal(1)
    Qp = occ[0][0] == occ[0][1] + 1


class IncrConstArg:
    x = Int("x")
    f = Function("f", IntSort(), IntSort())
    c = Int("c")
    offsets = [[c, 0]]

    occ = [[Int("occf1"), Int("occf2")]]
    argF = [[c + 1]]
    F = [c >= 0, f(argF[0][0]) == c]
    Q = f(x + offsets[0][0]) == f(x + offsets[0][1]) + IntVal(1)
    Qp = occ[0][0] == occ[0][1] + 1


class Incr2Functions:
    x = Int("x")
    f = Function("f", IntSort(), IntSort())
    g = Function("g", IntSort(), IntSort())
    offsets = [[1, 0], [0]]

    occ = [
        [Int("occf1"), Int("occf2")],
        [Int("occg1")],
    ]
    argF = [[0], []]
    F = f(argF[0][0]) == 0
    Q = f(x + offsets[0][0]) == IntVal(0) + f(x + offsets[0][1]) + g(x + offsets[1][0])
    Qp = occ[0][0] == occ[0][1] + occ[1][0]


class Test:
    x = Int("x")
    f = Function("f", IntSort(), IntSort())
    offsets = [[1, 0]]

    occ = [[Int("occf1"), Int("occf2")]]
    argF = [[4]]
    F = f(argF[0][0]) == 7
    Q = f(x + offsets[0][0]) == f(x + offsets[0][1]) + IntVal(1)
    Qp = occ[0][0] == occ[0][1] + 1
