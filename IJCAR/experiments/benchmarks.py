from z3 import *

class Incr:
    x= Int('x')                                 # the quantified variable    
    f= Function('f', IntSort(), IntSort())
    offsets= [[1, 0]]

    occ= [[Int('occf1'), Int('occf2')]]     # variables for occurrences of funct. symb. (u, v in the paper)
    argF= [[0]]                             # arguments of uninterpreted function symbols in F
    F= f(argF[0][0])==0
    Q= Or(x<0, x>=1000, f(x+offsets[0][0])==f(x+offsets[0][1])+1)
    Qp= Or(x<0, x>=1000, occ[0][0]==occ[0][1]+1)

class IncrConst:
    x= Int('x')                                 # the quantified variable    
    f= Function('f', IntSort(), IntSort())
    c= Int('c')
    offsets= [[1, 0]]

    occ= [[Int('occf1'), Int('occf2')]]     # variables for occurrences of funct. symb. (u, v in the paper)
    argF= [[0]]                             # arguments of uninterpreted function symbols in F
    F= f(argF[0][0])==c
    Q= Or(x<0, x>=1000, f(x+offsets[0][0])==f(x+offsets[0][1])+1)
    Qp= Or(x<0, x>=1000, occ[0][0]==occ[0][1]+1)

    
class Incr2Functions:
    x= Int('x')                                 # the quantified variable    
    f= Function('f', IntSort(), IntSort())
    g= Function('g', IntSort(), IntSort())
    offsets= [[1, 0],[0]]

    occ= [[Int('occf1'), Int('occf2')],[Int('occg1')]]     # variables for occurrences of funct. symb. (u, v in the paper)
    
    argF= [[0],[]]                             # arguments of uninterpreted function symbols in F
    F= f(argF[0][0])==0
    Q= Or(x<0, x>=1000, f(x+offsets[0][0])==f(x+offsets[0][1])+g(x+offsets[1][0]))
    Qp= Or(x<0, x>=1000, occ[0][0]==occ[0][1]+occ[1][0])

class Test:
    x= Int('x')                                 # the quantified variable    
    f= Function('f', IntSort(), IntSort())
    offsets= [[1, 0]]

    occ= [[Int('occf1'), Int('occf2')]]     # variables for occurrences of funct. symb. (u, v in the paper)
    argF= [[4]]                             # arguments of uninterpreted function symbols in F
    F= f(argF[0][0])==7
    Q= Or(x<0, x>=1000, f(x+offsets[0][0])==f(x+offsets[0][1])+1)
    Qp= Or(x<0, x>=1000, occ[0][0]==occ[0][1]+1)
