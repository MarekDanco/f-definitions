from z3 import *

global x
x= Int('x')                                 # the quantified variable

def def_example():                          # f(0)=0 /\ forall x . x<0 \/ x>=1000 \/ f(x+1)=f(x)+1
    global offsets, occ, argF, F, Q, Qp         # the variable needed to define a problem instance
    
    f= Function('f', IntSort(), IntSort())
    offsets= [[1, 0]]

    occ= [[Int('occf1'), Int('occf2')]]     # variables for occurrences of funct. symb. (u, v in the paper)
    argF= [[0]]                             # arguments of uninterpreted function symbols in F
    F= f(argF[0][0])==0
    Q= Or(x<0, x>=1000, f(x+offsets[0][0])==f(x+offsets[0][1])+1)
    Qp= Or(x<0, x>=1000, occ[0][0]==occ[0][1]+1)
    print(offsets)

def maximality(i):
    return [Or(Not(p[i][0]), Not(p[i][1]), offsets[i][0]==offsets[i][1]),  # equality
            Or(Not(p[i][0]), p[i][1], offsets[i][0]>offsets[i][1]),        # rest
            Or(Not(p[i][1]), p[i][0], offsets[i][1]>offsets[i][0])]

def reqpivot():
    assert(len(p)==1)                                                      # TODO: implement for several function symbols
    return [(Or(p[0][0], p[0][1], ForAll(x, ForAll(occ[0][0], ForAll(occ[0][1], Qp))))),
            (Or(p[0][0], Not(p[0][1]), ForAll(x, ForAll(occ[0][1], Exists(occ[0][0], Qp))))),
            (Or(Not(p[0][0]), p[0][1], ForAll(x, ForAll(occ[0][0], Exists(occ[0][1], Qp))))),
            (Or(Not(p[0][0]), Not(p[0][1]), Exists(x, Exists(occ[0][1], ForAll(occ[0][0], Qp)))))]

def clash(i):
    return [(Or(Not(p[i][0]), And([argF[0][arg]<=bmax+offsets[i][0] for arg in range(0, len(argF[i]))]))),
            (Or(Not(p[i][1]), And([argF[0][arg]<=bmax+offsets[i][1] for arg in range(0, len(argF[i]))])))]
    
# current restrictions:
  # one function symbol
  # two occurrences of function symbol in quantified part
  # positive indices only
def_example()
print(offsets)
assert(len(offsets)==len(occ))
assert(len(occ)==len(argF))
assert(all(len(offsets[i])==len(occ[i]) for i in range(len(offsets))))

solver = z3.SolverFor("UFLIA")
# solver.set(mbqi=True)

p= list(map(lambda l : list(map(lambda v : Bool(v.__repr__()+"p"), l)), occ))  # is a pivot
print(p)
bmax= 0
res="UNSAT"
solver.add(F, substitute(Q, (x, IntVal(0))))
while(solver.check()!=unsat):
    solver.reset() 
    solver.add(*maximality(0))
    solver.add(*reqpivot())
    solver.add(*clash(0))        
    subs=[ (x, IntVal(i)) for i in range(0,bmax+1)]                 # list of wanted substitutions
    print(subs)    
    print(list(map(lambda x : substitute(Q, x), subs)))
    solver.add(And(list(map(lambda x : substitute(Q, x), subs))))
    if(solver.check()==sat):
        res="SAT"
        print(solver.model())
        break
    
    bmax= bmax+1
    solver.reset()
    solver.add(F);
    solver.add(And(list(map(lambda x : substitute(Q, x), subs))))
print(res);
print("Interval: ", [0, bmax])
# solver.add(F)
#print(solver.to_smt2())

