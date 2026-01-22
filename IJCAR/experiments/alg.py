from z3 import *
from benchmarks import *

def maximality(i):
    return [Or(Not(p[i][0]), Not(p[i][1]), b.offsets[i][0]==b.offsets[i][1]),  # equality
            Or(Not(p[i][0]), p[i][1], b.offsets[i][0]>b.offsets[i][1]),        # rest
            Or(Not(p[i][1]), p[i][0], b.offsets[i][1]>b.offsets[i][0])]

def reqpivot():
    assert(len(p)==1)                                                      # TODO: implement for several function symbols
    return [(Or(p[0][0], p[0][1], ForAll(b.x, ForAll(b.occ[0][0], ForAll(b.occ[0][1], b.Qp))))),
            (Or(p[0][0], Not(p[0][1]), ForAll(b.x, ForAll(b.occ[0][1], Exists(b.occ[0][0], b.Qp))))),
            (Or(Not(p[0][0]), p[0][1], ForAll(b.x, ForAll(b.occ[0][0], Exists(b.occ[0][1], b.Qp))))),
            (Or(Not(p[0][0]), Not(p[0][1]), Exists(b.x, Exists(b.occ[0][1], ForAll(b.occ[0][0], b.Qp)))))]

def clash(i):
    return [(Or(Not(p[i][0]), And([b.argF[0][arg]<=bmax+b.offsets[i][0] for arg in range(0, len(b.argF[i]))]))),
            (Or(Not(p[i][1]), And([b.argF[0][arg]<=bmax+b.offsets[i][1] for arg in range(0, len(b.argF[i]))])))]
    
# current restrictions:
  # one function symbol
  # two occurrences of function symbol in quantified part
  # positive indices only

b= Incr                                                                          # choose the benchmark here
print(b.offsets)
assert(len(b.offsets)==len(b.occ))
assert(len(b.occ)==len(b.argF))
assert(all(len(b.offsets[i])==len(b.occ[i]) for i in range(len(b.offsets))))

solver = z3.SolverFor("UFLIA")
# solver.set(mbqi=True)

p= list(map(lambda l : list(map(lambda v : Bool(v.__repr__()+"p"), l)), b.occ))  # is a pivot
print(p)
bmax= 0
res="UNSAT"
solver.add(b.F, substitute(b.Q, (b.x, IntVal(0))))
while(solver.check()!=unsat):
    solver.reset() 
    solver.add(*maximality(0))
    solver.add(*reqpivot())
    solver.add(*clash(0))        
    subs=[ (b.x, IntVal(i)) for i in range(0,bmax+1)]                 # list of wanted substitutions
    print(subs)    
    print(list(map(lambda x : substitute(b.Q, x), subs)))
    solver.add(And(list(map(lambda x : substitute(b.Q, x), subs))))
    if(solver.check()==sat):
        res="SAT"
        print(solver.model())
        break
    
    bmax= bmax+1
    solver.reset()
    solver.add(b.F);
    solver.add(And(list(map(lambda x : substitute(b.Q, x), subs))))
print(res);
print("Interval: ", [0, bmax])
# solver.add(F)
#print(solver.to_smt2())

