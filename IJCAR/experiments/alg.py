from z3 import *

def def_example():                          # f(0)=0 /\ forall x . x<0 \/ x>=1000 \/ f(x+1)=f(x)+1
    global offsets, x, occf, argf, F, Q, Qp
    f= Function('f', IntSort(), IntSort())
    offsets= [1, 0]
    x= Int('x')
    occf= [Int('occf1'), Int('occf2')]      # variables for occurrences of f (u, v in the paper)
    argf= [0]                               # arguments of f in F
    F= f(argf[0])==0
    Q= Or(x<0, x>=1000, f(x+offsets[0])==f(x+offsets[1])+1)
    Qp= Or(x<0, x>=1000, occf[0]==occf[1]+1)

    

# current restrictions:
  # one function symbol
  # two occurrences of function symbol in quantified part
  # positive indices only
def_example()
assert(len(offsets)==len(occf))

solver = z3.SolverFor("UFLIA")
# solver.set(mbqi=True)

pf= [Bool('pf1'), Bool('pf2')]          # is a pivot
assert(len(pf)==len(occf))
bmax= 0
res="UNSAT"
solver.add(F, substitute(Q, (x, IntVal(0))))
while(solver.check()!=unsat):
    solver.reset() 
    solver.add(Or(Not(pf[0]), Not(pf[1]), offsets[0]==offsets[1]))  # maximality condition, equality
    solver.add(Or(Not(pf[0]), pf[1], offsets[0]>offsets[1]))        # maximality condition, rest
    solver.add(Or(Not(pf[1]), pf[0], offsets[1]>offsets[0]))
    solver.add(Or(pf[0], pf[1], ForAll(x, ForAll(occf[0], ForAll(occf[1], Qp)))))       # ReqPivot (4 cases)
    solver.add(Or(pf[0], Not(pf[1]), ForAll(x, ForAll(occf[1], Exists(occf[0], Qp)))))
    solver.add(Or(Not(pf[0]), pf[1], ForAll(x, ForAll(occf[0], Exists(occf[1], Qp)))))
    solver.add(Or(Not(pf[0]), Not(pf[1]), Exists(x, Exists(occf[1], ForAll(occf[0], Qp)))))
    solver.add(Or(Not(pf[0]), And([argf[arg]<=bmax+offsets[0] for arg in range(0, len(argf))]))) # clash condition
    solver.add(Or(Not(pf[1]), And([argf[arg]<=bmax+offsets[1] for arg in range(0, len(argf))])))
    solver.add(F)
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

