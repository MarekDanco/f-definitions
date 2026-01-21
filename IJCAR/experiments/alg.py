from z3 import *

solver = z3.SolverFor("UFLIA")
solver.set(mbqi=True)

pf= [Bool('pf1'), Bool('pf2')]          # is a pivot
f= Function('f', IntSort(), IntSort())
offsets= [1, 0]
x= Int('x')
occf1= Int('occf1')
occf2= Int('occf2')
argf= [0]
F= f(argf[0])==0
Q= Or(x<0, x>=1000, f(x+offsets[0])==f(x+offsets[1])+1)
Qp= Or(x<0, x>=1000, occf1==occf2+1)
bmax= 0
res="UNSAT"
solver.add(F, substitute(Q, (x, IntVal(0))))
while(solver.check()!=unsat):
    solver.reset()
    solver.add(Or(Not(pf[0]), Not(pf[1]), offsets[0]==offsets[1]))
    solver.add(Or(Not(pf[0]), pf[1], offsets[0]>offsets[1]))
    solver.add(Or(Not(pf[1]), pf[0], offsets[1]>offsets[0]))
    solver.add(Or(pf[0], pf[1], ForAll(x, ForAll(occf1, ForAll(occf2, Qp)))))
    solver.add(Or(pf[0], Not(pf[1]), ForAll(x, ForAll(occf2, Exists(occf1, Qp)))))
    solver.add(Or(Not(pf[0]), pf[1], ForAll(x, ForAll(occf1, Exists(occf2, Qp)))))
    solver.add(Or(Not(pf[0]), Not(pf[1]), Exists(x, Exists(occf2, ForAll(occf1, Qp)))))
    solver.add(Or(Not(pf[0]), And([argf[arg]<=bmax+offsets[0] for arg in range(0, len(argf))])))
    solver.add(Or(Not(pf[1]), And([argf[arg]<=bmax+offsets[1] for arg in range(0, len(argf))])))
    subs=[ (x, IntVal(i)) for i in range(0,bmax+1)]
    print(subs)
    solver.add(F)
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

