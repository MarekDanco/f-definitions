; Disjunctive constraint: forall x. f(cons(0,x))=f(x)+1 OR f(cons(0,x))=f(x)+2
; Expected: SAT (either increment by 1 or 2 at each step)
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 0))
(assert (forall ((x MyList)) (or (= (f (cons 0 x)) (+ (f x) 1)) (= (f (cons 0 x)) (+ (f x) 2)))))
(check-sat)
