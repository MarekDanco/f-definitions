; Squared constraint: f(nil)=0, forall x. f(cons(0,x))=f(x)*f(x)
; Combined with f(cons(0,nil))=5, which requires 0*0=5
; Expected: UNSAT
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 0))
(assert (= (f (cons 0 nil)) 5))
(assert (forall ((x MyList)) (= (f (cons 0 x)) (* (f x) (f x)))))
(check-sat)
