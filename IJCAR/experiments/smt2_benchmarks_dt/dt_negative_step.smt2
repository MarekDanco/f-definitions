; Negative step: f(nil)=0, forall x. f(cons(0,x))=f(x)-5
; Expected: SAT (f goes negative)
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 0))
(assert (forall ((x MyList)) (= (f (cons 0 x)) (- (f x) 5))))
(check-sat)
