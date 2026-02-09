; No ground part: forall x. f(cons(0,x))=f(x)+1
; Expected: SAT (any base value works, step is fixed)
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (forall ((x MyList)) (= (f (cons 0 x)) (+ (f x) 1))))
(check-sat)
