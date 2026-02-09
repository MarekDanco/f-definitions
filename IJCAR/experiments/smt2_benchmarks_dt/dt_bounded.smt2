; Bounded: f(nil)=0, forall x. f(cons(0,x))=f(x)+1 AND f(cons(0,x))<=3
; Expected: UNSAT (eventually exceeds bound, since f(cons^4(nil))=4>3)
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 0))
(assert (forall ((x MyList)) (and (= (f (cons 0 x)) (+ (f x) 1)) (<= (f (cons 0 x)) 3))))
(check-sat)
