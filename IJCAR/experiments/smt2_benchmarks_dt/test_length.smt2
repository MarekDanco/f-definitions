; Length benchmark: f(nil)=0, forall x. f(cons(1,x))=f(x)+1
; Expected: SAT (f is list length)
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 0))
(assert (forall ((x MyList)) (= (f (cons 1 x)) (+ (f x) 1))))
(check-sat)
