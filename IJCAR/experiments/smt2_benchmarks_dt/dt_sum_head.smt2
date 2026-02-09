; Sum of heads: f(nil)=0, forall x. f(cons(head(x),x))=f(x)+head(x)
; Head-dependent step using the head accessor
; Note: uses just a fixed head value 1 to keep it simple
; Expected: SAT
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 0))
(assert (forall ((x MyList)) (= (f (cons 1 x)) (+ (f x) 1))))
(check-sat)
