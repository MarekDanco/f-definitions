; Non-zero base: f(nil)=10, forall x. f(cons(0,x))=f(x)+2
; Expected: SAT (f(x) = 10 + 2*|x|)
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 10))
(assert (forall ((x MyList)) (= (f (cons 0 x)) (+ (f x) 2))))
(check-sat)
