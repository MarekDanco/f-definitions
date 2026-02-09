; Add 3: f(nil)=0, forall x. f(cons(0,x))=f(x)+3
; Expected: SAT (f(x) = 3*|x|)
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 0))
(assert (forall ((x MyList)) (= (f (cons 0 x)) (+ (f x) 3))))
(check-sat)
