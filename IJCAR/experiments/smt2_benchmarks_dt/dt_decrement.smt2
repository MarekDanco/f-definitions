; Decrement: f(nil)=100, forall x. f(cons(0,x))=f(x)-1
; Expected: SAT (f counts down from 100)
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 100))
(assert (forall ((x MyList)) (= (f (cons 0 x)) (- (f x) 1))))
(check-sat)
