; Two inconsistent ground constraints: f(nil)=0, f(cons(5,nil))=7, forall x. f(cons(0,x))=f(x)+1
; Expected: UNSAT (f(cons(5,nil)) must be f(nil)+1=1, not 7)
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 0))
(assert (= (f (cons 5 nil)) 7))
(assert (forall ((x MyList)) (= (f (cons 0 x)) (+ (f x) 1))))
(check-sat)
