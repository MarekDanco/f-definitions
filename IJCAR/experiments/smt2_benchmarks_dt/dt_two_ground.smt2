; Two ground constraints: f(nil)=0, f(cons(5,nil))=1, forall x. f(cons(0,x))=f(x)+1
; Expected: SAT (the two ground facts are consistent with f being length)
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 0))
(assert (= (f (cons 5 nil)) 1))
(assert (forall ((x MyList)) (= (f (cons 0 x)) (+ (f x) 1))))
(check-sat)
