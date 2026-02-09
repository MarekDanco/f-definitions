; Absolute difference bounded: f(nil)=0, forall x. |f(cons(0,x))-f(x)| <= 1
; Using conjunction of two inequalities instead of abs
; Expected: SAT (many solutions, e.g. f constant 0 satisfies it)
(declare-datatypes ((MyList 0)) (((nil) (cons (head Int) (tail MyList)))))
(declare-fun f (MyList) Int)
(assert (= (f nil) 0))
(assert (forall ((x MyList)) (and (<= (- (f (cons 0 x)) (f x)) 1) (>= (- (f (cons 0 x)) (f x)) (- 1)))))
(check-sat)
