; Decrement: f(x+1) = f(x) - 1, f(0) = 10
; Expected: SAT (f(x) = 10 - x)
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 0) 10))
(assert (forall ((x Int)) (= (f (+ x 1)) (- (f (+ x 0)) 1))))
(check-sat)
