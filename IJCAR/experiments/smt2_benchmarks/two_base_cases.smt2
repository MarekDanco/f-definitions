; Two base cases: f(x+1) = f(x) + 1, f(0) = 0, f(5) = 5
; Expected: SAT (consistent base cases)
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (= (f 5) 5))
(assert (forall ((x Int)) (= (f (+ x 1)) (+ (f (+ x 0)) 1))))
(check-sat)
