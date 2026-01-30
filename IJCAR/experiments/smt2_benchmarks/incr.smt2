; Incr benchmark: f(x+1) = f(x) + 1, f(0) = 0
; Expected: SAT (defines f(x) = x for x >= 0)
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((x Int)) (= (f (+ x 1)) (+ (f (+ x 0)) 1))))
(check-sat)
