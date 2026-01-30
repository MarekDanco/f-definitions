; Doubling: f(x+1) = 2*f(x), f(0) = 1
; Expected: SAT (f(x) = 2^x)
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 0) 1))
(assert (forall ((x Int)) (= (f (+ x 1)) (* 2 (f (+ x 0))))))
(check-sat)
