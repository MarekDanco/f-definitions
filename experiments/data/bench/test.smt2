; Test benchmark: f(x+1) = f(x) + 1, f(4) = 7
; Expected: SAT (f is increment starting from base value)
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 4) 7))
(assert (forall ((x Int)) (= (f (+ x 1)) (+ (f (+ x 0)) 1))))
(check-sat)
