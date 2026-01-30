; IncrConst benchmark: f(x+1) = f(x) + 1, f(c) = c
; Expected: SAT (defines f(x) = x)
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(assert (= (f c) c))
(assert (forall ((x Int)) (= (f (+ x 1)) (+ (f (+ x 0)) 1))))
(check-sat)
