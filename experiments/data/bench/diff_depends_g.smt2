; Difference depends on g: f(x+1) - f(x) = g(x), f(0) = 0, g(0) = 1
; Expected: SAT
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= (f 0) 0))
(assert (= (g 0) 1))
(assert (forall ((x Int)) (= (f (+ x 1)) (+ (f (+ x 0)) (g (+ x 0))))))
(check-sat)
;(get-model)
