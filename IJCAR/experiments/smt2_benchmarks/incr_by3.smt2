; Increment by 3: f(x+1) = f(x) + 3, f(0) = 0
; Expected: SAT (f(x) = 3x)
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((x Int)) (= (f (+ x 1)) (+ (f (+ x 0)) 3))))
(check-sat)
