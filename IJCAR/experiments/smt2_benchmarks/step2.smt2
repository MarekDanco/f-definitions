; Step 2: f(x+2) = f(x) + 2, f(0) = 0
; Expected: SAT (f defines values at even positions)
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((x Int)) (= (f (+ x 2)) (+ (f (+ x 0)) 2))))
(check-sat)
