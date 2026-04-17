; IncrConstArg benchmark: f(x+c) = f(x) + 1, f(c+1) = c, c >= 0
; Expected: SAT
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(assert (>= c 0))
(assert (= (f (+ c 1)) c))
(assert (forall ((x Int)) (= (f (+ x c)) (+ (f (+ x 0)) 1))))
(check-sat)
