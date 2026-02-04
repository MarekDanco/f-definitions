; Incr2Functions benchmark: f(x+1) = f(x) + g(x), f(0) = 0
; Expected: SAT
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun c () Int)
(assert (>= c 1))
(assert (= (f 0) 0))
(assert (= (g 0) 1))
(assert (forall ((x Int)) 
  (= (f (+ x 1)) 
  (+ (f (+ x 0)) (g (+ x 0)) (g (+ x c))))
))
(check-sat)
