; Simplified Fibonacci-like: f(x+2) = f(x+1) + f(x), f(0) = 0, f(1) = 1
; NOTE: Has 3 function occurrences - exceeds current alg.py limitation
; This file is for future extensions or other solvers
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (= (f 1) 1))
(assert (forall ((x Int)) (= (f (+ x 2)) (+ (f (+ x 1)) (f (+ x 0))))))
(check-sat)
