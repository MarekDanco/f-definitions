(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert
  (forall ((x Int))
    (> (+ (f x) (g (- x 1)))
       x)))
(check-sat)
