(declare-fun f (Int) Int)
(assert (forall ((x Int)) (> (f (+ x 1)) (f x))))
(check-sat)
