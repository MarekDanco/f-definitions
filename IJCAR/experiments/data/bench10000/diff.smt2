(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (> (g 1) (g 2)))
(assert (> (f 1) (g 1)))
(assert (forall ((x Int))
  (=>
    (<=
      0 x 10000
    )
    (= (f (+ x 1)) (- (* 2 (f (+ x 0))) (* 3 (g (+ x 0)))))
  )
))
(check-sat)
