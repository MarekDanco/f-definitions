(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= (f 0) 0))
(assert (= (g 0) 1))
(assert (forall ((x Int))
  (=>
    (<=
      0 x 10000
    )
    (= (f (+ x 1)) (+ (f (+ x 0)) (g (+ x 0))))
  )
))
(check-sat)
