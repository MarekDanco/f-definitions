(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (= (f 5) 5))
(assert (forall ((x Int))
  (=>
    (<=
      0 x 1000
    )
    (= (f (+ x 1)) (+ (f (+ x 0)) 1))
  )
))
(check-sat)
