(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((x Int))
  (=>
    (<=
      0 x 10
    )
    (= (f (+ x 2)) (+ (f (+ x 0)) 2))
  )
))
(check-sat)
