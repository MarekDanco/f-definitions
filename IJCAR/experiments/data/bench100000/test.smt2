(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 4) 7))
(assert (forall ((x Int))
  (=>
    (<=
      0 x 100000
    )
    (= (f (+ x 1)) (+ (f (+ x 0)) 1))
  )
))
(check-sat)
