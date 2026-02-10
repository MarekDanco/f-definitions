(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((x Int)) 
  (=>
    (<=
      0 x 100
    )
    (= (f (+ x 1)) (+ x 3 (f (+ x 0)) (g (+ x 0))))
  )
))
(check-sat)
