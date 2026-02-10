(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(assert (= (f c) c))
(assert (forall ((x Int)) 
  (=>
    (<=
      0 x 1000
    )
    (= (f (+ x 1)) (+ (f (+ x 0)) 1))
  )
))
(check-sat)
