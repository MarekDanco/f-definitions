(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(assert (= (f 0) (+ c 1)))
(assert (forall ((x Int))
  (=>
    (<=
      0 x 1000
    )
    (= (f (+ x 2)) (+ (f (+ x 0)) 2 x))
  )
))
(check-sat)
