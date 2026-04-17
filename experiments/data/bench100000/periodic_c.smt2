(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(assert (= (f 0) 1))
(assert (= (f 1) (f 2)))
(assert (> c 0))
(assert (forall ((x Int))
  (=>
    (<=
      0 x 100000
    )
    (= (f (+ x 3)) (+ c (f x)))
  )
))
(check-sat)
