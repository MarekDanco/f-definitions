(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(assert (= (f 0) 1))
(assert (= (f 2) (+ (f 1) c)))
(assert (> c 0))
(assert (forall ((x Int))
  (=>
    (<=
      0 x
    )
    (= (f (+ x 3)) (f x))
  )
))
(check-sat)
