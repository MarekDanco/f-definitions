(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (= (f 0) 0))
(assert (= (f 5) 5))
(assert (< (f 5) (g 3)))
(assert (forall ((x Int))
  (=>
    (<=
      0 x
    )
    (= (f (+ x 1)) (+ (f (+ x 0)) (g x)))
  )
))
(check-sat)
