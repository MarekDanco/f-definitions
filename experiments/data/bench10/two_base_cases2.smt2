(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun c () Int)
(assert (> c 0))
(assert (= (f 0) 0))
(assert (= (f 5) 5))
(assert (< (f 5) (g 3)))
(assert (forall ((x Int))
  (=>
    (<=
      0 x 10
    )
    (= (f (+ x 1)) (+ c (f (+ x 0)) (g x)))
  )
))
(check-sat)
