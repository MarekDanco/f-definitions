(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(declare-fun d () Int)
(assert (> d c 0))
(assert (= (f c) (+ (f d) 2)))
(assert (forall ((x Int))
  (=>
    (<=
      0 x 10000
    )
    (= (* 3 (f (+ x c))) (+ (f (+ x d)) x))
  )
))
(check-sat)
