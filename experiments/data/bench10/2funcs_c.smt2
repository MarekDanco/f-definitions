(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun c () Int)
(assert (> c 2))
(assert (= (f 0) 0))
(assert (> (g 0) (f 0)))
(assert (forall ((x Int))
  (=>
    (<=
      0 x 10
    )
    (and
      (= (f (+ x 1))
      (- (f (+ x 0)) (g (+ x c))))
      (= (+ c (g (+ x 1)))
      (+ (g (+ x c)) (f (+ x 0))))
    )
  )
))
(check-sat)
