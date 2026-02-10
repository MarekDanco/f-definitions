(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(declare-fun d () Int)
(assert (> d c))
(assert (forall ((x Int))
  (=>
    (<=
      0 x 10000
    )
    (= (f (+ x c)) (+ (f (+ x d)) 1))
  )
))
(check-sat)
