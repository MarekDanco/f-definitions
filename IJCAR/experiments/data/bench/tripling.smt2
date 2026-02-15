(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(assert (> c 1))
(assert (= (f 0) c))
(assert (forall ((x Int))
  (=>
    (<=
      0 x
    )
    (= (f (+ x 1)) (+ 1 (* 3 (f (+ x 0)))))
  )
))
(check-sat)
