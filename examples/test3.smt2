(set-logic UFLIA)
(declare-fun g (Int) Int)
(assert
  (forall ((x Int))
    (= (g (+ x 2))
      (+ (g x) 1))
  )
)
(check-sat)
