(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert
  (forall ((x Int))
    (< (+ (f x) (f (+ x 3)))
      (f (+ x 2)))
  )
)
(check-sat)
