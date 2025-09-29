(set-logic UFLIA)
(declare-fun g (Int) Int)
(assert
  (forall ((x Int))
    (and
      (< (g (+ x 2)) (+ (g (+ x 2)) 1))
      (forall ((w Int))
        (> x (g w))
      )
      (forall ((y Int) (z Int))
        (> y (g (+ x z)))
      )
      (> (g x) x
      )
    )
  )
)
(check-sat)
