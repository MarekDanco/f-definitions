(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(assert (> (f c) (f (+ c 7))))
(assert
  (forall ((x Int))
    (and
      (> (f (+ x 7))
        (- (f x) (f (+ x 3))))
      (> (f (+ x 3))
        (f (- x 1)))
    ))
)
(check-sat)
