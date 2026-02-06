(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun c () Int)
(assert (> c 1))
(assert (= (f 0) 0))
(assert (> (g 2) (f (+ c 1))))
(assert (forall ((x Int)) 
  (=>
    (<=
      0 x 10
    )
    (and
      (= (f (- x 1)) 
      (- (f (+ x 0)) (g (- x c))))
      (= (g (+ x 1)) 
      (+ (g (- x c)) (f (+ x 0))))
    )
  )
))
(check-sat)
