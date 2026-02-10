(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-fun c () Int)
(assert (>= c 0))
(assert (= (f (+ c 1)) c))
(assert (forall ((x Int)) 
  (=>
    (<=
      0 x 100
    )
    (= (f (+ x c)) (+ (f (+ x 0)) 1))
  )
))
(check-sat)
