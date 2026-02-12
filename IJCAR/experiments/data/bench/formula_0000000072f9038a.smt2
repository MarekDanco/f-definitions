; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun e () Int)
(declare-fun f (Int) Int)
(assert
 (> c 0))
(assert
 (> e 0))
(assert
 (<= (- 0 (f (- 1))) (+ (- 0 (f 3)) c)))
(assert
 (forall ((x Int) )(= (+ 0 (f (- x (- 1)))) (+ (+ 0 (f (- x 0))) e)))
)
(check-sat)
