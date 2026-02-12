; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(assert
 (> c 0))
(assert
 (>= (+ 0 (f c)) (- (- (- 0 (f 3)) c) (f c))))
(assert
 (forall ((x Int) )(> (- 0 (f (+ x 0))) (+ (- (- 0 (f (+ x (- 3)))) c) c)))
)
(check-sat)
