; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun e () Int)
(declare-fun g (Int) Int)
(assert
 (> c 0))
(assert
 (> e 0))
(assert
 (< (- 0 (g (- 2))) (+ (- 0 c) e)))
(assert
 (forall ((x Int) )(= (+ 0 (g (+ x 3))) (- (- 0 e) e)))
)
(check-sat)
