; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun e () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert
 (> c 0))
(assert
 (> e 0))
(assert
 (>= (+ 0 (f 1)) (- (- 0 c) (f 2))))
(assert
 (> (+ 0 c) (+ 0 (g 0))))
(assert
 (<= (+ 0 e) (+ (- (- 0 e) e) c)))
(assert
 (let ((?x34 (- 0 c)))
 (<= ?x34 (+ (- (- 0 e) c) (g c)))))
(assert
 (forall ((x Int) )(< (+ 0 (f (+ x (- 1)))) (+ (- (- 0 c) (g (- x 3))) (g (- x (- 1))))))
)
(check-sat)
