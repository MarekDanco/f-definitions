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
 (< (+ 0 (g e)) (+ (- (+ 0 (f (- 2))) (g 2)) (f 1))))
(assert
 (forall ((x Int) )(let (($x73 (> (+ 0 (f (- x (- 2)))) (+ (- (- 0 e) (g (- x 3))) e))))
(let (($x81 (>= x 0)))
(let (($x101 (and $x81 (<= x 1000))))
(=> $x101 $x73)))))
)
(check-sat)
