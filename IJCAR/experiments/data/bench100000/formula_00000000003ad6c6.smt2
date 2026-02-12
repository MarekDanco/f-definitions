; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert
 (> c 0))
(assert
 (<= (+ 0 (f 3)) (+ (+ (+ 0 (g (- 1))) (f 2)) (f 2))))
(assert
 (> (- 0 (f c)) (- (- 0 c) (g 0))))
(assert
 (forall ((x Int) )(let (($x81 (= (+ 0 (f (- x 3))) (+ (+ (- 0 c) (g (- x (- 2)))) (g (+ x 0))))))
(let (($x100 (>= x 0)))
(let (($x122 (and $x100 (<= x 100000))))
(=> $x122 $x81)))))
)
(check-sat)
