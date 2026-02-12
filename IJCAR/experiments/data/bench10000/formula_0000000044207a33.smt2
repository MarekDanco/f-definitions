; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun g (Int) Int)
(declare-fun f (Int) Int)
(assert
 (> c 0))
(assert
 (< (- 0 (f 0)) (+ (- 0 (f (- 3))) (g (- 1)))))
(assert
 (= (- 0 (g (- 3))) (- 0 (g 2))))
(assert
 (= (- 0 (f 2)) (+ (+ 0 (f 2)) (f (- 3)))))
(assert
 (= (+ 0 c) (- (+ (+ 0 (g 2)) (f (- 1))) (f 2))))
(assert
 (forall ((x Int) )(let (($x98 (< (+ 0 (f (- x c))) (+ (- (- 0 c) c) (g (- x 3))))))
(let (($x114 (>= x 0)))
(let (($x126 (and $x114 (<= x 10000))))
(=> $x126 $x98)))))
)
(check-sat)
