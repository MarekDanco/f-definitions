; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(assert
 (> c 0))
(assert
 (< (+ 0 (f 3)) (- 0 (f c))))
(assert
 (let ((?x33 (- 0 c)))
 (> ?x33 (+ (- (- 0 (f (- 3))) c) (f 0)))))
(assert
 (forall ((x Int) )(let (($x78 (< (+ 0 (f (+ x (- 3)))) (- (+ (- 0 c) c) (f (+ x (- 1)))))))
(let (($x94 (>= x 0)))
(let (($x100 (and $x94 (<= x 1000))))
(=> $x100 $x78)))))
)
(check-sat)
