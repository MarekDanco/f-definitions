; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun g (Int) Int)
(declare-fun f (Int) Int)
(assert
 (> c 0))
(assert
 (> d 0))
(assert
 (<= (+ 0 c) (- 0 (g 2))))
(assert
 (= (- 0 c) (+ (+ (+ 0 (f 3)) c) c)))
(assert
 (< (- 0 (g (- 2))) (+ 0 (g 2))))
(assert
 (forall ((x Int) )(let (($x80 (< (- 0 (f (+ x 2))) (+ 0 (f (- x 0))))))
(let (($x95 (>= x 0)))
(let (($x117 (and $x95 (<= x 100000))))
(=> $x117 $x80)))))
)
(check-sat)
