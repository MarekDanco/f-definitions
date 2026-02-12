; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert
 (> c 0))
(assert
 (> d 0))
(assert
 (< (+ 0 (f 3)) (- 0 (f c))))
(assert
 (<= (- 0 (g 3)) (+ (+ 0 (f (- 1))) (f 3))))
(assert
 (< (- 0 (g 2)) (- 0 d)))
(assert
 (>= (+ 0 (g 1)) (- (+ 0 d) c)))
(assert
 (forall ((x Int) )(let (($x100 (< (+ 0 (f (- x c))) (+ (- (+ 0 (g (+ x (- 2)))) c) d))))
(let (($x117 (>= x 0)))
(let (($x126 (and $x117 (<= x 1000))))
(=> $x126 $x100)))))
)
(check-sat)
