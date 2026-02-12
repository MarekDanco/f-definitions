; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert
 (> c 0))
(assert
 (> (+ 0 (g 3)) (- (- (+ 0 c) (f (- 2))) c)))
(assert
 (forall ((x Int) )(let ((?x62 (g (- x 1))))
(let (($x71 (>= (- 0 (g (+ x 2))) (+ (+ (- 0 (f (- x (- 1)))) ?x62) ?x62))))
(let (($x84 (>= x 0)))
(let (($x90 (and $x84 (<= x 10))))
(=> $x90 $x71))))))
)
(check-sat)
