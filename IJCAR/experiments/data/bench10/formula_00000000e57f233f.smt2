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
 (forall ((x Int) )(let (($x61 (= (+ 0 (g (+ x 3))) (- (- 0 e) e))))
(let (($x76 (>= x 0)))
(let (($x77 (and $x76 (<= x 10))))
(=> $x77 $x61)))))
)
(check-sat)
