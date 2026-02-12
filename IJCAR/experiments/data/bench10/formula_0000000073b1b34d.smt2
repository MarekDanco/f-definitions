; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun e () Int)
(declare-fun f (Int) Int)
(assert
 (> c 0))
(assert
 (> e 0))
(assert
 (let ((?x33 (- 0 e)))
 (>= (+ 0 (f e)) ?x33)))
(assert
 (let ((?x33 (- 0 e)))
 (<= ?x33 ?x33)))
(assert
 (forall ((x Int) )(let (($x59 (= (- 0 (f (+ x 0))) (- (+ 0 (f (+ x 3))) e))))
(let (($x75 (>= x 0)))
(let (($x76 (and $x75 (<= x 10))))
(=> $x76 $x59)))))
)
(check-sat)
