; benchmark generated from python API
(set-info :status unknown)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(assert
 (> c 0))
(assert
 (let ((?x28 (f 2)))
 (let ((?x29 (- 0 ?x28)))
 (>= ?x29 (+ (+ ?x29 c) ?x28)))))
(assert
 (forall ((x Int) )(let (($x54 (= (- 0 (f (+ x (- 2)))) (+ 0 (f (- x (- 1)))))))
(let (($x70 (>= x 0)))
(let (($x92 (and $x70 (<= x 100000))))
(=> $x92 $x54)))))
)
(check-sat)
