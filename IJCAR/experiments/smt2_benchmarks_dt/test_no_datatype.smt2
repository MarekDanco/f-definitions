; No datatype: f: Int -> Int, should bail out
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((x Int)) (= (f (+ x 1)) (+ (f x) 1))))
(check-sat)
