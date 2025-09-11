(set-option :produce-unsat-cores true)
(set-logic UFLIA)

(declare-fun f (Int Int) Int)
(declare-fun g (Int) Int)
(declare-const a Int)
(declare-const b Int)

(assert (! (>= (f 3 a) (+ 4 (g b))) :named c1))
(assert (! (< (f 3 a) (+ 3 (g a))) :named c2))
(assert (! (= a 0) :named c3))
(assert (! (= b 0) :named c4))

(check-sat)
(get-unsat-core)
