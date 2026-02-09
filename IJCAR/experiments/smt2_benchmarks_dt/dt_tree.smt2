; Binary tree: f(leaf)=1, forall t1 t2. f(node(t1,t2))=f(t1)+1
; Uses a binary tree datatype with two recursive positions
; Expected: SAT (f counts depth along left subtree)
(declare-datatypes ((Tree 0)) (((leaf) (node (left Tree) (right Tree)))))
(declare-fun f (Tree) Int)
(assert (= (f leaf) 1))
(assert (forall ((t1 Tree) (t2 Tree)) (= (f (node t1 t2)) (+ (f t1) (f t2) 1))))
(check-sat)
