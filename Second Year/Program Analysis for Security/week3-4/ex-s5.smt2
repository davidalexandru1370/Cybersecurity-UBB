(declare-sort Pair)

(declare-const null Pair)

(declare-fun cons (Int Int) Pair)
(declare-fun first (Pair) Int)

; first axiom
(assert (= null (cons 0 0)))

; second axiom
(assert (forall ((x Int) (y Int)) 
    (= x (first (cons x y)))
))

; formula (negated for validity check)
(assert (not
  (= (first null) 0)
))

(check-sat)