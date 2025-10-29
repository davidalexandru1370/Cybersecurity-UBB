; quantifier-free linear integer arithmetic (QF_LIA)
; for example, we can use QF_LIA to find integer
; solutions of systems of linear (in)equalities

(set-logic QF_LIA) ; prevent automatic theory selection

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)


(assert
  (and
    (= (- (+ (* 2 x) y) z) 8)
    (= (+ (- (* -3 x) y) (* 2 z)) -11)
    (= (+ (* -2 x) y (* 2 z) ) -3)
  )
)

(check-sat)
(get-model)