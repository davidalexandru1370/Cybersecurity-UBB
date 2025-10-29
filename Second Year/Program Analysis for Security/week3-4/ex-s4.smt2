
(declare-const a Bool)
(declare-const b Bool)

; precondition
(assert true)

; negation of weakest precondition
(assert (not
  (or
    (and
        a
        b
        (= true (=> a b))
    )
    (and
        (not b)
        (=
            false
            (=> a b)
        )
    )
    (and
        (not a)
        (= true (=> a b))
    )
  )
  
))

(check-sat) ; unsat means verifies