; The power operation ^ is Z3-specific.
(define-fun sqrt ((x Real)) Real (^ x 0.5))

(declare-const a Real)
(declare-const b Real)
(declare-const c Real)

; precondition
(assert (and (= a 1) (<= 0 (- (* b b) (* 4 c)))))

; negated weakest precondition
(assert (not
  (or
    (and (< (- (* b b) (* 4 a c)) 0) false) 
    (and
        (not (< (- (* b b) (* 4 a c)) 0))
        (= 0 (+
          (* a (^ (/ (+ (- b) (sqrt (- (* b b) (* 4 a c)))) 2) 2) )
          (* b (/ (+ (- b) (sqrt (- (* b b) (* 4 a c)))) 2) )
           c
        ))
    )
  )
))

(check-sat); unsat, i.e. verifies :)