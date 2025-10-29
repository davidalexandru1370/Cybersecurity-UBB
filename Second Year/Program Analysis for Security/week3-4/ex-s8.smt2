; quantifier-free non-linear integer arithmetic (QF_NIA)
; prove that (x+y)^2 = x^2 + 2*x*y + y^2

(set-logic QF_NIA)
(set-option :timeout 5000)

(declare-const x Int)
(declare-const y Int)

(push)
(declare-const sqrt Int)
(assert (= y (* sqrt sqrt)))
(assert (= y 15129))
(assert (> sqrt 0))
(check-sat)
(get-model)
(pop)

(push)
(assert
    (not
        (=
            (+
                (* x x)
                (* 2 x y)
                (* y y)
            )
            (*
                (+ x y)
                (+ x y)
            )
        )
    )
)

(check-sat)
(echo "unsat means the formula is valid")
; unsat
(pop)

; QF_NIA is *undecidable*, i.e. the solver may not terminate or output unknown. 
; Here is an example.
; Fermat's last theorem: a^n + b^n = c^n has no solutions for any n > 2 and positive integers a,b,c
; It's unsurprising that an SMT solver cannot just deal with it :)
; The proof of this theorem is often seen as one of the most complicated one in all of mathematics.
; Even if we fix n.
(push)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert 
    (and
        (> a 0)
        (> b 0)
        (> c 0)
        (=
            (+ (* a a a a) (* b b b b))
            (* c c c c)
        )
    )
)
(check-sat)
(pop)