; quantifier-free non-linear real arithmetic (QF_NRA)
; Example: Nesbitt's inequality states that for positive real numbers a, b and c,
; a/(b+c) + (b/(a+c) + c/(a+b) >= 3/2.
; You can read more about it (including hand-written proofs) on Wikipedia:
; https://en.wikipedia.org/wiki/Nesbitt%27s_inequality
; Since QF_NRA is decidable, we can use SMT to prove that Nesbitt's inequality is correct.

(set-logic QF_NRA) ; prevent automatic theory selection

(push)
(declare-const sqrt Real)
(declare-const y Real)
(assert (= y (* sqrt sqrt)))
(assert (= y 1.5129))
(assert (> sqrt 0))
(check-sat)
(get-model)
(pop)

(push)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert 
    (and
        (> a 0)
        (> b 0)
        (> c 0)
        (not
            (>= 
                (+
                    (/ a (+ b c))
                    (/ b (+ a c))
                    (/ c (+ a b))
                )
                (/ 3.0 2.0)
            )
        )
    )
)
(check-sat)
(echo "unsat means there is no counterexample, i.e. Nesbitt's inequality is correct.")
(pop)

; Since QF_NRA is decidable, we can also try out a "real variant" of Fermat's last theorem,
; which we failed to solve with QF_NIA. Since we admit reals, there are now of course 
; solutions to the equation.
(push)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
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
(get-model)
(pop)