; The N-queens problem is to place N-queens on an N x N chess board such that no two queens threaten each other.
;
; We use N integer-valued variables, x1, x2, ..., xN, 
; where xi holds the row of the queen in column i

(declare-const x0 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(declare-const x5 Int)
(declare-const x6 Int)
(declare-const x7 Int)

(declare-const N Int)

(assert (= N 8))


(check-sat)
(get-model)