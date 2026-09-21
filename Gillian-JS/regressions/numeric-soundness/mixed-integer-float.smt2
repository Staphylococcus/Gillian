; Pending: Z3 4.13.3 returns unknown (incomplete arithmetic).
; This is the conversion shape exposed by bundled array lemma preprocessing.
(set-option :timeout 5000)
(declare-const length Int)
(declare-const numericLength (_ FloatingPoint 11 53))
(assert (>= length 0))
(assert (fp.eq numericLength ((_ to_fp 11 53) RNE (to_real length))))
(check-sat)
(get-info :reason-unknown)
