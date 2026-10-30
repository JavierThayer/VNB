;;; ch4d-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ch4d/ch4d-vocab.scm.
;;; Library: complex-analysis.

;;; ch4d-vocab.scm -- complex-analysis 4.4 (CH4-D, 2026-10-29): the order of a pole.  Proof-free vocabulary;
;;; destination structure-library/, after ch4b-vocab (IS-POLE).  Library: complex-analysis.
;;;
;;; POLE-ORDER(f, a)   the N with IS-POLE(f, a, N) (Def 4.7: "a pole of order N").  Unique (pole-order-unique,
;;;                    ch4d-logder.scm); POLE-ORDER(f, a) = N whenever IS-POLE(f, a, N) (pole-order-value).
;;;                    The degree deg(f, a) of Def 4.16 is ZERO-ORDER at a zero and -POLE-ORDER at a pole.
;;; Binders pof_ poa_ pon_: used by no other body.
(def-functoid 'POLE-ORDER '(pof_ poa_) '(IOTA pon_ (IS-POLE pof_ poa_ pon_)))
(notation! 'POLE-ORDER 'kind 'functoid 'arity 2 'english "the order of the pole of $1 at $2")
