;;; zero-order-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ch6/zero-order-vocab.scm.
;;; Library: complex-analysis.

;;; zero-order-vocab.scm -- the ORDER OF A ZERO of a holomorphic function, and the number of hits of a value
;;; in a sequence (for "zeros counted with multiplicities").  Proof-free vocabulary: its place at wiring is
;;; structure-library/ (after diff-on.scm, which defines HOLOMORPHIC-ON).  Library: complex-analysis.
;;; Laws: scratchpad/ch6/zero-order-laws.scm.  (CH6-B, 2026-10-29; shared with CH4-B.)
;;;
;;; HAS-ZERO-OF-ORDER(u, f, a, m): f is holomorphic on the open set u, a in u, m in NN, and
;;;   f(x) = (x - a)^m h(x) on u for some h holomorphic on u with h(a) /= 0.
;;;   The notes' "a zero of multiplicity m >= 0 at a"; m = 0 says exactly f(a) /= 0 (zero-order-zero-iff).
;;;   The factor h is GLOBAL on u: a local factorisation near a extends, since (x - a)^-m f is holomorphic
;;;   off a.  REJECTED ALTERNATIVES: the least k with f^(k)(a) /= 0 (needs the n-th derivative and a
;;;   separate factorisation theorem to be used); a local h on a ball (every consumer would have to glue).
;;; ZERO-ORDER(u, f, a): the m with HAS-ZERO-OF-ORDER(u, f, a, m) (unique: zero-order-unique; it exists for f
;;;   not identically zero on a connected u: zero-order-exists).
;;; COUNT-HITS(s, z, n): the number of k < n with s(k) = z (primitive recursion on n).
;;; Binders zo*_ / ch*_: used by no other body.

(def-predicate 'HAS-ZERO-OF-ORDER '(zou_ zof_ zoa_ zom_)
  '(AND (HOLOMORPHIC-ON zou_ zof_)
    (AND (IN zoa_ zou_)
      (AND (IN zom_ NN)
        (FORSOME zoh_ (AND (HOLOMORPHIC-ON zou_ zoh_)
          (AND (NOT (= (zoh_ zoa_) 0))
               (FORALL zox_ (IMPLIES (IN zox_ zou_) (= (zof_ zox_) (* (power (- zox_ zoa_) zom_) (zoh_ zox_))))))))))))
(notation! 'HAS-ZERO-OF-ORDER 'kind 'predicate 'arity 4
           'english "$2 has a zero of order $4 at $3 (on $1)")

(def-functoid 'ZERO-ORDER '(zou_ zof_ zoa_) '(IOTA zon_ (HAS-ZERO-OF-ORDER zou_ zof_ zoa_ zon_)))
(notation! 'ZERO-ORDER 'kind 'functoid 'arity 3 'english "the order of the zero of $2 at $3 (on $1)")

(def-by-nn-recursion 'COUNT-HITS '(chs_ chz_) 0 '(chn_ chv_) '(IF (= (chs_ chn_) chz_) (succ chv_) chv_))
(notation! 'COUNT-HITS 'kind 'functoid 'arity 3 'english "the number of k < $3 with $1(k) = $2")
