;;; dual-stamps.scm -- the four definitional read-offs of structure-library/dual-space.scm, PROVEN.
;;; Agent DUAL-FIX, 2026-10-26.  DESTINATION: theorem-library/dual-space-readoffs.scm.  Library: analysis.
;;; Load window: right after structure-library/dual-space (and the files that define its heads); no
;;; theorem citation except the definitions' own macetes.  Helper prefix: dsr-.
;;;
;;; Each statement is the stamp's, character for character, under a new name; the integrator retires
;;; the stamps (dual-vec-membership, dual-carrier, dual-norm-value, dual-scal) and renames the citers
;;; (theorem-library/dual-nvs.scm, tvs-bidual.scm: see scratchpad/dualfix2/).

(define (dsr-qed! name)
  (if (not (proof-done? *ps*))
      (for-each (lambda (l) (display ";; DSR OPEN ") (display (expression->string (dk-goal-of l))) (newline))
                (dk-open-leaves)))
  (qed name) (topic! name 'analysis))

(sp (make-wff '(FORALL m (FORALL f
       (IFF (IN f (DUAL-VEC m))
            (AND (IN f (FUN (VEC m) RR))
                 (IS-BOUNDED-LINEAR-FUNCTIONAL m f)))))))
(dk-peel!)
(mac 'DUAL-VEC)
(for-each
  (lambda (l)
    (dk-focus! l)
    (if (dk-head-is? (dk-goal) 'AND)
        (let ((h (find-first (lambda (f) (and (dk-head-is? f 'IN) (dk-head-is? (caddr f) 'SEP))) (dk-asms))))
          (sep-me h)
          (dk-split-all!)
          (dk-conj-close! (lambda () (ass))))
        (begin
          (dk-split-all!)
          (in-sep! (lambda () (ass)) (lambda () (ass))))))
  (dk-opened (lambda () (di))))
(dsr-qed! 'dual-vec-membership-proven)

;;; THE OTHER THREE ARE NOT PROVABLE AS STATED.  Each reads a slot of the LIST DUAL(m), and since the
;;; 2026-10-01 decision a list denotes only when every component is a set: `nth-r' owes DUAL(m) = DUAL(m),
;;; i.e. DUAL-VEC(m) in SET (the ring view and the lambdas certify themselves).  For an m whose VEC is
;;; not a set (m = 0, not a tuple at all) the left side of `==' is undefined while
;;; NORMED-FIELD-AS-COMMUTATIVE-RING(RR-NORMED-FIELD), resp. DUAL-VEC(m) once it is a defined class,
;;; is defined, so dual-scal / dual-carrier assert something false there; dual-norm-value likewise
;;; when DUAL-VEC(m) is a defined proper class with a member.  Proven here with the one guard the read-off
;;; needs, (IN (DUAL-VEC m) SET), which every citer has from dual-vec-in-set (IS-NORMED-VECTOR-SPACE m).
(define (dsr-certify!)
  (dk-cite! 'rr-is-normed-field)
  (dk-cite! 'normed-field-as-commutative-ring-is-commutative-ring 'RR-NORMED-FIELD)
  (if (not (dk-asm? '(IN RR SET))) (fact 'rr-is-set)))

(sp (make-wff '(FORALL m (IMPLIES (IN (DUAL-VEC m) SET)
       (== (SCAL (DUAL m)) (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD))))))
(dk-peel!)
(dsr-certify!)
(mac 'DUAL)
(slot 'SCAL)
(nth-r)
(qrfl)
(dsr-qed! 'dual-scal-proven)

(sp (make-wff '(FORALL m (IMPLIES (IN (DUAL-VEC m) SET) (== (VEC (DUAL m)) (DUAL-VEC m))))))
(dk-peel!)
(dsr-certify!)
(mac 'DUAL)
(slot 'VEC)
(nth-r)
(qrfl)
(dsr-qed! 'dual-carrier-proven)

(sp (make-wff '(FORALL m (IMPLIES (IN (DUAL-VEC m) SET) (FORALL f (IMPLIES (IN f (DUAL-VEC m))
       (== ((VNRM (DUAL m)) f) (DUAL-NORM m f))))))))
(dk-peel!)
(dsr-certify!)
(mac 'DUAL)
(slot 'VNRM)
(nth-r)
(dk-lam-b!)
(qrfl)
(dsr-qed! 'dual-norm-value-proven)
