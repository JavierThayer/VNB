;;; deriv-on-read-off.scm -- DERIV-ON reads off IS-DIFF-ON.
;;; Batch 27-A follow-on, 2026-09-24.
;;;
;;; DERIV-ON(K, U, f, a) is IOTA L. IS-DIFF-ON(K, U, f, a, L)
;;; (structure-library/diff-on.scm).  Over a normed field with nonzero elements
;;; of arbitrarily small norm (the hypothesis exactly as diff-on-unique states
;;; it, binders d2e_ / d2h_, so it detaches literally), a derivative is unique,
;;; so the description denotes it:
;;;   deriv-on-of-is-diff-on     IS-DIFF-ON(K, U, f, a, L) => DERIV-ON(K, U, f, a) = L
;;;   cc-deriv-on-of-is-diff-on  the same over CC-NORMED-FIELD, the hypothesis
;;;                              discharged by cc-nf-small-elements
;;; The proof: mac DERIV-ON, iota-d; the description is typed in CARR(K) off
;;; the fifth conjunct of the IS-DIFF-ON it satisfies (an IOTA is never
;;; certified defined syntactically), then diff-on-unique.
;;; NOTHING asserted.  Helper prefix: dro-.
;;; LOAD WINDOW: lo = theorem-library/holomorphic-basics (cc-nf-small-elements;
;;; the general lemma alone needs only diff-on-laws-2: diff-on-unique); hi: none.

(define (dro-small k)
  (list 'FORALL 'd2e_
    (list 'IMPLIES '(POS-RR d2e_)
      (list 'FORSOME 'd2h_
        (list 'AND (list 'IN 'd2h_ (list 'CARR k))
          (list 'AND (list 'NOT (list '= 'd2h_ (list 'ZERO k)))
                     (list '< (list (list 'FNRM k) 'd2h_) 'd2e_)))))))
(define (dro-concl k)
  (list 'FORALL 'drou_ (list 'FORALL 'drof_ (list 'FORALL 'droa_ (list 'FORALL 'drol_
    (list 'IMPLIES (list 'IS-DIFF-ON k 'drou_ 'drof_ 'droa_ 'drol_)
      (list '= (list 'DERIV-ON k 'drou_ 'drof_ 'droa_) 'drol_)))))))

(sp (make-wff
  (list 'FORALL 'drok_ (list 'IMPLIES '(IS-NORMED-FIELD drok_)
    (list 'IMPLIES (dro-small 'drok_) (dro-concl 'drok_))))))
(dk-peel!)
(define dro-pd (dk-pick (dk-head? 'IS-DIFF-ON) "the derivative"))
(define dro-k (list-ref dro-pd 1))
(define dro-u (list-ref dro-pd 2))
(define dro-f (list-ref dro-pd 3))
(define dro-a (list-ref dro-pd 4))
(define dro-l (list-ref dro-pd 5))
(define dro-uq
  (let loop ((c (dk-fact! 'diff-on-unique dro-k)))
    (if (dk-head-is? c 'IMPLIES) (loop (dk-landed-1 (lambda () (detach! c)))) c)))
;;; (IN T (CARR K)) off IS-DIFF-ON(K, U, f, a, T) in context, on a lane
(define (dro-typ! t)
  (dk-have! (list 'IN t (list 'CARR dro-k))
    (lambda ()
      (mac-h 'IS-DIFF-ON (dk-ctx-form (list 'IS-DIFF-ON dro-k dro-u dro-f dro-a t)))
      (dk-split-all!)
      (ass))))
(dro-typ! dro-l)
(mac 'DERIV-ON)
(define dro-iot (cadr (dk-goal)))
(for-each
  (lambda (leaf)
    (dk-focus! leaf)
    (if (dk-head-is? (dk-goal) 'FORSOME)
        (begin
          (ew dro-l)
          (dk-conj-close!
            (lambda ()
              (if (dk-head-is? (dk-goal) 'FORALL)
                  (begin
                    (dk-peel!)
                    (let ((y (caddr (dk-goal))))
                      (dro-typ! y)
                      (dk-apply! dro-uq dro-u dro-f dro-a dro-l y)
                      (ass)))
                  (ass)))))
        (begin
          (dro-typ! dro-iot)
          (dk-apply! dro-uq dro-u dro-f dro-a dro-iot dro-l)
          (ass))))
  (dk-opened (lambda () (iota-d dro-iot))))
(qed 'deriv-on-of-is-diff-on)

;;; the CC instance
(sp (make-wff (dro-concl 'CC-NORMED-FIELD)))
(fact 'cc-is-normed-field)
(fact 'cc-nf-small-elements)
(define dro-cc
  (let loop ((c (dk-fact! 'deriv-on-of-is-diff-on 'CC-NORMED-FIELD)))
    (if (dk-head-is? c 'IMPLIES) (loop (dk-landed-1 (lambda () (detach! c)))) c)))
(ass)
(qed 'cc-deriv-on-of-is-diff-on)
