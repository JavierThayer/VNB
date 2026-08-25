;;; ccint-basics.scm -- CCINT's membership law, PROVEN from its definition.
;;;
;;;     ccint-membership:  x in CCINT(a,b)  iff  x in RR and a <= x and x <= b
;;;
;;; CCINT(a,b) = SEP(x in RR | a <= x and x <= b) is a def-functoid
;;; (theorem-library/extreme-value.scm), so this is separation and nothing else.
;;; It stood there as an `add-to-pss' support carrying a `proof' warrant whose
;;; text WAS the derivation -- "Separation: x in CCINT(a,b) = SEP(x in RR |
;;; a<=x and x<=b) iff x in RR and a<=x and x<=b, by the SEP membership kernel
;;; rule" -- i.e. a proof written in prose and then not run.  That species of
;;; comment is the same failure as an unloaded proof file, one line long.
;;;
;;; WHY IT IS WORTH THE FILE.  Every consumer of the closed interval reads its
;;; members through this law: rolle-proof, interior-extremum-proof,
;;; deriv-constant-proof, deriv-monotone-proof and ivt-proof all `mac' or
;;; `mac-h' it.  As an assertion it was the leaf that kept those bills off
;;; `modulo 0'; as a theorem it contributes nothing to any of them.
;;;
;;; WHY IT IS SHORTER THAN interval-basics.scm.  That file could not unfold
;;; INTERVAL in an ASSUMPTION (`mac-h' cannot touch a def-functoid) and so had
;;; to mint a citable unfolding equation first.  Here the unfold happens in the
;;; GOAL -- the statement IS the membership law -- so one `mac CCINT' puts the
;;; SEP in place and the two kernel rules `sep-me' / `sep-mi' close the two
;;; directions.  No new axiom, no unfolding equation.
;;;
;;; Loads immediately after extreme-value.scm (which defines CCINT) and before
;;; every file that cites the law.

;;; ---- file-local driver helpers (the `cb-' prefix) --------------------
(define (cb-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; `ai' every conjunction in the context, to exhaustion.  Both directions need
;;; it: `from-context!' closes an AND goal conjunct by conjunct, so a hypothesis
;;; that is still an AND matches none of them.
(define (cb-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 10)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (cb-mem-in set-expr)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cb-mem-in: no context membership in" set-expr))
          ((and (pair? (car l)) (eq? (caar l) 'IN) (equal? (caddr (car l)) set-expr))
           (car l))
          (else (loop (cdr l))))))

(define cb-sep '(SEP x RR (AND (<= a x) (<= x b))))

(sp (make-wff '(FORALL a (FORALL b (FORALL x
   (IFF (IN x (CCINT a b))
        (AND (IN x RR) (AND (<= a x) (<= x b)))))))))
(cb-peel!)
(mac 'CCINT)                      ; the goal now speaks of the separation itself
(for-each
 (lambda (k)
   (dk-focus! k)
   (if (eq? (car (dk-goal)) 'AND)
       ;; forward: read the two halves off the membership
       (begin (sep-me (cb-mem-in cb-sep)) (cb-split!) (from-context!))
       ;; backward: the two halves are the separation's two obligations
       (begin (cb-split!)
              (for-each (lambda (j) (dk-focus! j) (from-context!))
                        (dk-opened (lambda () (sep-mi)))))))
 (dk-opened (lambda () (di))))
(qed 'ccint-membership)
(topic! 'ccint-membership 'topology)
