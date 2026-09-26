;;; bijection-identity-proof.scm -- the identity lambda on a SET is a bijection.
;;;
;;;   bijection-identity   forall X. X in SET => (VNB-LAMBDA x_ X x_) in BIJECTION(X,X)
;;;
;;; Statement verbatim from structure-library/bijection.scm (the `add-axiom!'
;;; retired by this file), guard included.  The guard is load-bearing: unguarded, at
;;; X := ORD the axiom put the identity LAMBDOID on a proper class into FUN(ORD,ORD),
;;; which is exactly what pi-lambda-type!'s (IN A SET) obligation exists to prevent
;;; (bijection.scm's own note, 2026-08-05).  Here the guard is what CLOSES the
;;; sethood leaf `lam-t' opens, so the proof is only possible in the guarded form.
;;;
;;; PLAN -- the warrant's three steps, each a kernel rule and nothing else:
;;;   * `mac' the defining iff (bijection-membership-iff, `definitional') BACKWARD
;;;     on the goal, leaving the three conjuncts;
;;;   * FUN(X,X): `dk-lam-fun!' -- lam-t, sethood from the guard (dk-set-close!
;;;     falls through to `ass' for a variable domain), pointwise typing is the
;;;     peeled (IN x_ X) itself;
;;;   * INJECTIVITY: peel to (= a b) with ((\x.x) a) = ((\x.x) b) in context, and
;;;     `lam-b-h' reduces BOTH redexes in one call (reduce-lambda-in-expr walks the
;;;     whole assumption), leaving (= a b) in context;
;;;   * SURJECTIVITY: witness z := w (read off the equation of the FORSOME body,
;;;     never guessed), then (IN w X) by `ass' and ((\x.x) w) = w by `lam-b' + `rfl'
;;;     -- rfl's definedness guard is met by (IN w X) in context.
;;;
;;; No citation but the defining iff, so the bill is `modulo 0'.
;;;
;;; LOAD WINDOW [lo, hi):
;;;   lo -- after structure-library/bijection (bijection-membership-iff, BIJECTION)
;;;         and, as any proof file, after interactive / proof-debt / driver-kit.
;;;   hi -- before theorem-library/card-defined, the only citer
;;;         (card-defined.scm:147, `(fact 'bijection-identity '(ORD-SEGMENT n_))').
;;;   Suggested slot: immediately after structure-library/bijection-derived.
;;;
;;; Helper prefix: bid-.

;;; ---- helpers ----------------------------------------------------------

;; The finish: report open goals loudly rather than qed a half-proof.
(define (bid-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** bijection-identity-proof: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (sequent-node-assertion l)))
                    (newline)
                    (for-each (lambda (a)
                                (display "      asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "bijection-identity-proof: unfinished" name))))

;; injectivity, once peeled: the context holds (= (phi a) (phi b)) with phi the
;; identity lambda.  Cite the assumption FROM the context (a reconstruction
;; matches nothing and no-ops), beta-reduce it, and the goal is that assumption.
(define (bid-inj!)
  (let ((h (dk-pick (lambda (f)
                      (and (pair? f) (eq? (car f) '=)
                           (pair? (cadr f)) (pair? (car (cadr f)))
                           (eq? (car (car (cadr f))) 'VNB-LAMBDA)))
                    "the applied-lambda equation")))
    (lam-b-h h)
    (ass)))

;; one leaf of the surjectivity conjunction: (IN w X) from context, or the
;; beta-equation (phi w) = w.
(define (bid-surj-leaf!)
  (if (eq? (car (dk-goal)) '=)
      (begin (lam-b) (rfl))
      (ass)))

;; surjectivity, once peeled: goal (FORSOME z (AND (IN z X) (= (phi z) w))).
;; The witness is w -- read off the equation, not guessed from the binder.
(define (bid-surj!)
  (let* ((g    (dk-goal))
         (body (caddr g))
         (w    (caddr (caddr body))))
    (ew w)
    (dk-conj-close! bid-surj-leaf!)))

;; Split the unfolded iff and dispatch.  The two universal conjuncts share head,
;; binder shape and everything else a shape match could see, so they are told
;; apart by what is left AFTER the peel: an equation (injectivity) or an
;; existential (surjectivity).
(define (bid-drive!)
  (let ((g (dk-goal)))
    (cond
      ((eq? (car g) 'AND)
       (for-each (lambda (l) (dk-focus! l) (bid-drive!))
                 (dk-opened (lambda () (di)))))
      ((eq? (car g) 'IN) (dk-lam-fun!))
      ((eq? (car g) 'FORALL)
       (dk-peel!)
       (let ((h (dk-goal)))
         (cond ((eq? (car h) 'FORSOME) (bid-surj!))
               ((eq? (car h) '=)       (bid-inj!))
               (#t (error "bijection-identity: peeled to neither an equation nor an existential"
                          (expression->string h))))))
      (#t (error "bijection-identity: unexpected conjunct"
                 (expression->string g))))))

;;; ---- bijection-identity -----------------------------------------------

(sp (make-wff '(FORALL X
                 (IMPLIES (IN X SET)
                          (IN (VNB-LAMBDA x_ X x_) (BIJECTION X X))))))
(dk-peel!)                                     ; X, and (IN X SET)
(mac 'bijection-membership-iff)
(bid-drive!)
(bid-qed! 'bijection-identity)
(topic! 'bijection-identity 'constructions)
