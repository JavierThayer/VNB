;;; functor-invariance.scm -- a construction that cannot see the functor.
;;;
;;;     PREIMAGE(s, f, V)  =  { z in PTS(s) : f(z) in V }
;;;
;;; reads its structure argument ONLY through PTS.  And METRIC-TOP carries PTS
;;; across on the nose: PTS(METRIC-TOP r) is PTS(r) -- a metric space and its
;;; topology have the same points.  So, for EVERY r, both sides of
;;;
;;;     PREIMAGE(METRIC-TOP r, f, V)  ==  PREIMAGE(r, f, V)
;;;
;;; unfold to the same separation, and the functor is invisible to the preimage.
;;;
;;; That is not naturality -- there is no map and no square, and nothing commutes
;;; that could fail to.  It is the syntactic shadow of a STRICT commuting triangle:
;;; on the slots it carries on the nose the functor IS the identity, so anything
;;; defined through those slots and nothing else cannot tell it was applied.
;;;
;;; WHY `=='  AND NOT `='.  VNB's `=' is partial: t = t IS the definedness claim.
;;; An unconditional (= (PREIMAGE (METRIC-TOP r) f V) (PREIMAGE r f V)) would
;;; therefore assert that both preimages are DEFINED for every r whatsoever --
;;; including an r that is no metric space at all -- and would need a guard, and a
;;; sethood argument, to be honest.  `==' claims exactly what is true: the same
;;; thing, defined or not.  It is unconditional, and `qrfl' closes it on alpha-
;;; equivalence with no definedness obligation.  `macete-equivalence?' accepts
;;; `==', so the theorem is a REWRITE by name, usable with mac / mac-h.
;;;
;;; NOTHING IS ASSERTED.  Each equation is PROVED, by the same three moves every
;;; time -- unfold the functoid, project the accessors, qrfl -- and installed as a
;;; theorem, modulo 0.  A pair whose canned proof does not close is REPORTED, not
;;; warranted: the machine may generate statements freely, it may not assert them.
;;;
;;; Loads LAST (with functoriality.scm), because it needs every functor and
;;; functoid declared and the tactic layer present.

;;; --- which accessors of its structure parameter does a functoid READ? -------
;;; Scans the body for (ACC p) with p the functoid's FIRST parameter and ACC a
;;; registered accessor.  #f if it touches p in any other way (passes it whole to
;;; something else, say), because then the functor is NOT invisible to it and the
;;; whole argument collapses.

(define (fni--accessors-read name)
  (let ((entry (hash-table-ref/default *functoid-registry* name #f)))
    (and entry
         (let* ((params (car entry))
                (body   (cadr entry)))
           (and (pair? params)
                (let ((p    (car params))
                      (accs '())
                      (bare #f))
                  (let walk ((e body))
                    (cond
                      ((eq? e p) (set! bare #t))    ; p used other than under an accessor
                      ((pair? e)
                       (if (and (symbol? (car e))
                                (eq? (constant-head? (car e)) 'accessor)
                                (pair? (cdr e)) (null? (cddr e))
                                (eq? (cadr e) p))
                           (if (not (memq (car e) accs))
                               (set! accs (cons (car e) accs)))
                           (begin (for-each walk (cdr e))
                                  (if (pair? (car e)) (walk (car e))))))
                      (else #f)))
                  (and (not bare) (pair? accs) (reverse accs))))))))

;;; --- the qualifying pairs ---------------------------------------------------
;;; F qualifies for G when every accessor F reads is one G carries on the nose.

(define (fni--qualifies? fname gname)
  (let ((reads (fni--accessors-read fname))
        (nose  (functor-nose-accessors gname)))
    (and reads nose
         (every (lambda (a) (memq a nose)) reads)
         reads)))

(define (fni--statement fname gname)
  (let* ((entry  (hash-table-ref/default *functoid-registry* fname #f))
         (params (car entry))
         (r      (car params))
         (rest   (cdr params)))
    ;; FORALL r, x... :  F(G r, x...) == F(r, x...)
    (fold-right (lambda (v f) `(FORALL ,v ,f))
                `(== (,fname (,gname ,r) ,@rest)
                     (,fname ,r ,@rest))
                params)))

;;; --- the canned proof: unfold, project, qrfl --------------------------------
;;; The SAME three moves for every pair -- which is exactly what the qualifying
;;; condition buys.  Unfolding F rewrites BOTH sides (a macete rewrites every
;;; occurrence, and here that is what we want); `slot' then projects the functor
;;; away on the left, where it is the only thing standing between the two.

(define (fni--prove! fname gname accs)
  (let ((nm (symbol-append gname '@ fname)))
    (and (not (hash-table-ref/default *theorem-table* nm #f))
         (begin
           (sp (make-wff (fni--statement fname gname)))
           (let peel ((n (length (car (hash-table-ref/default
                                        *functoid-registry* fname '(()))))))
             (unless (= n 0) (quietly (lambda () (di))) (peel (- n 1))))
           (quietly (lambda () (mac fname)))
           (for-each (lambda (a) (quietly (lambda () (slot a)))) accs)
           (quietly (lambda () (qrfl)))
           (and (null? (dg-ungrounded-nodes (proof-state-dg *ps*)))
                (begin (quietly (lambda () (qed nm))) nm))))))

;;; --- the sweep --------------------------------------------------------------

(define *functor-invariance-owed* '())

(define (prove-functor-invariance!)
  (let ((proved '()) (failed '()))
    (for-each
      (lambda (gname)
        (for-each
          (lambda (fname)
            (let ((accs (fni--qualifies? fname gname)))
              (when accs
                (if (fni--prove! fname gname accs)
                    (set! proved (cons (symbol-append gname '@ fname) proved))
                    (set! failed (cons (list gname fname) failed))))))
          (sort (hash-table-keys *functoid-registry*)
                (lambda (a b) (string<? (symbol->string a) (symbol->string b))))))
      (functor-names))
    (set! *functor-invariance-owed* (reverse failed))
    (display ";; functor invariance: ") (display (length proved))
    (display " equation(s) PROVED (modulo 0): ") (display (reverse proved))
    (when (pair? failed)
      ;; NOT warranted, NOT asserted -- owed, and said out loud.
      (display "\n;;   ") (display (length failed))
      (display " pair(s) qualify but the canned proof did not close (OWED, not asserted): ")
      (display (reverse failed)))
    (newline)
    (list (reverse proved) (reverse failed))))

(prove-functor-invariance!)
