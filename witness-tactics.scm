;;; witness-tactics.scm -- getting a witness out of a quantified hypothesis.
;;;
;;; WHY THIS FILE EXISTS.  Analysis is written in the shape
;;;
;;;     forall x. GUARD(x) => forsome y. BODY(x, y)
;;;
;;; -- "for every epsilon there is an index / a delta / a point" -- and the
;;; whole of an eps-delta argument is: pick the x, get the y, use the body.
;;; VNB had no tactic for that.  Doing it by hand is five steps, and a user
;;; driving `uniform-limit-of-regulated' on 2026-09-10 got lost in exactly
;;; those five, asking "Given an eps I can find a k_ s.t. BLAH.  How do I get
;;; that k_?".  The five, and what each one can do to you:
;;;
;;;   (inst+ h t)     -- instantiates, and auto-detaches an antecedent already
;;;                      in context.  It will NOT split a CONJUNCTIVE one, so
;;;                      on `(k in nn and n <= k) => ...' it lands the
;;;                      implication and stops, looking exactly like success.
;;;   (dk-have! ANT)  -- the conjunction, whole, to unblock that.
;;;   (detach! imp)   -- takes the IMPLICATION, never the antecedent; handed
;;;                      the antecedent it is a silent no-op.
;;;   (ai ex)         -- skolemizes, but only a TOP-LEVEL forsome.  The one
;;;                      inside `forall eps. pos-rr(eps) => forsome n. ...' is
;;;                      not reachable: `ai' declines with "cannot decompose",
;;;                      because the assumption's head is FORALL.
;;;   (dk-split! ...) -- a GUARDED existential lands as one conjunction
;;;                      `(y in S) and BODY'; the parts are wanted separately.
;;;
;;; and then the eigenvariable has to be read off the context by difference,
;;; because it is minted with a counter-generated name nobody can predict.
;;;
;;; None of that is mathematics.  It is the same five steps every time, and
;;; four of the five fail SILENTLY when they fail.
;;;
;;; TRUST.  These are composites: they drive the ordinary surface tactics and
;;; nothing else, so a `qed' over a proof using them bills exactly what the
;;; expansion bills, and the recorded script is the step-by-step proof rather
;;; than a line naming the composite.  Same contract as `prop' and `contra'.
;;;
;;; NOT `obtain' (sketch.scm).  That one takes a LANE -- a thunk it runs and
;;; diffs around -- so an existential already sitting in the context is
;;; invisible to it, and it runs the lane under `vnb-guard', which turns an
;;; error inside into "nothing obtained".  It answers a different question.

;;; -----------------------------------------------------------------------
;;; Shared machinery.

(define (wt--forsome? f) (and (pair? f) (eq? (car f) 'FORSOME)))
(define (wt--implies? f) (and (pair? f) (eq? (car f) 'IMPLIES)))

;;; The variables free in LANDED that were not free in BEFORE, in order.
(define (wt--fresh-in landed before)
  (let loop ((gs landed) (acc '()))
    (if (null? gs)
        acc
        (loop (cdr gs)
              (append acc (filter (lambda (v) (and (not (memq v before))
                                                   (not (memq v acc))))
                                  (free-vars (car gs))))))))

;;; Skolemize the top-level FORSOME F (an assumption), split what lands, and
;;; return the eigenvariable `ai' minted.  Reading the name off by DIFFERENCE
;;; is not a convenience: `fresh-var' names it `<hint>_<n>' with n a monotone
;;; global counter, so no caller can predict it and no caller should try.
(define (wt--skolemize! f)
  (let* ((before (free-vars f))
         (landed (dk-split! f))
         (new    (wt--fresh-in landed before)))
    (if (null? new)
        (error "witness: ai landed no fresh variable -- not an existential?" f)
        (car new))))

;;; Discharge IMP's antecedent and detach.  `dk-have!' takes the antecedent
;;; WHOLE, conjunction and all, which is the step `inst+' cannot do for itself.
;;;
;;; PROVER is #f to read the antecedent off the context (`dk-have!'s default),
;;; or a thunk that proves it.  The thunk is not a nicety: the commonest guard
;;; in the tree is `(n in NN) and (n <= n)', whose second half is TRUE but is
;;; not an assumption -- it wants `nn-le-refl' -- so with no way to say that,
;;; the tactic would decline on the single most ordinary case there is.
(define (wt--discharge! imp prover)
  (if prover (dk-have! (cadr imp) prover) (dk-have! (cadr imp)))
  (dk-landed (lambda () (detach! imp))))

;;; Instantiate: a SYMBOL is a theorem name (cite it), anything else is a
;;; hypothesis (instantiate it in place).
;;; With NO terms there is nothing to instantiate: the hypothesis is already
;;; the implication or the existential we want, so hand it back untouched.
;;; `(obtain-at h)' is then "discharge and skolemize what is already here",
;;; which is the shape a conjunct split out of a definition arrives in.
(define (wt--instantiate! f ts)
  (if (null? ts)
      (list f)
      (dk-landed (lambda () (if (symbol? f) (apply fact f ts) (apply inst+ f ts))))))

;;; A trailing PROCEDURE in the argument list is the guard's prover, never a
;;; term -- terms are S-expressions and are never procedures, so the two cannot
;;; be confused.  Returns (terms . prover).
(define (wt--split-args ts)
  (if (and (pair? ts) (procedure? (car (last-pair ts))))
      (cons (except-last-pair ts) (car (last-pair ts)))
      (cons ts #f)))

;;; -----------------------------------------------------------------------
;;; (obtain-at h t ...) -- instantiate and skolemize, in one move.
;;;
;;; H is a hypothesis (formula or 1-based index) or a THEOREM NAME; it must
;;; have the shape `forall x... . GUARD => forsome y. BODY' with the guard
;;; optional.  Instantiates at the terms, discharges the guard if one is in
;;; the way, skolemizes the existential and splits the body into its conjuncts.
;;;
;;; A trailing PROCEDURE is the guard's prover, for a guard the context does
;;; not already hold -- `(use-at h t (lambda () (fact 'nn-le-refl t) (prop)))'.
;;;
;;; RETURNS THE EIGENVARIABLE, which is the point: the caller needs the name to
;;; go on with, and it cannot be predicted.  Everything the body says about it
;;; is now in the context as separate assumptions.
(define (obtain-at h . ts0)
  (let* ((split  (wt--split-args ts0))
         (ts     (car split))
         (prover (cdr split))
         (f      (->raw-formula/idx h))
         (landed (wt--instantiate! f ts))
         (ex     (find-first wt--forsome? landed)))
    (cond
      (ex (wt--skolemize! ex))
      ((find-first (lambda (g) (and (wt--implies? g) (wt--forsome? (caddr g)))) landed)
       => (lambda (imp)
            (let ((ex2 (find-first wt--forsome? (wt--discharge! imp prover))))
              (if ex2
                  (wt--skolemize! ex2)
                  (error "obtain-at: detached, but no existential appeared" imp)))))
      (else
       (error "obtain-at: instantiating produced no existential -- use `use-at' if the conclusion is not one" f)))))

;;; -----------------------------------------------------------------------
;;; (use-at h t ...) -- the same, where the conclusion is NOT an existential.
;;;
;;; Instantiate, discharge the antecedent (conjunctive or not), split what
;;; lands.  Returns the landed facts.  This is the half of the dance that bites
;;; hardest, because `inst+' handles the simple antecedent silently and the
;;; conjunctive one silently too -- differently.
(define (use-at h . ts0)
  (let* ((split  (wt--split-args ts0))
         (ts     (car split))
         (prover (cdr split))
         (f      (->raw-formula/idx h))
         (landed (wt--instantiate! f ts))
         (imp    (find-first wt--implies? landed)))
    ;; `inst+' and `fact' auto-detach an antecedent ALREADY in context, so the
    ;; implication may be landed and spent at the same time.  Detaching it again
    ;; is a no-op, and `dk-landed' -- rightly -- calls a no-op an error.  So ask
    ;; whether the consequent is already here before reaching for the guard.
    (cond ((not imp) landed)
          ((dk-asm? (caddr imp))
           (filter (lambda (g) (not (wt--implies? g))) landed))
          (else (wt--discharge! imp prover)))))

;;; -----------------------------------------------------------------------
;;; (eps-part e k) -- "let h be e/k", the move every eps-delta proof opens with.
;;;
;;; Lands `pos-rr(h)' and the equation summing K copies of h to E, and returns
;;; h.  Requires `pos-rr(e)' in context.
;;;
;;; K MUST BE A POWER OF TWO, and the restriction is the tree's, not a
;;; shortcut: the only subdivision lemma in the library is `rr-pos-halvable'
;;; (`forall eps. pos-rr(eps) => forsome d. pos-rr(d) and d + d = eps'), so
;;; halves are what is cheap and thirds are not available at all.  Worth
;;; knowing before choosing the shape of an estimate: an eps/3 argument will
;;; fight the lemma stock, an eps/4 argument will not.
;;;
;;; The summed equation is built nested-binary -- 4 gives `(h + h) + (h + h)',
;;; never the flat `h + h + h + h'.  A flat n-ary node is a DIFFERENT
;;; S-expression that only the `nary-plus-*' axioms interpret, and it would not
;;; be `equal?' to what a later `ass' reconstructs.
(define (wt--sum h k)
  (if (= k 1) h (let ((half (wt--sum h (quotient k 2)))) (list '+ half half))))

(define (eps-part e k)
  (if (not (and (exact-nonnegative-integer? k) (> k 0)
                (= 0 (bitwise-and k (- k 1)))))
      (error "eps-part: k must be a power of two -- the library has rr-pos-halvable and no thirds" k))
  (let loop ((cur e) (n k) (eqs '()))
    (if (= n 1)
        (begin
          ;; chain the halving equations, innermost first, back up to E
          ;; Substitute the INNER halving equations only, innermost first.
          ;; The outermost one -- `h1 + h1 = e' -- is the assumption `ass' then
          ;; closes against; substituting it too would leave `e = e', which is
          ;; a definedness claim and not in the context.
          (if (pair? eqs)
              (let ((target (list '= (wt--sum cur k) e)))
                (if (not (dk-asm? target))
                    (dk-have! target
                              (lambda ()
                                (for-each subst (except-last-pair eqs))
                                (ass))))))
          cur)
        (let* ((h  (obtain-at 'rr-pos-halvable cur))
               (eq (list '= (list '+ h h) cur)))
          (loop h (quotient n 2) (cons eq eqs))))))
