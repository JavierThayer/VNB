;;; continuous-is-regulated.scm -- docs/calculus.pdf Ch 4, the bridge from
;;; Section 1 to the finished Section 2/3 arc.
;;;
;;;   f continuous at every point of [a,b]  ==>  f is REGULATED on [a,b]
;;;
;;; hence integrable in the notes' sense.  Definition 4.1 asks for both
;;; one-sided limits at every point of the interval; continuity supplies both,
;;; with value f(x), so with `continuous-at-right-limit' and
;;; `continuous-at-left-limit' (onesided-limits.scm, both `modulo 0') this is
;;; assembly and not an eps/delta argument.
;;;
;;; THE SHARED WORK IS DONE BEFORE THE SPLIT, and that is the whole shape of
;;; this proof.  After unfolding IS-REGULATED the goal is a CONJUNCTION
;;;
;;;   (x_ < b implies forsome l. is-right-limit(f,x_,l))
;;;     and (a < x_ implies forsome l. is-left-limit(f,x_,l))
;;;
;;; and both halves need the same three facts -- x_ in RR, f(x_) in RR, and
;;; continuity at x_.  Split first and the two leaves are independent nodes, so
;;; every one of them has to be rebuilt twice; the user drove exactly that and
;;; reported "I keep proving the same things over and over".  Land them while
;;; there is still ONE node and both children inherit them.
;;;
;;; TWO ORDERING TRAPS, both of which cost a run:
;;;
;;;   * `mac-h' REPLACES the hypothesis it unfolds.  Unfolding
;;;     `x_ in ccint(a,b)' destroys the very fact the continuity universal has
;;;     to detach against, so the `inst+' must come FIRST.
;;;   * after a `mac-h' the rewritten hypothesis is no longer the newest, so
;;;     `(car (dk-asms))' grabs the instantiation instead and `dk-split!' errors
;;;     on an atom.  Find the conjunction by SHAPE.

(sp (make-wff
  '(FORALL f (FORALL a (FORALL b
     (IMPLIES (IN f (FUN RR RR))
     (IMPLIES (IN a RR)
     (IMPLIES (IN b RR)
     (IMPLIES (< a b)
     (IMPLIES (FORALL x_ (IMPLIES (IN x_ (CCINT a b))
                                  (IS-CONTINUOUS-AT RR-MS RR-MS f x_)))
              (IS-REGULATED f a b)))))))))))

;;; Peel the hypotheses, unfold IS-REGULATED, sweep the four typing conjuncts
;;; of Definition 4.1 (all already in the context), then peel the outer
;;; `forall([x_ in ccint(a,b)], ...)' -- which is what puts `x_ in ccint(a,b)'
;;; in the context for the instantiation below.
(quietly (lambda ()
  (di) (di) (di) (di) (di) (di) (mac 'IS-REGULATED)
  (di) (focus 2) (di) (focus 3) (di) (focus 4) (di) (focus 5)
  (ass-all) (focus 1) (di)))

;;; The shared work, once.
(quietly (lambda ()
  (inst+ (let loop ((as (dk-asms)) (i 1))
           (cond ((null? as) (error "continuity universal not in context"))
                 ((and (pair? (car as)) (eq? (caar as) 'FORALL)
                       (let scan ((f (car as)))
                         (cond ((eq? f 'IS-CONTINUOUS-AT) #t)
                               ((pair? f) (or (scan (car f)) (scan (cdr f))))
                               (else #f))))
                  i)
                 (else (loop (cdr as) (+ i 1)))))
         'x_)
  (mac-h 'ccint-membership '(IN x_ (CCINT a b)))
  (dk-split! (let loop ((as (dk-asms)))
               (cond ((null? as) (error "unfolded ccint membership not found"))
                     ((and (pair? (car as)) (eq? (caar as) 'AND)
                           (equal? (cadr (car as)) '(IN x_ RR)))
                      (car as))
                     (else (loop (cdr as))))))
  (fact 'fun-apply-type-c 'f 'RR 'RR 'x_)
  ;; now split the conjunction.  Each guard is peeled on its own leaf below --
  ;; NOT with `bplus', which is defined far later in the load order than this
  ;; file and is unbound during a cold load (it worked standalone against a
  ;; full band, which is exactly how a load-order bug hides).  A library proof
  ;; should not lean on a saturating composite anyway.
  (di)))

;;; Each half: the witness continuity hands you, then the lemma.
(quietly (lambda ()
  (dk-focus! (find-first
              (lambda (n) (let scan ((f (wff-formula (sequent-node-assertion n))))
                            (cond ((eq? f 'IS-RIGHT-LIMIT) #t)
                                  ((pair? f) (or (scan (car f)) (scan (cdr f))))
                                  (else #f))))
              (proof-leaves)))
  (di)                                   ; past the guard  x_ < b
  (ew '(f x_))
  (fact 'continuous-at-right-limit 'f 'x_)
  (ass)
  (dk-focus! (car (proof-leaves)))
  (di)                                   ; past the guard  a < x_
  (ew '(f x_))
  (fact 'continuous-at-left-limit 'f 'x_)
  (ass)))

(qed 'continuous-is-regulated)
(topic! 'continuous-is-regulated 'analysis)
(alias! 'continuous-is-regulated
        "a function continuous on [a,b] is regulated there, hence integrable")
