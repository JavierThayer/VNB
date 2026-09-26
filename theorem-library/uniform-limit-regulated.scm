;;; uniform-limit-regulated.scm -- a uniform limit of regulated functions is
;;; regulated.  docs/calculus.pdf Prop 4.5, the sufficiency half.
;;;
;;; THE ARGUMENT.  To show `g' has a one-sided limit at x, do NOT construct the
;;; limit -- `cauchy-criterion-right' / `-left' reduce its existence to a
;;; CLUSTERING statement, which needs no witness:
;;;
;;;     for every eps > 0 there is delta > 0 with
;;;     |g(s) - g(t)| <= eps  for all s, t in the one-sided delta-range of x.
;;;
;;; Given eps, put h = eps/4.  Uniform convergence at h gives an index n with
;;; |g(u) - fam(n)(u)| <= h for every u in [a,b].  `fam(n)' is regulated, so it
;;; HAS a one-sided limit l at x; unfold that at h to get delta with
;;; |fam(n)(t) - l| <= h on the delta-range.  Then for s, t in that range
;;;
;;;     g(s) - g(t) = (g(s)-fam(n)(s)) + (fam(n)(s)-l)
;;;                 - (fam(n)(t)-l)    - (g(t)-fam(n)(t))
;;;
;;; and each of the four differences is within h, so the whole is within 4h=eps.
;;;
;;; FOUR terms, hence eps/4 and not eps/3: the route to fam(n)'s values at BOTH
;;; points passes through its limit l, because `is-regulated' hands over a limit
;;; and not a Cauchy property.  (`eps-part' also only subdivides by powers of
;;; two -- the library's one subdivision lemma is `rr-pos-halvable'.)
;;;
;;; TWO THINGS THE PAPER PROOF LEAVES OUT, and both are real work here:
;;;
;;; * DELTA MUST BE CAPPED.  The uniform bound holds on [a,b] only, while the
;;;   criterion's delta-range is not confined to [a,b].  So the witness is not
;;;   fam(n)'s delta but something below BOTH it and the distance from x to the
;;;   near end of the interval.  `rr-min-pos' supplies exactly that, and it is
;;;   stated as an existential, so `obtain-at' takes it in one step.
;;; * THE ESTIMATE IS LINEAR, once the absolute values are opened.
;;;   `rr-abs-bound' (`|X| <= c iff -c <= X and X <= c') turns each of the four
;;;   bounds and the goal into linear inequalities, and `g(s)-g(t)' is a linear
;;;   combination of the four differences -- so `ineq' closes it outright.  The
;;;   three nested applications of the triangle inequality that the hand proof
;;;   uses are not needed.  `rr-abs-bound' is GUARDED, so `mac-h' spawns a
;;;   typing side-condition for any argument not already typed: type the four
;;;   differences FIRST.

;;; -----------------------------------------------------------------------
;;; Helpers.  File-local, per the one-place rule: nothing outside this proof
;;; wants them.

(define (ulr--asm-find pred) (find-first pred (dk-asms)))

(define (ulr--asm-forall-mentioning str)
  (ulr--asm-find (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                  (substring? str (wff->string (make-wff a)))))))

;;; Split an AND goal down to its leaves and close each from the context.
;;; `grind' opens these and does not close them, and `prop' cannot help: the
;;; context here is far past its atom cap, so it narrows to the goal-connected
;;; assumptions and drops the conjunction it needed.
(define (ulr--close-and!)
  (let loop ((fuel 8))
    (let ((g (dk-goal)))
      (if (and (pair? g) (eq? (car g) 'AND) (> fuel 0))
          (for-each (lambda (nd)
                      (if (not (sequent-node-grounded? nd))
                          (begin (dk-focus! nd) (loop (- fuel 1)))))
                    (dk-opened (lambda () (di))))
          (ass)))))

;;; `pos-rr(x)' entails `x in rr' and `0 < x', but `in-rr' cannot read a
;;; predicate -- only a membership -- so take both out here.  Each in its own
;;; `have!' lane, because `mac-h' is destructive and the main branch still
;;; wants `pos-rr(x)' intact.
(define (ulr--pos-parts! x)
  (dk-have! (list 'IN x 'RR) (lambda () (mac-h 'pos-rr (list 'POS-RR x)) (prop)))
  (dk-have! (list '< 0 x)    (lambda () (mac '<) (mac-h 'pos-rr (list 'POS-RR x)) (prop))))

;;; Read a bound off `u in ccint(a,b)' without consuming the membership.
(define (ulr--from-ccint! u concl)
  (dk-have! concl (lambda ()
                    (mac-h 'ccint-membership (list 'IN u (list 'CCINT 'a 'b)))
                    (dk-split! (car (dk-asms)))
                    (ass))))

(define (ulr--typed! t) (dk-have! (list 'IN t 'RR) (lambda () (in-rr))))

;;; -----------------------------------------------------------------------
;;; One branch of the per-point obligation.  SIDE is 'right or 'left; the two
;;; differ only in the criterion cited, the guard already assumed, which end of
;;; the interval the cap measures to, and how a point of the delta-range is
;;; bracketed.  Everything between is the same argument.
(define (ulr--branch! side)
  (let* ((right? (eq? side 'right))
         (crit   (if right? 'cauchy-criterion-right 'cauchy-criterion-left))
         (limpr  (if right? 'IS-RIGHT-LIMIT 'IS-LEFT-LIMIT))
         (gap    (if right? (list '- 'b 'x_) (list '- 'x_ 'a))))

    ;; reduce "a one-sided limit exists" to the clustering statement
    (dk-have! '(IN x_ RR) (lambda () (in-rr)))
    (bc* crit)
    (ass-all)
    (dk-focus! (or (find-first (lambda (nd)
                                 (let ((q (wff-formula (sequent-node-assertion nd))))
                                   (and (pair? q) (eq? (car q) 'FORALL))))
                               (proof-open-leaves *ps*))
                   (error "ulr: no clustering leaf")))
    ;; `forall eps. pos-rr(eps) => ...' is an UNGUARDED universal: the first di
    ;; peels the quantifier and lands nothing, the second lands the guard.
    (di) (di)

    (let* ((h    (eps-part 'eps_ 4))
           (unif (ulr--asm-forall-mentioning "forsome([n_ in nn]"))
           (n    (obtain-at unif h))
           ;; take k := n; the guard is a CONJUNCTION, which `inst+' will not
           ;; split for itself, and `n <= n' is true but is not an assumption
           (ubound (car (use-at (ulr--asm-find
                                 (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                  (eq? (cadr a) 'k_))))
                                n (lambda () (fact 'nn-le-refl n) (prop)))))
           (reg  (car (use-at (ulr--asm-forall-mentioning "is-regulated") n))))

      ;; fam(n) is regulated, so it has the one-sided limit l at x_
      (mac-h 'is-regulated reg)
      (let* ((regparts (dk-split! (car (dk-asms))))
             (perpoint (find-first (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)))
                                   regparts))
             (halves   (dk-split! (car (use-at perpoint 'x_))))
             (limimp   (find-first (lambda (a)
                                     (and (pair? a) (eq? (car a) 'IMPLIES)
                                          (pair? (caddr a))
                                          (eq? (car (caddr a)) 'FORSOME)
                                          (eq? (car (caddr (caddr a))) limpr)))
                                   halves))
             (l        (obtain-at limimp)))

        ;; unfold that limit at h to get fam(n)'s delta
        (mac-h limpr (list limpr (list 'FAM n) 'x_ l))
        (let* ((lparts (dk-split! (car (dk-asms))))
               (epsuniv (find-first (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)))
                                    lparts))
               (d      (obtain-at epsuniv h))
               (tbound (find-first (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                    (eq? (cadr a) 't_)
                                                    (memq d (free-vars a))))
                                   (dk-asms))))

          ;; THE CAP: a positive w below both fam(n)'s delta and the distance
          ;; from x_ to the near end of [a,b].
          (ulr--pos-parts! d)
          (if right?
              (begin (use-at 'rr-sub-in-rr 'b 'x_) (use-at 'rr-lt-diff-pos 'x_ 'b))
              (begin (use-at 'rr-sub-in-rr 'x_ 'a) (use-at 'rr-lt-diff-pos 'a 'x_)))
          (let ((w (obtain-at 'rr-min-pos d gap)))
            (use-at 'rr-pos-rr-of-lt w)
            (ew w)
            (di)                          ; pos-rr(w) | the two-point statement
            (ass-all)
            (dk-focus! (or (find-first (lambda (nd)
                                         (let ((q (wff-formula (sequent-node-assertion nd))))
                                           (and (pair? q) (eq? (car q) 'FORALL)
                                                (eq? (cadr q) 's_))))
                                       (proof-open-leaves *ps*))
                           (error "ulr: no two-point leaf")))
            (di) (di) (dk-split! (car (dk-asms)))
            (di)     (dk-split! (car (dk-asms)))
            (ulr--from-ccint! 'x_ '(<= a x_))
            (ulr--from-ccint! 'x_ '(<= x_ b))

            ;; everything the estimate needs about one of the two points
            (let ((point!
                   (lambda (u)
                     (if right?
                         (begin
                           (dk-have! (list '<= 'a u)
                                     (lambda () (ineq-on! '(<= a x_) (list '< 'x_ u))))
                           (dk-have! (list '<= u 'b)
                                     (lambda () (ineq-on! (list '<= u (list '+ 'x_ w))
                                                          (list '<= w gap)))))
                         (begin
                           (dk-have! (list '<= 'a u)
                                     (lambda () (ineq-on! (list '<= (list '- 'x_ w) u)
                                                          (list '<= w gap))))
                           (dk-have! (list '<= u 'b)
                                     (lambda () (ineq-on! (list '< u 'x_) '(<= x_ b))))))
                     (dk-have! (list 'IN u (list 'CCINT 'a 'b))
                               (lambda () (mac 'ccint-membership) (ulr--close-and!)))
                     (use-at ubound u)
                     (if right?
                         (dk-have! (list '<= u (list '+ 'x_ d))
                                   (lambda () (ineq-on! (list '<= u (list '+ 'x_ w))
                                                        (list '<= w d))))
                         (dk-have! (list '<= (list '- 'x_ d) u)
                                   (lambda () (ineq-on! (list '<= (list '- 'x_ w) u)
                                                        (list '<= w d)))))
                     (use-at tbound u (lambda () (ulr--close-and!))))))
              (point! 's_)
              (point! 't_))

            ;; THE ESTIMATE.  Type every atom the oracle will meet, open the
            ;; absolute values, and let Fourier-Motzkin do the arithmetic.
            (ulr--pos-parts! 'eps_)
            (ulr--pos-parts! h)
            (for-each ulr--typed!
                      (list '(g s_) '(g t_)
                            (list (list 'FAM n) 's_) (list (list 'FAM n) 't_)
                            (list '- '(g s_) '(g t_))
                            (list '- '(g s_) (list (list 'FAM n) 's_))
                            (list '- (list (list 'FAM n) 's_) l)
                            (list '- '(g t_) (list (list 'FAM n) 't_))
                            (list '- (list (list 'FAM n) 't_) l)))
            (for-each (lambda (f)
                        (mac-h 'rr-abs-bound f)
                        (dk-split! (car (dk-asms))))
                      (filter (lambda (a) (and (pair? a) (eq? (car a) '<=)
                                               (pair? (cadr a))
                                               (eq? (car (cadr a)) 'ABS)))
                              (dk-asms)))
            (mac 'rr-abs-bound)
            (for-each (lambda (nd)
                        (if (not (sequent-node-grounded? nd))
                            (begin (dk-focus! nd) (ineq!))))
                      (dk-opened (lambda () (di))))))))))

;;; -----------------------------------------------------------------------

(sp (make-wff (parse-string "forall([fam, g, a, b], is-unif-limit-on(fam, g, a, b) implies (forall([k_ in nn], is-regulated(fam(k_), a, b))) implies is-regulated(g, a, b))")))

(quietly (lambda ()
  (di) (di) (di)
  (mac-h 'is-unif-limit-on '(IS-UNIF-LIMIT-ON fam g a b))
  (dk-split! (car (dk-asms)))
  (mac 'is-regulated)
  (let split ((k 0))
    (let ((nd (find-first (lambda (nd)
                            (let ((q (wff-formula (sequent-node-assertion nd))))
                              (and (pair? q) (eq? (car q) 'AND))))
                          (proof-leaves))))
      (if (and nd (< k 8)) (begin (dk-focus! nd) (di) (split (+ k 1))))))
  (ass-all)
  ;; the per-point obligation, then its two halves
  (dk-focus! (or (find-first (lambda (nd)
                               (let ((q (wff-formula (sequent-node-assertion nd))))
                                 (and (pair? q) (eq? (car q) 'FORALL))))
                             (proof-leaves))
                 (error "ulr: no per-point leaf")))
  (di) (di)

  (for-each
   (lambda (side)
     (let ((nd (find-first
                (lambda (nd)
                  (let ((q (wff-formula (sequent-node-assertion nd))))
                    (and (pair? q) (eq? (car q) 'IMPLIES)
                         (equal? (cadr q)
                                 (if (eq? side 'right) '(< x_ b) '(< a x_))))))
                (proof-open-leaves *ps*))))
       (if (not nd) (error "ulr: no branch leaf for" side))
       (dk-focus! nd)
       (di)
       (ulr--branch! side)))
   '(right left))))

(qed 'uniform-limit-of-regulated)
(topic! 'uniform-limit-of-regulated 'analysis)
