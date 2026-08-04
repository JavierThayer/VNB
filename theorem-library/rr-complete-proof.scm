;;; rr-complete-proof.scm -- RR is a COMPLETE METRIC SPACE.  Proven 2026-08-01/02.
;;;
;;;     IS-COMPLETE(RR-MS)
;;;
;;; This was an asserted axiom (structure-library/numeric-instances.scm), whose
;;; own comment said "the bespoke rr-complete the earlier design deferred is
;;; exactly IS-COMPLETE(RR-MS)".  It could not be proved before 2026-08-01,
;;; because RR was axiomatised as an ordered field with NO completeness axiom of
;;; any kind; `rr-sup-in' / `-upper' / `-least' were added that day and this is
;;; their first real consumer.
;;;
;;; THE ROUTE, and why this one.  Let
;;;
;;;     A = { x in RR : forsome N in NN. forall n >= N.  x <= f(n) }
;;;
;;; the eventual lower bounds of the Cauchy sequence f, and take L = SUP(A).
;;;
;;;   1. A is inhabited      Cauchy at eps = 1 gives a threshold N; then
;;;                          f(N) - 1 <= f(n) for every n >= N.
;;;   2. A is bounded above  by f(N) + 1: for x in A with witness m, take c above
;;;                          both N and m (nn-pair-upper-bound, NN is directed);
;;;                          then x <= f(c) <= f(N) + 1.
;;;   3. L = SUP(A)          exists by rr-sup-in; rr-sup-upper and rr-sup-least
;;;                          give the two comparisons used in step 4.
;;;   4. f -> L              given eps, halve it (rr-pos-halvable) to d and take
;;;                          the Cauchy threshold N2 at d.  Then f(N2)-d is in A
;;;                          so f(N2)-d <= L, and f(N2)+d is an upper bound of A
;;;                          so L <= f(N2)+d.  For n >= N2, |f(n)-f(N2)| <= d,
;;;                          and d + d = eps closes it.
;;;
;;; The textbook proof usually goes through Bolzano-Weierstrass or a monotone
;;; subsequence.  Both were rejected deliberately: a subsequence would drag in
;;; STRICTLY-MONO-NN and the diagonalization machinery, and the "Cauchy implies
;;; bounded" step wants a maximum over an initial segment, for which this library
;;; has no lemma.  The eventual-lower-bounds route needs neither -- its only
;;; NN-side fact is directedness.
;;;
;;; ALL FIVE inequalities are closed by `ineq', the Fourier-Motzkin/Farkas
;;; oracle, each in one call: step 1 ((h1)(goal)), step 2 ((h14)(goal)(h2)),
;;; step 4's membership ((h1)(goal)), and the two halves of the final bound
;;; ((h23)(goal)(h46)(h8)) and ((h9)(goal)(h30)(h46)).  The driver's real work is
;;; therefore not the arithmetic but the TYPING: `ineq' certifies an atom as real
;;; only by a LITERAL (IN t RR) in context -- (IN k NN) does not count, it does no
;;; subtype reasoning -- which is why fun-apply-type-c and rr-sub-in-rr are cited
;;; as often as they are.
;;;
;;; The distance is brought to the surface by `rr-ms-dist' as a MACETE, never by
;;; subst: the accessor sits in OPERATOR position, where subst's Leibniz walk
;;; cannot reach.  `rr-abs-bound' is an IFF, so it serves both directions -- on a
;;; hypothesis it unpacks |x| <= c into two linear bounds, and on the GOAL it
;;; turns one abs goal into two linear ones.  Each use opens a typing side-goal
;;; from its guard, discharged by rr-sub-in-rr.
;;;
;;; This file was DERIVED mechanically from the probe driver that found the
;;; proof (a paren-aware strip of its probe/dump scaffolding), then re-verified
;;; to close with zero open leaves -- not retyped, because 190-odd tactic calls
;;; transcribed by hand is a silent-error machine.
;;;
;;; Loads after interactive/proof-debt (sp/di/mac/fact/ew/have!/detach!/qed) and
;;; driver-kit, and before theorem-library/ascoli-bridge, which declares
;;; (rests-on 'unif-cauchy-cont-implies-uniform-limit '(rr-complete)).

;; ---- file-local helpers (rc- prefix; never named like a tactic) -----------
;; Each exists ONLY to work around a tactic weakness, and each should disappear
;; when that weakness is fixed rather than be promoted anywhere:
;;
;;   rc-focus-exact  `ass' hands focus to an engine-chosen leaf, and several
;;                   leaves in this proof share a goal, so focusing by goal
;;                   fragment is ambiguous.  It ERRORS on a miss: a focus helper
;;                   that silently leaves focus put hides every later mistake.
;;   rc-have-and     `fact'/`inst+' will not split a CONJUNCTIVE antecedent, and
;;                   `grind' will not close a goal that sits verbatim in context.
;;   rc-fact-and     the same, for citing a lemma whose hypotheses are an AND
;;                   (rr-add-closed).  Note rr-sup-in/-upper/-least need NO such
;;                   helper: they state their three guards as nested implications,
;;                   so `fact' peels and detaches them in one call.
;;   rc-find/rc-idx  select a hypothesis by CONTENT rather than by shape or
;;                   position -- reconstructing a formula to cite it is how a
;;                   driver silently addresses the wrong assumption.


;; ---- selecting an assumption by CONTENT, never by position ---------------
;; These replace `(car (dk-asms))' -- the most recent assumption -- which is
;; even more fragile than the shape-matching the brief warns about: it survives
;; against a saved band (a fixed starting point, where landings always sit in
;; the same order) and breaks in a fresh load, where they do not.
(define (rc-has? tree sub)
  (or (equal? tree sub)
      (and (pair? tree) (or (rc-has? (car tree) sub) (rc-has? (cdr tree) sub)))))

(define (rc-and-with sub)                 ; the context AND mentioning SUB
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "rc-and-with: no context AND mentioning" sub))
          ((and (pair? (car l)) (eq? (caar l) 'AND) (rc-has? (car l) sub)) (car l))
          (else (loop (cdr l))))))

(define (rc-mem-in set-expr)              ; the context (IN t SET-EXPR), for sep-me
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "rc-mem-in: no context membership in" set-expr))
          ((and (pair? (car l)) (eq? (caar l) 'IN) (equal? (caddr (car l)) set-expr))
           (car l))
          (else (loop (cdr l))))))

(define (rc-focus-exact form)
  (let loop ((l (proof-leaves)))
    (cond ((null? l) (error "rc-focus-exact: no leaf with goal" form))
          ((equal? (wff-formula (sequent-node-assertion (car l))) form)
           (dk-focus! (car l)))
          (else (loop (cdr l))))))
(define (rc-have-and a b)
  (have! (list 'AND a b)
         (lambda () (di) (ass) (rc-focus-exact b) (ass))))
(define (rc-fact-and lemma args a b)
  (let ((land (dk-landed* (lambda () (apply fact (cons lemma args))))))
    (rc-have-and a b)
    (detach! (car land))))
(define rc-cauchy
  '(FORALL eps (IMPLIES (POS-RR eps)
     (FORSOME n (AND (IN n NN)
       (FORALL m (IMPLIES (IN m NN)
         (FORALL n_ (IMPLIES (IN n_ NN)
           (IMPLIES (AND (<= n m) (<= n n_))
             (<= ((DIST RR-MS) (f m) (f n_)) eps)))))))))))
(define rc-A
  '(SEP x_ RR
     (FORSOME m_ (AND (IN m_ NN)
       (FORALL k_ (IMPLIES (AND (IN k_ NN) (<= m_ k_))
         (<= x_ (f k_))))))))
(sp (make-wff '(IS-COMPLETE RR-MS)))
(mac 'is-complete)
(di)
(fact 'rr-is-metric-space)
(ass)
(di)
(di)
(mac-h 'is-cauchy-seq (list 'IS-CAUCHY-SEQ 'RR-MS 'f))
(dk-split! (list 'AND '(IS-METRIC-SPACE RR-MS)
                          (list 'AND '(IN f (FUN NN (PTS RR-MS)))
                                rc-cauchy)))
(have! (list 'IN rc-A 'SET)
                (lambda () (sep-set) (fact 'rr-is-set) (ass)))
(have! '(POS-RR 1) (lambda () (mac 'pos-rr) (arith)))
(define rc-N #f)
(set! rc-N (obtain (lambda () (inst+ rc-cauchy '1))))
(newline)
(slot-h 'PTS '(IN f (FUN NN (PTS RR-MS))))
(if rc-N
             (fact 'fun-apply-type-c 'f 'NN 'RR rc-N)
             (error "no threshold to type"))
(fact 'rr-one-in)
(fact 'rr-sub-in-rr (list 'f rc-N) 1)
(define rc-witness (list '- (list 'f rc-N) 1))
(cut (list 'IN rc-witness rc-A))
(sep-mi)
(ass)
(dk-focus-goal! "forsome([m_ in nn]")
(ew rc-N)
(di)
(ass)
(dk-focus-goal! "forall([k_]")
(di)
(di)
(dk-split!
          (let loop ((l (dk-asms)))
            (cond ((null? l) (error "no guard conjunction in context"))
                  ((and (pair? (car l)) (eq? (caar l) 'AND)) (car l))
                  (else (loop (cdr l))))))
(define rc-k #f)
;; goal is (<= (- (f N) 1) (f k)) -- k is the arg of the RHS
         (let ((g (dk-goal)))
           (set! rc-k (cadr (caddr g))))
(newline)
(fact 'fun-apply-type-c 'f 'NN 'RR rc-k)
(fact 'nn-le-refl rc-N)
(define (rc-contains? tree sym)
  (cond ((eq? tree sym) #t)
        ((pair? tree) (or (rc-contains? (car tree) sym)
                          (rc-contains? (cdr tree) sym)))
        (else #f)))
(define (rc-find pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) #f)
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))
(define rc-bound2
  (rc-find (lambda (a)
             (and (pair? a) (eq? (car a) 'FORALL)
                  (rc-contains? a 'DIST)
                  (rc-contains? a rc-N)))))
(newline)
(define rc-landings '())
(set! rc-landings (dk-landed* (lambda () (inst+ rc-bound2 rc-N))))
(newline)
(define rc-step1 (if (null? rc-landings) #f (car rc-landings)))
(define rc-landings2 '())
(set! rc-landings2 (dk-landed* (lambda () (inst+ rc-step1 rc-k))))
(newline)
;; both conjuncts are in context verbatim; grind will NOT just use them,
         ;; so split the AND goal and close each leaf with ass explicitly.
         (have! (list 'AND (list '<= rc-N rc-N) (list '<= rc-N rc-k))
                (lambda ()
                  (di)
                  (ass)
                  (dk-focus-goal! (string-append (symbol->string rc-N) " <= "
                                                 (symbol->string rc-k)))
                  (ass)))
(define rc-impl (if (null? rc-landings2) #f (car rc-landings2)))
(detach! rc-impl)
(mac-h 'rr-ms-dist
                (list '<= (list '(DIST RR-MS) (list 'f rc-N) (list 'f rc-k)) 1))
(mac-h 'rr-abs-bound
                (list '<= (list 'abs (list '- (list 'f rc-N) (list 'f rc-k))) 1))
(newline)
(let loop ((l (dk-asms)) (i 1))
  (if (pair? l)
      (begin (display "  ") (display i) (display ". ")
             (display (expression->string (car l))) (newline)
             (loop (cdr l) (+ i 1)))))
(dk-split! (rc-and-with (list 'f rc-k)))
(newline)
(let loop ((l (dk-asms)) (i 1))
  (if (pair? l)
      (begin (display "  ") (display i) (display ". ")
             (display (expression->string (car l))) (newline)
             (loop (cdr l) (+ i 1)))))
(ineq 1)
(newline)
(newline)
(dk-focus-goal! (string-append "f(" (symbol->string rc-N)
                                                 ") - f(" (symbol->string rc-k)
                                                 ") in rr"))
(fact 'rr-sub-in-rr (list 'f rc-N) (list 'f rc-k))
(ass)
(newline)
(dk-focus-goal! "converges(rr-ms, f)")
(newline)
(let loop ((l (dk-asms)) (i 1))
  (if (and (pair? l) (< i 8))
      (begin (display "  ") (display i) (display ". ")
             (display (expression->string (car l))) (newline)
             (loop (cdr l) (+ i 1)))))
(have! (list 'FORSOME 'x_ (list 'IN 'x_ rc-A))
                (lambda () (ew rc-witness) (ass)))
(have! (list 'SUBSET rc-A 'RR)
                (lambda ()
                  (mac 'subset-def)
                  (di)
                  (sep-me (rc-mem-in rc-A))   ; the ASSUMPTION x in A, not the goal
                  (ass)))
(define rc-ub (list '+ (list 'f rc-N) 1))
(rc-fact-and 'rr-add-closed (list (list 'f rc-N) 1)
                      (list 'IN (list 'f rc-N) 'RR) '(IN 1 RR))
(cut (list 'RR-BOUNDED-ABOVE rc-A))
(mac 'rr-bounded-above)
(ew rc-ub)
(mac 'rr-upper-bound)
(di)
(newline)
(dk-focus-goal! "+ 1 in rr")
(ass)
(dk-focus-goal! "x <= f(")
(di)
(define rc-m #f)
(set! rc-m (obtain (lambda () (sep-me (rc-mem-in rc-A)))))
(newline)
(define rc-c #f)
(set! rc-c (obtain (lambda () (fact 'nn-pair-upper-bound rc-N rc-m))))
(newline)
(define rc-xb
  (list 'FORALL 'k_ (list 'IMPLIES (list 'AND '(IN k_ NN) (list '<= rc-m 'k_))
                          (list '<= 'x (list 'f 'k_)))))
(define rc-xl '())
(set! rc-xl (dk-landed* (lambda () (inst+ rc-xb rc-c))))
(newline)
(rc-have-and (list 'IN rc-c 'NN) (list '<= rc-m rc-c))
(detach! (car rc-xl))
(fact 'nn-le-refl rc-N)
(define rc-cl0 '())
(set! rc-cl0 (dk-landed* (lambda () (inst+ rc-bound2 rc-N))))
(define rc-cl '())
(set! rc-cl (dk-landed* (lambda () (inst+ (car rc-cl0) rc-c))))
(rc-have-and (list '<= rc-N rc-N) (list '<= rc-N rc-c))
(detach! (car rc-cl))
(fact 'fun-apply-type-c 'f 'NN 'RR rc-c)
(mac-h 'rr-ms-dist
                         (list '<= (list '(DIST RR-MS) (list 'f rc-N) (list 'f rc-c)) 1))
(mac-h 'rr-abs-bound
                         (list '<= (list 'abs (list '- (list 'f rc-N) (list 'f rc-c))) 1))
(dk-split! (rc-and-with (list 'f rc-c)))
(newline)
(let loop ((l (dk-asms)) (i 1))
  (if (and (pair? l) (< i 10))
      (begin (display "  ") (display i) (display ". ")
             (display (expression->string (car l))) (newline)
             (loop (cdr l) (+ i 1)))))
(newline)
(newline)
(let loop ((l (dk-asms)) (i 1))
  (if (and (pair? l) (< i 16))
      (begin (display "  ") (display i) (display ". ")
             (display (expression->string (car l))) (newline)
             (loop (cdr l) (+ i 1)))))
(define rc-xi
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) #f)
          ((equal? (car l) (list '<= 'x (list 'f rc-c))) i)
          (else (loop (cdr l) (+ i 1))))))
(define rc-lo
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) #f)
          ((and (pair? (car l)) (eq? (caar l) '<=) (equal? (cadar l) -1)) i)
          (else (loop (cdr l) (+ i 1))))))
(write rc-lo)
(newline)
(ineq rc-xi 2)
(ineq rc-xi 1 2)
(newline)
(rc-focus-exact (list 'IN (list '- (list 'f rc-N) (list 'f rc-c)) 'RR))
(fact 'rr-sub-in-rr (list 'f rc-N) (list 'f rc-c))
(ass)
(newline)
(dk-focus-goal! "converges(rr-ms, f)")
(newline)
(define rc-L (list 'SUP rc-A))
(fact 'rr-sup-in rc-A)
(fact 'rr-sup-upper rc-A)
(fact 'rr-sup-least rc-A)
(newline)
(newline)
(mac-h 'rr-upper-bound (list 'RR-UPPER-BOUND rc-A rc-L))
(dk-split! (rc-and-with 'SUP))
(mac 'converges)
(ew rc-L)
(mac 'converges-to)
(di)
(newline)
(dk-focus-goal! "is-metric-space(rr-ms)")
(fact 'rr-is-metric-space)
(ass)
(dk-focus-goal! "f in fun(nn, pts(rr-ms)) and")
(di)
(dk-focus-goal! "f in fun(nn, pts(rr-ms))")
(slot 'PTS)
(ass)
(newline)
(di)
(dk-focus-goal! ") in pts(rr-ms)")
(slot 'PTS)
(ass)
(dk-focus-goal! "forall([eps], pos-rr(eps)")
(di)
(di)
(define rc-d #f)
(set! rc-d (obtain (lambda () (fact 'rr-pos-halvable 'eps))))
(newline)
(define rc-N2 #f)
(set! rc-N2 (obtain (lambda () (inst+ rc-cauchy rc-d))))
(newline)
(ew rc-N2)
(di)
(ass)
(newline)
(mac-h 'pos-rr (list 'POS-RR rc-d))
(dk-split! (rc-and-with rc-d))
(fact 'fun-apply-type-c 'f 'NN 'RR rc-N2)
(fact 'rr-sub-in-rr (list 'f rc-N2) rc-d)
(newline)
(define rc-bd
  (rc-find (lambda (a)
             (and (pair? a) (eq? (car a) 'FORALL)
                  (rc-contains? a 'DIST) (rc-contains? a rc-N2)))))
(newline)
(define rc-w2 (list '- (list 'f rc-N2) rc-d))
(cut (list 'IN rc-w2 rc-A))
(sep-mi)
(ass)
(dk-focus-goal!
                   (string-append (expression->string rc-w2) " <= f(k_)"))
(ew rc-N2)
(di)
(ass)
(dk-focus-goal!
                   (string-append "implies " (expression->string rc-w2) " <= f(k_)"))
(di)
(di)
(define rc-k2 (cadr (caddr (dk-goal))))
(newline)
(dk-split!
          (let loop ((l (dk-asms)))
            (cond ((null? l) (error "no guard"))
                  ((and (pair? (car l)) (eq? (caar l) 'AND)) (car l))
                  (else (loop (cdr l))))))
(fact 'nn-le-refl rc-N2)
(define rc-b1 '())
(set! rc-b1 (dk-landed* (lambda () (inst+ rc-bd rc-N2))))
(define rc-b2 '())
(set! rc-b2 (dk-landed* (lambda () (inst+ (car rc-b1) rc-k2))))
(rc-have-and (list '<= rc-N2 rc-N2) (list '<= rc-N2 rc-k2))
(detach! (car rc-b2))
(fact 'fun-apply-type-c 'f 'NN 'RR rc-k2)
(mac-h 'rr-ms-dist
                         (list '<= (list '(DIST RR-MS) (list 'f rc-N2) (list 'f rc-k2)) rc-d))
(mac-h 'rr-abs-bound
                         (list '<= (list 'abs (list '- (list 'f rc-N2) (list 'f rc-k2))) rc-d))
(dk-split! (rc-and-with (list 'f rc-k2)))
(ineq 1)
(newline)
(rc-focus-exact (list 'IN (list '- (list 'f rc-N2) (list 'f rc-k2)) 'RR))
(fact 'rr-sub-in-rr (list 'f rc-N2) (list 'f rc-k2))
(ass)
(define rc-ptwise
  (rc-find (lambda (a)
             (and (pair? a) (eq? (car a) 'FORALL) (rc-contains? a 'SUP)
                  (not (rc-contains? a 'RR-UPPER-BOUND))))))
(newline)
(inst+ rc-ptwise rc-w2)
(newline)
(newline)
(define rc-ub2 (list '+ (list 'f rc-N2) rc-d))
(rc-fact-and 'rr-add-closed (list (list 'f rc-N2) rc-d)
                               (list 'IN (list 'f rc-N2) 'RR) (list 'IN rc-d 'RR))
(cut (list 'RR-UPPER-BOUND rc-A rc-ub2))
(mac 'rr-upper-bound)
(di)
(ass)
(dk-focus-goal! (string-append "x <= " (expression->string rc-ub2)))
(di)
(define rc-m2 #f)
(set! rc-m2 (obtain (lambda () (sep-me (rc-mem-in rc-A)))))
(define rc-c2 #f)
(set! rc-c2 (obtain (lambda () (fact 'nn-pair-upper-bound rc-N2 rc-m2))))
(write rc-c2)
(newline)
(define rc-xb2 (rc-find (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                         (rc-contains? a rc-m2)))))
(define rc-xl2 '())
(set! rc-xl2 (dk-landed* (lambda () (inst+ rc-xb2 rc-c2))))
(rc-have-and (list 'IN rc-c2 'NN) (list '<= rc-m2 rc-c2))
(detach! (car rc-xl2))
(fact 'nn-le-refl rc-N2)
(define rc-e1 '())
(set! rc-e1 (dk-landed* (lambda () (inst+ rc-bd rc-N2))))
(define rc-e2 '())
(set! rc-e2 (dk-landed* (lambda () (inst+ (car rc-e1) rc-c2))))
(rc-have-and (list '<= rc-N2 rc-N2) (list '<= rc-N2 rc-c2))
(detach! (car rc-e2))
(fact 'fun-apply-type-c 'f 'NN 'RR rc-c2)
(mac-h 'rr-ms-dist
                         (list '<= (list '(DIST RR-MS) (list 'f rc-N2) (list 'f rc-c2)) rc-d))
(mac-h 'rr-abs-bound
                         (list '<= (list 'abs (list '- (list 'f rc-N2) (list 'f rc-c2))) rc-d))
(dk-split! (rc-and-with (list 'f rc-c2)))
(define rc-xi2
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) #f)
          ((equal? (car l) (list '<= 'x (list 'f rc-c2))) i)
          (else (loop (cdr l) (+ i 1))))))
(newline)
(ineq rc-xi2 2)
(newline)
(rc-focus-exact (list 'IN (list '- (list 'f rc-N2) (list 'f rc-c2)) 'RR))
(fact 'rr-sub-in-rr (list 'f rc-N2) (list 'f rc-c2))
(ass)
(define rc-least
  (rc-find (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                            (rc-contains? a 'RR-UPPER-BOUND)))))
(inst+ rc-least rc-ub2)
(newline)
(dk-focus-goal! "<= eps)")
(di)
(di)
(define rc-n #f)
(set! rc-n (cadr (cadr (cadr (dk-goal)))))
(newline)
(fact 'fun-apply-type-c 'f 'NN 'RR rc-n)
(fact 'nn-le-refl rc-N2)
(define rc-g1 '())
(set! rc-g1 (dk-landed* (lambda () (inst+ rc-bd rc-N2))))
(define rc-g2 '())
(set! rc-g2 (dk-landed* (lambda () (inst+ (car rc-g1) rc-n))))
(rc-have-and (list '<= rc-N2 rc-N2) (list '<= rc-N2 rc-n))
(detach! (car rc-g2))
(mac-h 'rr-ms-dist
                         (list '<= (list '(DIST RR-MS) (list 'f rc-N2) (list 'f rc-n)) rc-d))
(mac-h 'rr-abs-bound
                         (list '<= (list 'abs (list '- (list 'f rc-N2) (list 'f rc-n))) rc-d))
(dk-split! (rc-and-with (list 'f rc-n)))
(mac-h 'pos-rr '(POS-RR eps))
(dk-split! (rc-and-with 'eps))
(fact 'rr-sub-in-rr (list 'f rc-n) rc-L)
(mac 'rr-ms-dist)
(mac 'rr-abs-bound)
(define (rc-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) #f)
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define rc-i-lo  (rc-idx (list '<= (list '- rc-d) (list '- (list 'f rc-N2) (list 'f rc-n)))))
(define rc-i-hi  (rc-idx (list '<= (list '- (list 'f rc-N2) (list 'f rc-n)) rc-d)))
(define rc-i-sl  (rc-idx (list '<= rc-w2 rc-L)))
(define rc-i-su  (rc-idx (list '<= rc-L rc-ub2)))
(define rc-i-eps (rc-idx (list '= (list '+ rc-d rc-d) 'eps)))
(newline)
(di)
(ineq rc-i-su rc-i-hi rc-i-eps)
(ineq rc-i-sl rc-i-lo rc-i-eps)
(newline)
(rc-focus-exact (list 'IN (list '- (list 'f rc-N2) (list 'f rc-n)) 'RR))
(fact 'rr-sub-in-rr (list 'f rc-N2) (list 'f rc-n))
(ass)
(rc-focus-exact
                   (list '<= (list '- (list 'f rc-n) rc-L) 'eps))
(define rc-j-sl  (rc-idx (list '<= rc-w2 rc-L)))
(define rc-j-lo  (rc-idx (list '<= (list '- rc-d) (list '- (list 'f rc-N2) (list 'f rc-n)))))
(define rc-j-eps (rc-idx (list '= (list '+ rc-d rc-d) 'eps)))
(newline)
(ineq rc-j-sl rc-j-lo rc-j-eps)
(newline)
(newline)
(qed 'rr-complete)
(category! 'rr-complete 'analysis)
