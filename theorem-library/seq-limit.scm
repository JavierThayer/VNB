;;; theorem-library/seq-limit.scm -- THE LIMIT OF A REAL SEQUENCE AS A TERM,
;;; and the two pieces of limit arithmetic the tree was missing.
;;;
;;; WHY.  Nothing in the tree let you WRITE  lim_k f(k)  as a term.
;;; `SERIES-LIMIT' (dominated-convergence.scm) is the limit of the PARTIAL SUMS
;;; of a series, not of a sequence, and everything else about limits is stated
;;; through the PREDICATE `CONVERGES-TO(RR-MS, f, L)', which cannot appear in
;;; the body of a VNB-LAMBDA.  Prop 4.16 of docs/calculus.pdf (a uniform limit
;;; of antiderivatives) has to BUILD the limit function  x |-> lim_k f_k(x),
;;; so the term is a prerequisite, not a convenience.
;;;
;;; SEQ-LIMIT IS TOTAL, AND THAT IS THE DESIGN DECISION.  The obvious
;;;
;;;     SEQ-LIMIT(f) = IOTA lm_. CONVERGES-TO(RR-MS, f, lm_)
;;;
;;; -- the shape `DERIV' and `SERIES-LIMIT' both take -- is DEFINED only where
;;; the sequence converges, and `=' is partial, so
;;;     (VNB-LAMBDA x RR (SEQ-LIMIT (VNB-LAMBDA k NN ((fam k) x))))
;;; would not be in FUN(RR,RR) unless the family converged at EVERY real.  In
;;; Prop 4.16 it converges on [a,b] and nowhere else is claimed, so the partial
;;; description is unusable exactly where the theorem needs it.  The definition
;;; therefore carries its own fallback,
;;;
;;;     SEQ-LIMIT(f) = IF CONVERGES(RR-MS,f) THEN (IOTA lm_ ...) ELSE 0,
;;;
;;; which makes `seq-limit-in-rr' UNCONDITIONAL: the term is real for every f
;;; whatever, junk included, and the lam-t body obligation is a one-line
;;; citation.  The price is the usual price of totalisation -- SEQ-LIMIT(f) = 0
;;; says nothing when f diverges -- and it is paid once here rather than at
;;; every `VNB-LAMBDA' that mentions a limit.
;;;
;;; NO EXTRA TYPING CONJUNCT IS NEEDED inside the IOTA.  The eight IOTA-defined
;;; functoids in the tree either pin the value's membership with an explicit
;;; (IN v RR) conjunct or let the characterising predicate do it; `CONVERGES-TO'
;;; does it (its third conjunct is (IN L (PTS s))), so the description body is
;;; the bare predicate, as `DERIV' and `SERIES-LIMIT' have it.  The membership
;;; comes out through one `slot-h' on PTS(RR-MS), which is what `seq-limit-in-rr'
;;; is for.
;;;
;;; WHAT IS HERE NOW.  Two transfer-form limit laws, both `modulo 0':
;;;
;;;   rr-limit-scale   h(j) = f(j).c  pointwise, f -> lv   =>   h -> lv.c
;;;   rr-limit-sub     h(j) = f(j)-g(j) pointwise, f -> lv, g -> mv  =>  h -> lv-mv
;;;
;;; The tree had `rr-limit-add' (limit-arithmetic.scm) and `rr-null-scale' (the
;;; scalar law for NULL sequences only, and only for a NONNEGATIVE factor).
;;; rr-limit-scale is the general statement; the reciprocal is kept out of the
;;; estimate by `rr-scale-eps' (rr-null-scale.scm), which packages
;;; d = eps/(1+|c|) once and hands back the d.  rr-limit-sub is then a
;;; composition -- scale by -1, then add -- not a second epsilon argument.
;;;
;;; WHAT MOVED OUT (2026-09-14).  SEQ-LIMIT itself and everything about it --
;;; seq-limit-converges-to, seq-limit-in-rr, seq-limit-value, the TAIL bound
;;; rr-limit-tail-abs-le and rr-cauchy-converges (sections L3-L7) -- now live
;;; in theorem-library/seq-limit-core.scm, which loads ~140 entries EARLIER,
;;; beside rr-complete-proof and metric-limit-unique.  The reason is load
;;; order: `unif-cauchy-has-uniform-limit' (unif-cauchy-limit.scm) is built
;;; from those five and must precede ascoli-bridge, while the two laws kept
;;; here cite limit-arithmetic and rr-null-scale, which load after
;;; ascoli-bridge.  The design argument above still belongs to the definition
;;; and is left here, where it was written; seq-limit-core.scm points back.
;;;
;;; Loads after limit-arithmetic (rr-limit-add), rr-null-scale (rr-scale-eps),
;;; rr-abs-basics (rr-abs-mult, rr-abs-closed, rr-abs-nonneg), rr-ms-dist,
;;; fun-apply-type-proof (fun-apply-type-c), metric-completeness
;;; (CONVERGES-TO) and driver-kit.  Nothing here needs seq-limit-core.
;;; =====================================================================

;;; ---- file-local driver helpers (the `sq-' prefix) ---------------------
;;; seq-limit-core.scm carries its own copies of the ones its block uses
;;; (per-file environments); the L6/L7-only helpers (`ulc-', sq-idx, sq-ineq)
;;; went with it and are not here.

;;; Select a hypothesis by CONTENT; a miss ERRORS.
(define (sq-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "sq-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (sq-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME already in the CONTEXT (`obtain' sees only what its own
;;; lane landed); the eigenvariable is read off by free-variable set difference.
(define (sq-skolem! ex)
  (let* ((fv0 (sq-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (sq-fvs (dk-asms)))))
      (if (null? fresh) (error "sq-skolem!: nothing appeared" ex) (car fresh)))))

;;; `di' until an ASSUMPTION lands -- an UNGUARDED universal peels the
;;; quantifier and lands nothing, so loop on the LANDING, never on a count.
(define (sq-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "sq-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (sq-di-landed-1!)
  (let ((new (sq-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "sq-di-landed-1!: expected 1" (map expression->string new)))))

;;; di-split an AND goal to its leaves and run CLOSER on each.
(define (sq-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (sq-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; (IN x RR) off a POS-RR, on a SIDE branch: `mac-h' is destructive and the
;;; main branch still wants the POS-RR for later detachments.
(define (sq-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; Peel the whole leading FORALL/IMPLIES prefix.
(define (sq-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; The eps-N clause of an unfolded CONVERGES-TO, named by the SEQUENCE it is
;;; about -- both clauses of a two-limit proof have the same shape.
(define (sq-tail-of s)
  (sq-find s (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a s)
                              (dk-contains? a 'POS-RR)))))

;;; The inner (FORALL n_ ... (<= thr n_) => ...) of a skolemized eps-N clause,
;;; discriminated on its THRESHOLD and captured while the context is clean.
(define (sq-inner thr)
  (sq-find thr (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                (let ((b (caddr a)))
                                  (and (pair? b) (eq? (car b) 'IMPLIES)
                                       (dk-contains? (caddr b) thr)))))))

;;; The four conjuncts of an unfolded CONVERGES-TO(RR-MS, seq, L) GOAL.
(define (sq-converges-to! eps-branch)
  (mac 'converges-to)
  (sq-and!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond ((eq? (car gl) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
             ((eq? (car gl) 'IN) (slot 'PTS) (ass))
             (else (eps-branch)))))))

;;; =====================================================================
;;; L1.  rr-limit-scale -- lim (f.c) = (lim f).c, in TRANSFER form.
;;;
;;; The estimate is |h(n) - lv.c| = |c|.|f(n) - lv|, and `rr-scale-eps' hands
;;; back the d with |c|.t <= eps for every 0 <= t <= d, so no reciprocal
;;; appears in this driver at all.  `ineq' reads abs(_) as an opaque atom, so
;;; the two sides are normalised to the SAME atom (abs(c) * abs(f(n)-lv))
;;; before the d-property is instantiated.
;;; =====================================================================

(sp (make-wff "forall([c in rr, f in fun(nn,rr), h in fun(nn,rr), lv in rr],
     forall([j_ in nn], h(j_) = f(j_) * c) implies
     converges-to(rr-ms, f, lv) implies
     converges-to(rr-ms, h, lv * c))"))
(quietly (lambda () (sq-peel!)))
(define sc-pt (sq-find 'pointwise
   (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'h)))))
(quietly (lambda ()
  (dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO RR-MS f lv)))
                             (lambda (a) (eq? (car a) 'AND))))))
(define sc-tf (sq-tail-of 'f))
(quietly (lambda ()
  (fact 'rr-abs-closed 'c)
  (fact 'rr-abs-nonneg 'c)
  (have! '(AND (IN lv RR) (IN c RR)))
  (fact 'rr-mul-closed 'lv 'c)))

(define (sc-eps!)
  (let ((eps (cadr (sq-di-landed-1!))))
    (sq-pos-in-rr! eps)
    (let* ((dex (dk-fact! 'rr-scale-eps '(abs c) eps))
           (d   (sq-skolem! dex))
           (dprop (sq-find 'dprop (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                   (dk-contains? a d)
                                                   (dk-contains? a '(abs c))))))
           (exf (dk-deepest (lambda () (inst+ sc-tf d))))
           (bigN (sq-skolem! exf))
           (inner (sq-inner bigN)))
      (ew bigN)
      (sq-and!
       (lambda ()
         (if (eq? (car (dk-goal)) 'IN) (ass)
             (let* ((memb (sq-di-landed-1!))
                    (n_ (cadr memb)))
               (sq-di-landed!)                        ; the (<= bigN n_) hypothesis
               (inst+ inner n_)
               (inst+ sc-pt n_)
               (fact 'fun-apply-type-c 'f 'NN 'RR n_)
               (fact 'fun-apply-type-c 'h 'NN 'RR n_)
               (subst (list '= (list 'h n_) (list '* (list 'f n_) 'c)))
               (have! (list 'AND (list 'IN (list 'f n_) 'RR) '(IN c RR)))
               (fact 'rr-mul-closed (list 'f n_) 'c)
               ;; rr-ms-dist is GUARDED: type the arguments BEFORE the rewrite.
               (mac 'rr-ms-dist)
               (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) (list 'f n_) 'lv) d))
               (fact 'rr-sub-in-rr (list 'f n_) 'lv)
               (let* ((u (list '- (list 'f n_) 'lv))
                      (lhs (list '- (list '* (list 'f n_) 'c) '(* lv c))))
                 (have! (list '= lhs (list '* u 'c)) (lambda () (crs)))
                 (subst (list '= lhs (list '* u 'c)))
                 (have! (list 'AND (list 'IN u 'RR) '(IN c RR)))
                 (fact 'rr-abs-mult u 'c)
                 (subst (list '= (list 'abs (list '* u 'c))
                              (list '* (list 'abs u) '(abs c))))
                 (fact 'rr-abs-closed u)
                 (fact 'rr-abs-nonneg u)
                 (have! (list '= (list '* (list 'abs u) '(abs c))
                              (list '* '(abs c) (list 'abs u))) (lambda () (crs)))
                 (subst (list '= (list '* (list 'abs u) '(abs c))
                              (list '* '(abs c) (list 'abs u))))
                 (dk-deepest (lambda () (inst+ dprop (list 'abs u))))
                 (ass)))))))))

(quietly (lambda () (sq-converges-to! sc-eps!)))
(qed 'rr-limit-scale)
(topic! 'rr-limit-scale 'analysis)
(alias! 'rr-limit-scale
        "the limit of a scalar multiple is the scalar multiple of the limit")

;;; =====================================================================
;;; L2.  rr-limit-sub -- lim (f - g) = lim f - lim g, in TRANSFER form.
;;;
;;; A COMPOSITION, not a second epsilon argument: scale g by -1 (L1), add
;;; (rr-limit-add), and rewrite lv + mv.(-1) to lv - mv with `crs'.  The
;;; scaled sequence has to be BUILT and TYPED, which is the whole cost.
;;;
;;; The lambda's bound variable is `q_', not `j_': the pointwise hypotheses
;;; below quantify `j_' and a binder list scopes left to right, so a lambda
;;; spelled with `j_' inside a formula that also binds `j_' carries two
;;; distinct variables of the same name and `validate-wff!' says so.
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr), g in fun(nn,rr), h in fun(nn,rr), lv in rr, mv in rr],
     forall([j_ in nn], h(j_) = f(j_) - g(j_)) implies
     converges-to(rr-ms, f, lv) implies converges-to(rr-ms, g, mv) implies
     converges-to(rr-ms, h, lv - mv))"))
(quietly (lambda () (sq-peel!)))
(define sb-pt (sq-find 'pointwise
   (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'h)))))
(define sb-ng '(VNB-LAMBDA q_ NN (* (g q_) (- 1))))
(define sb-beta (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
                  (list '= (list sb-ng 'j_) '(* (g j_) (- 1))))))
(define sb-add  (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
                  (list '= '(h j_) (list '+ '(f j_) (list sb-ng 'j_))))))
(quietly (lambda ()
 (fact 'rr-one-in) (fact 'rr-neg-closed 1)
 (have! (list 'IN sb-ng '(FUN NN RR))
   (lambda ()
     (dk-lam-t!)
     (let ((j (cadr (sq-di-landed-1!))))
       (fact 'fun-apply-type-c 'g 'NN 'RR j)
       (have! (list 'AND (list 'IN (list 'g j) 'RR) '(IN (- 1) RR)))
       (fact 'rr-mul-closed (list 'g j) '(- 1))
       (ass))))
 (have! sb-beta
   (lambda ()
     (sq-di-landed-1!)
     (fact 'fun-apply-type-c 'g 'NN 'RR 'j_)
     (have! '(AND (IN (g j_) RR) (IN (- 1) RR)))
     (fact 'rr-mul-closed '(g j_) '(- 1))
     (lam-b)
     (rfl)))
 (fact 'rr-limit-scale '(- 1) 'g sb-ng 'mv)
 (have! sb-add
   (lambda ()
     (sq-di-landed-1!)
     (inst+ sb-pt 'j_)
     (inst+ sb-beta 'j_)
     (fact 'fun-apply-type-c 'f 'NN 'RR 'j_)
     (fact 'fun-apply-type-c 'g 'NN 'RR 'j_)
     (subst (list '= (list sb-ng 'j_) '(* (g j_) (- 1))))
     (subst '(= (h j_) (- (f j_) (g j_))))
     (crs)))
 (have! '(AND (IN mv RR) (IN (- 1) RR)))
 (fact 'rr-mul-closed 'mv '(- 1))
 (fact 'rr-limit-add 'f sb-ng 'h 'lv '(* mv (- 1)))
 (have! '(= (- lv mv) (+ lv (* mv (- 1)))) (lambda () (crs)))
 (subst '(= (- lv mv) (+ lv (* mv (- 1)))))
 (ass)))
(qed 'rr-limit-sub)
(topic! 'rr-limit-sub 'analysis)
(alias! 'rr-limit-sub
        "the limit of a pointwise difference is the difference of the limits")
