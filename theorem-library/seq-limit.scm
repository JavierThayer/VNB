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
;;; WHAT ELSE IS HERE.  Two transfer-form limit laws, both `modulo 0':
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
;;; Loads after limit-arithmetic (rr-limit-add), rr-null-scale (rr-scale-eps),
;;; dominated-convergence (rr-limit-unique), rr-abs-basics (rr-abs-mult,
;;; rr-abs-closed, rr-abs-nonneg), rr-ms-dist, fun-apply-type-proof
;;; (fun-apply-type-c), metric-completeness (CONVERGES, CONVERGES-TO) and
;;; driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `sq-' prefix) ---------------------

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

;;; inst+ lands its whole instantiation chain; the detached result is the
;;; landing no other landing contains.
(define (ulc-inst! fm t) (dk-deepest (lambda () (inst+ fm t))))

;;; skolemize a context FORSOME, returning (LANDED . (EIGENVARIABLES)).
(define (ulc-skolem! fm)
  (let* ((landed (dk-landed* (lambda () (ai fm))))
         (new (car landed))
         (fvs-b (free-vars fm)))
    (list new (filter (lambda (v) (not (memq v fvs-b))) (free-vars new)))))

;;; |a - c| <= |a - b| + |b - c|, landed as a hypothesis.  The three arguments
;;; must already be typed in RR; rr-abs-triangle-c is about a SUM, so the
;;; difference is normalised to (a-b) + (b-c) by `crs' and substituted in.
(define (ulc-tri! aa bb cc)
  (let ((u (list '- aa bb)) (v (list '- bb cc)) (w (list '- aa cc)))
    (fact 'rr-sub-in-rr aa bb) (fact 'rr-sub-in-rr bb cc) (fact 'rr-sub-in-rr aa cc)
    (have! (list '<= (list 'abs w) (list '+ (list 'abs u) (list 'abs v)))
      (lambda ()
        (have! (list '= w (list '+ u v)) (lambda () (crs)))
        (subst (list '= w (list '+ u v)))
        (fact 'rr-abs-triangle-c u v)
        (ass)))))

;;; `ineq' wants 1-based assumption indices, named ONE BY ONE.
(define (sq-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "sq-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (sq-ineq . forms) (apply ineq (map sq-idx forms)))

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

;;; =====================================================================
;;; L3.  SEQ-LIMIT -- the limit of a real sequence, as a TERM.
;;; =====================================================================

(def-functoid 'SEQ-LIMIT '(f)
  '(IF (CONVERGES RR-MS f) (IOTA lm_ (CONVERGES-TO RR-MS f lm_)) 0))
(notation! 'SEQ-LIMIT 'kind 'functoid 'arity 1
           'english "the limit of the sequence $1"
           'noun "limit of the sequence $1")

(define sl-if '(IF (CONVERGES RR-MS f) (IOTA lm_ (CONVERGES-TO RR-MS f lm_)) 0))
(define sl-iota '(IOTA lm_ (CONVERGES-TO RR-MS f lm_)))

;;; (IN v RR) off a CONVERGES-TO, on a SIDE branch -- `mac-h' REPLACES the
;;; hypothesis it unfolds and the CONVERGES-TO is wanted again below.
(define (sl-in-rr! v cvt)
  (have! (list 'IN v 'RR)
    (lambda ()
      (dk-split! (dk-landed-find (lambda () (mac-h 'converges-to cvt))
                                 (lambda (a) (eq? (car a) 'AND))))
      (slot-h 'PTS (list 'IN v '(PTS RR-MS)))
      (ass))))
(define (sl-fun! cvt)
  (have! '(IN f (FUN NN RR))
    (lambda ()
      (dk-split! (dk-landed-find (lambda () (mac-h 'converges-to cvt))
                                 (lambda (a) (eq? (car a) 'AND))))
      (slot-h 'PTS '(IN f (FUN NN (PTS RR-MS))))
      (ass))))

;;; The IOTA's existence-and-uniqueness obligation: the witness is the limit
;;; CONVERGES hands over, and `rr-limit-unique' is the uniqueness.
(define (sl-exists-unique!)
  (let* ((cex (dk-landed-1 (lambda () (mac-h 'converges (list 'CONVERGES 'RR-MS 'f)))))
         (lm  (sq-skolem! cex))
         (cvt (sq-find 'conv (dk-head? 'CONVERGES-TO))))
    (sl-fun! cvt)
    (sl-in-rr! lm cvt)
    (ew lm)
    (sq-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'CONVERGES-TO)
           (ass)
           (let* ((yt (sq-di-landed-1!))
                  (y  (cadddr yt)))            ; CONVERGES-TO(s, f, L): L is 4th
             (sl-in-rr! y yt)
             (fact 'rr-limit-unique 'f lm y)
             (ass)))))))

(sp (make-wff '(FORALL f (IMPLIES (CONVERGES RR-MS f)
                  (CONVERGES-TO RR-MS f (SEQ-LIMIT f))))))
(quietly (lambda () (sq-peel!) (mac 'seq-limit)))
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) 'CONVERGES)
       (ass)                                   ; the IF's condition, assumed
       (begin
         (quietly (lambda () (subst (list '= sl-if sl-iota))))
         (for-each
          (lambda (m)
            (dk-focus! m)
            (if (eq? (car (dk-goal)) 'CONVERGES-TO)
                (ass)                          ; the description's own property
                (quietly (lambda () (sl-exists-unique!)))))
          (dk-opened (lambda () (iota-d sl-iota)))))))
 (dk-opened (lambda () (if-true sl-if))))
(qed 'seq-limit-converges-to)
(topic! 'seq-limit-converges-to 'analysis)
(alias! 'seq-limit-converges-to "a convergent real sequence converges to its limit")

;;; UNCONDITIONAL definedness -- what the totalising IF buys.  Without it
;;; SEQ-LIMIT cannot appear in the body of a VNB-LAMBDA whose domain is larger
;;; than the set where the family converges, which is exactly Prop 4.16's case.
(sp (make-wff '(FORALL f (IN (SEQ-LIMIT f) RR))))
(quietly (lambda () (sq-peel!)))
(use-em '(CONVERGES RR-MS f)
  (lambda ()
    (quietly (lambda ()
      (fact 'seq-limit-converges-to 'f)
      (dk-split! (dk-landed-find
                  (lambda () (mac-h 'converges-to '(CONVERGES-TO RR-MS f (SEQ-LIMIT f))))
                  (lambda (a) (eq? (car a) 'AND))))
      (slot-h 'PTS '(IN (SEQ-LIMIT f) (PTS RR-MS)))
      (ass))))
  (lambda ()
    (quietly (lambda ()
      (mac 'seq-limit)
      (for-each (lambda (l)
                  (dk-focus! l)
                  (if (eq? (car (dk-goal)) 'NOT)
                      (ass)
                      (begin (subst (list '= sl-if 0)) (fact 'rr-zero-in) (ass))))
                (dk-opened (lambda () (if-false sl-if))))))))
(qed 'seq-limit-in-rr)
(topic! 'seq-limit-in-rr 'analysis)
(alias! 'seq-limit-in-rr "the limit of a real sequence is a real number")

;;; ... and the identification: a sequence's limit IS its SEQ-LIMIT.
(sp (make-wff '(FORALL f (FORALL lv (IMPLIES (CONVERGES-TO RR-MS f lv)
                                             (= (SEQ-LIMIT f) lv))))))
(quietly (lambda ()
  (sq-peel!)
  (have! '(CONVERGES RR-MS f) (lambda () (mac 'converges) (ew 'lv) (ass)))
  (fact 'seq-limit-converges-to 'f)
  (fact 'seq-limit-in-rr 'f)
  (sl-fun! '(CONVERGES-TO RR-MS f lv))
  (sl-in-rr! 'lv '(CONVERGES-TO RR-MS f lv))
  (fact 'rr-limit-unique 'f '(SEQ-LIMIT f) 'lv)
  (ass)))
(qed 'seq-limit-value)
(topic! 'seq-limit-value 'analysis)
(alias! 'seq-limit-value "a sequence's limit is its SEQ-LIMIT")

;;; =====================================================================
;;; L6.  rr-limit-tail-abs-le -- a TAIL bound passes to the limit.
;;;
;;;   |f(k) - v| <= c  for every k >= N,  f -> lv    =>    |lv - v| <= c
;;;
;;; `rr-limit-abs-le' (dominated-convergence.scm) is the tree's only fact of
;;; this species and it is weaker twice over: the bound must hold at EVERY
;;; index, and the conclusion is about |lv| rather than the distance to a
;;; chosen point.  Both weakenings matter for a uniform-Cauchy family, where
;;; the bound is exactly a TAIL bound and the point is another member of the
;;; family.  The route is `rr-le-all-pos-nonpos' with the estimate taken at the
;;; single index MAX(N, N_eps), as in `rr-limit-abs-le'.
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr), lv in rr, v_ in rr, c in rr, n_ in nn],
   converges-to(rr-ms, f, lv) implies
   forall([k in nn], n_ <= k implies abs(f(k) - v_) <= c) implies
   abs(lv - v_) <= c)"))
(quietly (lambda () (sq-peel!)))
(define cb-pt (car (dk-asms)))
(quietly (lambda ()
  (dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO RR-MS f lv)))
                             (lambda (a) (eq? (car a) 'AND))))))
(define cb-tail (sq-tail-of 'f))
(quietly (lambda ()
  (fact 'rr-sub-in-rr 'lv 'v_)
  (fact 'rr-abs-closed '(- lv v_))
  (have! '(IN (- (abs (- lv v_)) c) RR)
    (lambda () (fact 'rr-sub-in-rr '(abs (- lv v_)) 'c) (ass)))))
(have! '(FORALL eps (IMPLIES (POS-RR eps) (<= (- (abs (- lv v_)) c) eps)))
  (lambda ()
    (quietly (lambda ()
      (let* ((eps (cadr (sq-di-landed-1!)))
             (sk  (ulc-skolem! (ulc-inst! cb-tail eps)))
             (bigN (car (cadr sk))))
        (dk-split! (car sk))
        (let* ((inner (sq-inner bigN))
               (kk (list 'MAX 'n_ bigN)))
        (sq-pos-in-rr! eps)
        (fact 'nn-max-closed 'n_ bigN)
        (fact 'nn-in-rr 'n_) (fact 'nn-in-rr bigN) (fact 'nn-in-rr kk)
        (fact 'rr-le-max-left 'n_ bigN)
        (fact 'rr-le-max-right 'n_ bigN)
        (ulc-inst! inner kk)
        (ulc-inst! cb-pt kk)
        (fact 'fun-apply-type-c 'f 'NN 'RR kk)
        (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) (list 'f kk) 'lv) eps))
        (fact 'rr-sub-in-rr (list 'f kk) 'lv)
        (fact 'rr-abs-closed (list '- (list 'f kk) 'lv))
        (fact 'rr-abs-sub-sym 'lv (list 'f kk))
        (fact 'rr-sub-in-rr 'lv (list 'f kk))
        (fact 'rr-abs-closed (list '- 'lv (list 'f kk)))
        (fact 'rr-sub-in-rr (list 'f kk) 'v_)
        (fact 'rr-abs-closed (list '- (list 'f kk) 'v_))
        (ulc-tri! 'lv (list 'f kk) 'v_)
        (sq-ineq (list '<= '(abs (- lv v_))
                       (list '+ (list 'abs (list '- 'lv (list 'f kk)))
                                (list 'abs (list '- (list 'f kk) 'v_))))
                 (list '= (list 'abs (list '- 'lv (list 'f kk)))
                          (list 'abs (list '- (list 'f kk) 'lv)))
                 (list '<= (list 'abs (list '- (list 'f kk) 'lv)) eps)
                 (list '<= (list 'abs (list '- (list 'f kk) 'v_)) 'c))))))))
(quietly (lambda ()
  (fact 'rr-le-all-pos-nonpos '(- (abs (- lv v_)) c))
  (sq-ineq '(<= (- (abs (- lv v_)) c) 0))))
(qed 'rr-limit-tail-abs-le)
(topic! 'rr-limit-tail-abs-le 'analysis)
(alias! 'rr-limit-tail-abs-le "a tail bound on a real sequence passes to its limit")

;;; =====================================================================
;;; L7.  rr-cauchy-converges -- COMPLETENESS in the abs/eps language.
;;;
;;; `rr-complete' says IS-COMPLETE(RR-MS), and IS-CAUCHY-SEQ is written with
;;; (DIST RR-MS); every estimate in the calculus arc is written with `abs'.
;;; This is the one-line crossing, and it exists so that a proof that has just
;;; produced an abs-form Cauchy estimate does not have to re-derive the metric
;;; packaging.  `modulo 0'.
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr)],
   forall([eps], pos-rr(eps) implies
      forsome([n_ in nn], forall([m_ in nn, p_ in nn],
         n_ <= m_ implies n_ <= p_ implies abs(f(m_) - f(p_)) <= eps)))
   implies converges(rr-ms, f))"))
(quietly (lambda () (sq-peel!)))
(define cc-h (car (dk-asms)))
(quietly (lambda ()
 (fact 'rr-is-metric-space)
 (have! '(IS-CAUCHY-SEQ RR-MS f)
  (lambda ()
    (mac 'is-cauchy-seq)
    (sq-and!
     (lambda ()
       (let ((gl (dk-goal)))
         (cond ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
               ((eq? (car gl) 'IN) (slot 'PTS) (ass))
               (else
                (let* ((eps (cadr (sq-di-landed-1!)))
                       (sk  (ulc-skolem! (ulc-inst! cc-h eps)))
                       (bigN (car (cadr sk))))
                  (dk-split! (car sk))
                  (let ((inner (sq-find 'inner
                                 (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                  (dk-contains? a bigN)
                                                  (dk-contains? a 'abs))))))
                    (ew bigN)
                    (sq-and!
                     (lambda ()
                       (if (eq? (car (dk-goal)) 'IN) (ass)
                           (begin
                             (sq-di-landed!)
                             (dk-split! (car (sq-di-landed!)))
                             (let* ((gl (dk-goal))
                                    (da (cadr gl))
                                    (m  (cadr (cadr da)))
                                    (p  (cadr (caddr da))))
                               (fact 'fun-apply-type-c 'f 'NN 'RR m)
                               (fact 'fun-apply-type-c 'f 'NN 'RR p)
                               (mac 'rr-ms-dist)
                               (ulc-inst! (ulc-inst! inner m) p)
                               (ass)))))))))))))))
 (fact 'rr-complete)
 (fact 'complete-cauchy-converges 'RR-MS 'f)
 (ass)))
(qed 'rr-cauchy-converges)
(topic! 'rr-cauchy-converges 'analysis)
(alias! 'rr-cauchy-converges "a real sequence Cauchy in the abs metric converges")
