;;; theorem-library/seq-limit-core.scm -- THE LIMIT OF A REAL SEQUENCE AS A
;;; TERM (SEQ-LIMIT), its three characterising theorems, the TAIL bound
;;; rr-limit-tail-abs-le, and rr-cauchy-converges.
;;;
;;; SPLIT OUT OF theorem-library/seq-limit.scm ON 2026-09-14, for load order.
;;; seq-limit.scm used to hold seven results in one file: two limit laws in
;;; transfer form (rr-limit-scale, rr-limit-sub) and the five below.  The two
;;; laws cite limit-arithmetic (rr-limit-add) and rr-null-scale (rr-scale-eps),
;;; which load late; the five cite nothing later than rr-complete-proof and
;;; metric-limit-unique (rr-limit-unique).  `unif-cauchy-has-uniform-limit'
;;; (theorem-library/unif-cauchy-limit.scm) needs SEQ-LIMIT, seq-limit-in-rr,
;;; seq-limit-converges-to, rr-limit-tail-abs-le and rr-cauchy-converges and
;;; must itself precede ascoli-bridge, ~140 load entries above where
;;; seq-limit.scm sits.  So the five moved up, into this file, and the two laws
;;; stayed where they were.  Their section labels (L3-L7) are kept from the
;;; original so that the two files still read as one numbered sequence.
;;;
;;; The design argument for SEQ-LIMIT -- why it is TOTAL (an IF with 0 as the
;;; fallback) rather than the bare description `IOTA lm_. CONVERGES-TO(...)',
;;; and why no typing conjunct is needed inside the IOTA -- is at the head of
;;; seq-limit.scm and is not repeated here.  In one line: the fallback makes
;;; `seq-limit-in-rr' UNCONDITIONAL, so the term may sit in the body of a
;;; VNB-LAMBDA over a domain larger than the set where the sequence converges.
;;;
;;; WHAT IS HERE, all `modulo 0':
;;;
;;;   SEQ-LIMIT(f)              = IF CONVERGES(RR-MS,f) THEN IOTA lm_. ... ELSE 0
;;;   seq-limit-converges-to    CONVERGES(RR-MS,f)  =>  CONVERGES-TO(RR-MS, f, SEQ-LIMIT(f))
;;;   seq-limit-in-rr           SEQ-LIMIT(f) in RR, for EVERY f
;;;   seq-limit-value           CONVERGES-TO(RR-MS,f,lv)  =>  SEQ-LIMIT(f) = lv
;;;   rr-limit-tail-abs-le      |f(k) - v| <= c for k >= N,  f -> lv  =>  |lv - v| <= c
;;;   rr-cauchy-converges       Cauchy in the abs/eps language  =>  CONVERGES(RR-MS, f)
;;;
;;; Loads after rr-complete-proof (rr-complete), metric-limit-unique
;;; (rr-limit-unique -- MOVED UP beside rr-complete-proof the same day, for
;;; this file), rr-metric-space-proof (rr-is-metric-space), rr-ms-dist,
;;; rr-abs-basics (rr-abs-closed, rr-abs-sub-sym, rr-abs-triangle-c),
;;; rr-le-all-pos (rr-le-all-pos-nonpos), rr-max-basics / rr-min-basics
;;; (rr-le-max-left/right, nn-max-closed), nn-order-basics (nn-in-rr),
;;; binary-minus-laws (rr-sub-in-rr), fun-apply-type-proof (fun-apply-type-c),
;;; metric-completeness (CONVERGES, CONVERGES-TO, IS-CAUCHY-SEQ,
;;; complete-cauchy-converges) and driver-kit.  Cited by unif-cauchy-limit
;;; (directly below), recip-star, cauchy-criterion-left/-right,
;;; antiderivable-uniform-limit and c-int-oriented -- all of which load later.
;;;
;;; HELPERS.  Every theorem-library file loads into its own environment, so a
;;; helper defined in seq-limit.scm is invisible here.  The helpers below are
;;; COPIES of the ones the moved block used there, names unchanged (the `sq-'
;;; prefix is shared with seq-limit.scm, which is harmless across two
;;; environments and keeps the proof text identical to what it was).  The
;;; `ulc-' trio and `sq-idx' / `sq-ineq' were used ONLY by L6 and L7, so they
;;; are gone from seq-limit.scm rather than duplicated; the rest remain there
;;; too because rr-limit-scale / rr-limit-sub use them.
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
