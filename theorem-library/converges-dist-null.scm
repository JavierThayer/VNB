;;; converges-dist-null.scm -- CONVERGENCE IN A METRIC SPACE IS A NULL
;;; SEQUENCE OF REAL DISTANCES, proven both ways:
;;;
;;;   converges-iff-dist-null
;;;       CONVERGES-TO(t, f, L)
;;;         iff  CONVERGES-TO(RR-MS, (VNB-LAMBDA j_ NN ((DIST t)(f j_) L)), 0)
;;;
;;; THE BRIDGE TWO LANES WERE MISSING.  Everything the tree can prove about
;;; real null sequences -- `dominated-null-series', `rr-null-sum',
;;; `rr-null-scale', `rr-limit-add' -- speaks about FUN(NN,RR) and about 0.
;;; Everything the product-metric and c-metric statements say -- and both
;;; `product-convergence-coordinatewise' and the convergence equivalence for
;;; C-METRIC are of this form -- speaks about CONVERGES-TO in a metric space.
;;; Nothing crossed between them, so a coordinate hypothesis could not be fed
;;; into a series argument and the series conclusion could not be converted
;;; back.  `product-convergence-coordinatewise' needs the crossing TWICE, once
;;; in each direction, which is why the equivalence is stated as an IFF rather
;;; than as the one implication a particular caller happens to want.
;;;
;;; BOTH SIDES UNFOLD TO THE SAME eps/N CLAUSE and the proof is the two-line
;;; observation that makes them the same clause:
;;;
;;;     (DIST RR-MS)(d, 0)  =  abs(d - 0)  =  abs(d)  =  d     for d >= 0,
;;;
;;; i.e. `rr-ms-dist', one `crs', and `rr-abs-of-nonneg' standing on
;;; `metric-pos'.  There is no epsilon bookkeeping at all: the SAME threshold
;;; works in both directions, so neither branch halves anything or takes a MAX.
;;;
;;; THE BETA RULE IS A THEOREM, NOT A MACETE, AND THAT IS THE ONE MECHANICAL
;;; FINDING.  `dist-seq-apply' is proved exactly as `series-partial-sum-seq-apply'
;;; is (one `lam-b' with the index already typed, then `qrfl') -- but unlike it,
;;; it CANNOT BE APPLIED WITH `mac'.  Its left-hand side is
;;;
;;;     ((VNB-LAMBDA j_ NN ((DIST t) (f j_) lv)) n_)
;;;
;;; in which the schema variable `f' stands in OPERATOR position, applied to
;;; the lambda's own bound variable; the matcher is first-order, so `mac'
;;; reports "macete not applicable" on a goal that is literally an instance of
;;; the pattern.  (`series-partial-sum-seq-apply' escapes this because its `f'
;;; is an ARGUMENT of SERIES-PARTIAL-SUM, never a head.)  The route that works
;;; is to INSTANTIATE it -- `(fact 'dist-seq-apply t f lv n_)' does no matching
;;; at all -- and then `subst', which accepts a `==' as readily as a `='
;;; (pi-eq-subst!, primitive-inferences.scm:481).
;;;
;;; And because `subst' rewrites the GOAL only, the BACKWARD direction rewrites
;;; the goal INTO the hypothesis rather than the hypothesis into the goal: it
;;; establishes (= (DIST t)(f n_) lv   (DIST RR-MS)(lambda(n_), 0)) on a side
;;; branch and substitutes with that.  Rewriting the hypothesis would have
;;; wanted `mac-h', which is the door that is shut.
;;;
;;; WHAT IT COSTS.  `modulo {metric-dist-real}' [trust: well-known] throughout
;;; -- the one asserted support of structure-library/metric-space.scm, that a
;;; distance is a real number, which every metric estimate in the tree already
;;; pays (bdd-metric-convergence.scm cites it five times).  Nothing else: the
;;; beta rule `dist-seq-apply' is `modulo 0'.
;;;
;;; Loads after theorem-library/bdd-metric-convergence (the same neighbourhood,
;;; and the file whose driver this one follows), metric-space (metric-pos,
;;; metric-dist-real), metric-completeness (CONVERGES-TO), rr-ms-dist,
;;; rr-abs-basics (rr-abs-of-nonneg), fun-apply-type-proof (fun-apply-type-c),
;;; `prop' and driver-kit (dk-lam-t!).

;;; ---- file-local driver helpers (the `cdn-' prefix) -------------------
;;; The prefix is checked against the tree: a file-local `la-find' would rebind
;;; linear-arith.scm's `la-find', which `ineq' calls -- and `clobber-guard'
;;; does not see a procedure replaced by a procedure.

(define (cdn-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cdn-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (cdn-fvs forms) (apply append (map free-vars forms)))

(define (cdn-skolem! ex)
  (let* ((fv0 (cdn-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (cdn-fvs (dk-asms)))))
      (if (null? fresh) (error "cdn-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

(define (cdn-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "cdn-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (cdn-di-landed-1!)
  (let ((new (cdn-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "cdn-di-landed-1!: expected 1 landing"
               (map expression->string new)))))

(define (cdn-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cdn-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (cdn-peel-to! head)
  (let lp ((k 0))
    (if (and (< k 14) (not (eq? (car (dk-goal)) head))) (begin (di) (lp (+ k 1))))))

(define (cdn-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; The inner (FORALL n_ ... (<= thr n_) => ...) of a skolemized eps-N clause,
;;; discriminated on its THRESHOLD.
(define (cdn-inner thr)
  (cdn-find thr (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                 (let ((b (caddr a)))
                                   (and (pair? b) (eq? (car b) 'IMPLIES)
                                        (dk-contains? (caddr b) thr)))))))

;;; abs(d - 0) = d for a nonnegative real d -- the whole content of the
;;; equivalence, isolated.  Wants (IN d RR) and (<= 0 d) in the context.
(define (cdn-abs-zero! d)
  (have! (list '= (list 'abs (list '- d 0)) d)
    (lambda ()
      (have! (list '= (list '- d 0) d) (lambda () (crs)))
      (subst (list '= (list '- d 0) d))
      (fact 'rr-abs-of-nonneg d)
      (ass))))

(define cdn-lam '(VNB-LAMBDA j_ NN ((DIST t) (f j_) lv)))

;;; =====================================================================
;;; B1.  dist-seq-apply -- the beta rule of the distance sequence.
;;; `series-partial-sum-seq-apply's twin: the index is typed by the guard, so
;;; one `lam-b' owes nothing, and `==' rather than `=' because the reduction
;;; carries no definedness claim of its own.
;;; =====================================================================

(sp (make-wff (list 'FORALL 't (list 'FORALL 'f (list 'FORALL 'lv
   (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
     (list '== (list cdn-lam 'n_) '((DIST t) (f n_) lv)))))))))
(cdn-peel-to! '==)
(lam-b)
(qrfl)
(qed 'dist-seq-apply)
(topic! 'dist-seq-apply 'analysis)
(alias! 'dist-seq-apply "the distance sequence at an index")

;;; =====================================================================
;;; B2.  dist-seq-in-fun -- and it is a real sequence.  `dk-lam-t!' because
;;; `lam-t' opens TWO leaves and the sethood of NN is the second.
;;; =====================================================================

(sp (make-wff (list 'FORALL 't (list 'IMPLIES '(IS-METRIC-SPACE t)
   (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN NN (PTS t)))
     (list 'FORALL 'lv (list 'IMPLIES '(IN lv (PTS t))
       (list 'IN cdn-lam '(FUN NN RR))))))))))
(cdn-peel-to! 'IN)
(dk-lam-t!)
(define cdn-j (cadr (cdn-di-landed-1!)))
(fact 'fun-apply-type-c 'f 'NN '(PTS t) cdn-j)
(fact 'metric-dist-real 't (list 'f cdn-j) 'lv)
(ass)
(qed 'dist-seq-in-fun)
(topic! 'dist-seq-in-fun 'analysis)
(alias! 'dist-seq-in-fun "the distance sequence is a real sequence")

;;; =====================================================================
;;; F.  converges-dist-null-fwd -- convergence makes the distances null.
;;; Same threshold; the estimate is rewritten, not re-derived.
;;; =====================================================================

(sp (make-wff (list 'FORALL 't (list 'IMPLIES '(IS-METRIC-SPACE t)
  (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN NN (PTS t)))
    (list 'FORALL 'lv (list 'IMPLIES '(IN lv (PTS t))
      (list 'IMPLIES '(CONVERGES-TO t f lv)
            (list 'CONVERGES-TO 'RR-MS cdn-lam 0))))))))))
(cdn-peel-to! 'CONVERGES-TO)
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO t f lv)))
                           (lambda (a) (eq? (car a) 'AND))))
(define cdnf-tail (cdn-find 'tail (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                   (dk-contains? a 'POS-RR)))))
(fact 'rr-is-metric-space)
(fact 'dist-seq-in-fun 't 'f 'lv)
(fact 'rr-zero-in)
(mac 'converges-to)
(cdn-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IS-METRIC-SPACE) (ass))
           ((eq? (car g) 'IN) (slot 'PTS) (ass))
           (else
            (let* ((eps (cadr (cdn-di-landed-1!)))
                   (nex (dk-deepest (lambda () (inst+ cdnf-tail eps))))
                   (bigN (cdn-skolem! nex))
                   (inner (cdn-inner bigN)))
              (cdn-pos-in-rr! eps)
              (ew bigN)
              (cdn-and!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (let ((n_ (cadr (cdn-di-landed-1!))))
                       (cdn-di-landed!)             ; the (<= bigN n_) hypothesis
                       (inst+ inner n_)
                       (fact 'fun-apply-type-c 'f 'NN '(PTS t) n_)
                       (let ((d (list '(DIST t) (list 'f n_) 'lv)))
                         (fact 'metric-dist-real 't (list 'f n_) 'lv)
                         (fact 'metric-pos 't (list 'f n_) 'lv)
                         ;; `mac' cannot fire this one -- see the header.
                         (fact 'dist-seq-apply 't 'f 'lv n_)
                         (subst (list '== (list cdn-lam n_) d))
                         (mac 'rr-ms-dist)          ; arguments typed above
                         (cdn-abs-zero! d)
                         (subst (list '= (list 'abs (list '- d 0)) d))
                         (ass))))))))))))
(qed 'converges-dist-null-fwd)
(topic! 'converges-dist-null-fwd 'analysis)
(alias! 'converges-dist-null-fwd
        "a convergent sequence has null distances to its limit")

;;; =====================================================================
;;; B.  converges-dist-null-bwd -- and back.  The goal is rewritten into the
;;; hypothesis, because `subst' works on GOALS and the beta rule is not a
;;; usable macete.
;;; =====================================================================

(sp (make-wff (list 'FORALL 't (list 'IMPLIES '(IS-METRIC-SPACE t)
  (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN NN (PTS t)))
    (list 'FORALL 'lv (list 'IMPLIES '(IN lv (PTS t))
      (list 'IMPLIES (list 'CONVERGES-TO 'RR-MS cdn-lam 0)
            '(CONVERGES-TO t f lv))))))))))
(cdn-peel-to! 'CONVERGES-TO)
(dk-split! (dk-landed-find
            (lambda () (mac-h 'converges-to (list 'CONVERGES-TO 'RR-MS cdn-lam 0)))
            (lambda (a) (eq? (car a) 'AND))))
(define cdnb-tail (cdn-find 'tail (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                   (dk-contains? a 'POS-RR)))))
(fact 'rr-zero-in)
(mac 'converges-to)
(cdn-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IS-METRIC-SPACE) (ass))
           ((eq? (car g) 'IN) (ass))
           (else
            (let* ((eps (cadr (cdn-di-landed-1!)))
                   (nex (dk-deepest (lambda () (inst+ cdnb-tail eps))))
                   (bigN (cdn-skolem! nex))
                   (inner (cdn-inner bigN)))
              (cdn-pos-in-rr! eps)
              (ew bigN)
              (cdn-and!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (let ((n_ (cadr (cdn-di-landed-1!))))
                       (cdn-di-landed!)
                       (inst+ inner n_)
                       (fact 'fun-apply-type-c 'f 'NN '(PTS t) n_)
                       (let ((d (list '(DIST t) (list 'f n_) 'lv)))
                         (fact 'metric-dist-real 't (list 'f n_) 'lv)
                         (fact 'metric-pos 't (list 'f n_) 'lv)
                         (fact 'dist-seq-apply 't 'f 'lv n_)
                         (have! (list '= d (list '(DIST RR-MS) (list cdn-lam n_) 0))
                           (lambda ()
                             (subst (list '== (list cdn-lam n_) d))
                             (mac 'rr-ms-dist)
                             (cdn-abs-zero! d)
                             (subst (list '= (list 'abs (list '- d 0)) d))
                             (rfl)))
                         (subst (list '= d (list '(DIST RR-MS) (list cdn-lam n_) 0)))
                         (ass))))))))))))
(qed 'converges-dist-null-bwd)
(topic! 'converges-dist-null-bwd 'analysis)
(alias! 'converges-dist-null-bwd
        "null distances to a point make the sequence converge to it")

;;; =====================================================================
;;; The IFF, assembled by `prop' -- which treats both CONVERGES-TO atoms as
;;; opaque, so the assembly is pure propositional logic and costs no trust.
;;; =====================================================================

(sp (make-wff (list 'FORALL 't (list 'IMPLIES '(IS-METRIC-SPACE t)
  (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN NN (PTS t)))
    (list 'FORALL 'lv (list 'IMPLIES '(IN lv (PTS t))
      (list 'IFF '(CONVERGES-TO t f lv)
            (list 'CONVERGES-TO 'RR-MS cdn-lam 0))))))))))
(cdn-peel-to! 'IFF)
(fact 'converges-dist-null-fwd 't 'f 'lv)
(fact 'converges-dist-null-bwd 't 'f 'lv)
(prop)
(qed 'converges-iff-dist-null)
(topic! 'converges-iff-dist-null 'analysis)
(alias! 'converges-iff-dist-null
        "a sequence converges exactly when its distances to the limit are null")
