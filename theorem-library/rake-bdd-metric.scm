;;; rake-bdd-metric.scm -- the three asserted leaves still on the bill of
;;; `metrizable-iff-bounded-metrizable' (theorem-library/metrizable-bounded-proof.scm),
;;; PROVEN.  Statements copied VERBATIM from their support sites:
;;;
;;;   metrizable-has-metric-top            structure-library/top-space.scm:159
;;;   bdd-metric-is-bounded-metric-space   structure-library/bounded-metric.scm:60
;;;   bdd-metric-preserves-metric-top      structure-library/bounded-metric.scm:69
;;;
;;; L1 is the METRIZABLE-TOP-SPACE law read through the functor's own name:
;;; the law's tuple [pts(md), {u in power(pts md) : is-open(md,u)}] is literally
;;; what `mac 'metric-top' produces, so the proof is skolemize + one `subst'.
;;;
;;; L2 is 1 as the bound: `bdd-metric-bounded' says every rho-distance is < 1.
;;;
;;; L3 is the topological content, and it goes through the BALLS, not through
;;; `bdd-metric-id-bicontinuous' + `continuous-implies-open-preimage' (the route
;;; the warrant describes).  That route needs PREIMAGE(s, id, U) == U, which is
;;; a set equation under a beta redex inside a SEP; the ball route needs no set
;;; surgery at all, because the two open-set conditions differ only in the
;;; radius:
;;;
;;;   rho <= d                    (bdd-metric-dist-le)     so BALL(d,y,r) is
;;;                               inside BALL(rho,y,r)     -- the radius is kept;
;;;   rho(y,z) <= r/(1+r) => d(y,z) <= r
;;;                               (bdd-metric-dist-reflect) so BALL(rho,y,r/(1+r))
;;;                               is inside BALL(d,y,r).
;;;
;;; Strictness in the second direction is the one piece neither lemma gives:
;;; `bdd-metric-dist-reflect' delivers only d(y,z) <= r.  It is recovered from
;;; d(y,z) = r  =>  rho(y,z) = r/(1+r)  (bdd-metric-distance, two `subst's),
;;; against the strict half of ball membership.
;;;
;;; So two implications are proven first -- `bdd-metric-open-fwd' and
;;; `bdd-metric-open-bwd' -- and METRIC-TOP equality is then
;;; class-extensionality on the two separations, the carriers already being
;;; equal by `bdd-metric-carrier'.
;;;
;;; WINDOW.  lo = theorem-library/bdd-metric-convergence (bdd-metric-dist-le,
;;; bdd-metric-dist-reflect); everything else is earlier (rake-balls,
;;; bdd-metric-basics, bdd-metric-carrier/-distance, pos-rr-bridges,
;;; rr-recip-order, subset-lemmas, op-typing).  hi =
;;; theorem-library/metrizable-bounded-proof, the only citer of the three.
;;; No late tactic is used (no `contra', `prep', `ineq-supply').
;;;
;;; Helper prefix: rbm-.

;;; ---- file-local kit ---------------------------------------------------

;; close a (nested) AND goal leaf by leaf
(define (rbm-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (rbm-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (rbm-and2! a b) (have! (list 'AND a b) (lambda () (rbm-and! (lambda () (ass))))))

;; have! the right-nested AND of context facts F1 ... Fn; return it
(define (rbm-conj! . fs)
  (let loop ((l fs))
    (if (null? (cdr l))
        (car l)
        (let ((f (list 'AND (car l) (loop (cdr l)))))
          (have! f (lambda () (rbm-and! (lambda () (ass)))))
          f))))

(define (rbm-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rbm-idx: not in context" form))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (rbm-ineq . forms) (apply ineq (map rbm-idx forms)))

;; IN x RR, 0 <= x, NOT (= 0 x) from POS-RR x, keeping POS-RR x
(define (rbm-pos-parts! x)
  (for-each
   (lambda (part)
     (have! part (lambda ()
                   (mac-h 'pos-rr (list 'POS-RR x))
                   (dk-split! (list 'AND (list 'IN x 'RR)
                                    (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
                   (ass))))
   (list (list 'IN x 'RR) (list '<= 0 x) (list 'NOT (list '= 0 x)))))

;; the reciprocal block for 1+t: needs (IN t RR), (<= 0 t), 0, 1 and 0 < 1
(define (rbm-one-plus! t)
  (let ((one+t (list '+ 1 t)))
    (rbm-and2! '(IN 1 RR) (list 'IN t 'RR))
    (fact 'rr-add-closed 1 t)
    (have! (list '<= 1 one+t) (lambda () (rbm-ineq (list '<= 0 t))))
    (rbm-and2! '(< 0 1) (list '<= 1 one+t))
    (fact 'rr-lt-le-trans 0 1 one+t)
    (fact 'rr-pos-ne-zero one+t)
    (rbm-and2! (list 'IN one+t 'RR) (list 'NOT (list '= one+t 0)))
    (fact 'rr-recip-closed one+t)
    (fact 'rr-recip-inverse one+t)
    (have! (list '<= 0 one+t) (lambda () (rbm-ineq (list '<= 0 t))))))

;; the eigenvariable of the landed guard (IN v uu)
(define (rbm-pt-of landed tag)
  (cadr (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) tag)))
                    landed)))

;; the eigenvariable of the landed guard (IN v (BALL ...))
(define (rbm-ball-pt-of landed)
  (cadr (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                     (pair? (caddr f)) (eq? (car (caddr f)) 'BALL)))
                    landed)))

;;; =====================================================================
;;; L1.  metrizable-has-metric-top
;;; =====================================================================

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIZABLE-TOP-SPACE s)
     (FORSOME md (AND (IS-METRIC-SPACE md)
                      (== (METRIC-TOP md) s)))))))
(dk-peel!)
(define rbm-l1-unf
  (dk-landed-1 (lambda () (mac-h 'is-metrizable-top-space-def
                                 '(IS-METRIZABLE-TOP-SPACE s)))))
(define rbm-l1-ex (find-first (dk-head? 'FORSOME) (dk-split! rbm-l1-unf)))
(define rbm-w (dk-skolem! rbm-l1-ex))
(define rbm-l1-eq
  (find-first (lambda (f) (and (pair? f) (eq? (car f) '==) (eq? (cadr f) 's)))
              (dk-asms)))
(ew rbm-w)
(for-each (lambda (n)
            (dk-focus! n)
            (if (eq? (car (dk-goal)) 'IS-METRIC-SPACE)
                (ass)
                (begin (mac 'metric-top) (subst rbm-l1-eq) (qrfl))))
          (dk-opened (lambda () (di))))
(qed 'metrizable-has-metric-top)

;;; =====================================================================
;;; L2.  bdd-metric-is-bounded-metric-space -- 1 is the bound
;;; =====================================================================

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IS-BOUNDED-METRIC-SPACE (BDD-METRIC s))))))
(dk-peel!)
(fact 'bdd-metric-is-metric-space 's)
(mac 'is-bounded-metric-space)
(mac 'bdd-metric-carrier)
(for-each
 (lambda (n)
   (dk-focus! n)
   (if (eq? (car (dk-goal)) 'IS-METRIC-SPACE)
       (ass)
       (begin
         (ew 1)
         (for-each
          (lambda (m)
            (dk-focus! m)
            (if (eq? (car (dk-goal)) 'IN)
                (begin (fact 'rr-one-in) (ass))
                (begin
                  (dk-peel!)
                  (let* ((app (cadr (dk-goal)))
                         (xx (cadr app))
                         (yy (caddr app)))
                    (fact 'bdd-metric-bounded 's xx yy)
                    (mac-h '< (list '< app 1))
                    (prop)))))
          (dk-opened (lambda () (di)))))))
 (dk-opened (lambda () (di))))
(qed 'bdd-metric-is-bounded-metric-space)

;;; =====================================================================
;;; L3a.  bdd-metric-open-bwd -- rho-open implies d-open, SAME radius
;;; =====================================================================

(define rbm-b-tail #f)

(define (rbm-b-subset! yy rr)
  (mac 'subset-def)
  (let* ((landed (dk-peel!))
         (zz  (rbm-ball-pt-of landed))
         (dd  (list (list 'DIST 's) yy zz))
         (rho (list (list 'DIST '(BDD-METRIC s)) yy zz)))
    (dk-split! (dk-landed-find
                (lambda () (mac-h 'ball-membership (list 'IN zz (list 'BALL 's yy rr))))
                (dk-head? 'AND)))
    (have! (list 'IN zz '(PTS (BDD-METRIC s)))
           (lambda () (mac 'bdd-metric-carrier) (ass)))
    (fact 'metric-dist-real 's yy zz)
    (fact 'bdd-metric-dist-le 's yy zz)
    (fact 'rr-pos-rr-in-rr rr)
    (have! (list '< dd rr) (lambda () (mac '<) (rbm-and! (lambda () (ass)))))
    (rbm-conj! (list 'IN zz '(PTS (BDD-METRIC s)))
               (list 'IN dd 'RR)
               (list 'IN rr 'RR)
               (list '<= rho dd)
               (list '< dd rr))
    (fact 'ball-mem-from-le '(BDD-METRIC s) yy zz dd rr)
    (fact 'subset-mem-fwd (list 'BALL '(BDD-METRIC s) yy rr) 'uu zz)
    (ass)))

(define (rbm-b-tail!)
  (let* ((landed (dk-peel!))
         (yy (rbm-pt-of landed 'uu))
         (ex (dk-apply! rbm-b-tail yy))
         (rr (dk-skolem! ex)))
    (fact 'subset-mem-fwd 'uu '(PTS s) yy)
    (have! (list 'IN yy '(PTS (BDD-METRIC s)))
           (lambda () (mac 'bdd-metric-carrier) (ass)))
    (ew rr)
    (rbm-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'POS-RR) (ass) (rbm-b-subset! yy rr))))))

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL uu (IMPLIES (IS-OPEN (BDD-METRIC s) uu) (IS-OPEN s uu)))))))
(dk-peel!)
(fact 'bdd-metric-is-metric-space 's)
(define rbm-b-parts
  (dk-split! (dk-landed-find (lambda () (mac-h 'is-open '(IS-OPEN (BDD-METRIC s) uu)))
                             (dk-head? 'AND))))
(set! rbm-b-tail (find-first (dk-head? 'FORALL) rbm-b-parts))
(dk-landed-1 (lambda () (mac-h 'bdd-metric-carrier
                               (find-first (dk-head? 'SUBSET) rbm-b-parts))))
(mac 'is-open)
(rbm-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IS-METRIC-SPACE) (ass))
           ((eq? (car g) 'SUBSET) (ass))
           (#t (rbm-b-tail!))))))
(qed 'bdd-metric-open-bwd)
(gloss! 'bdd-metric-open-bwd
  "Every set open for the bounded metric d/(1+d) is open for d: the same radius
   works, because d/(1+d) <= d.")
(topic! 'bdd-metric-open-bwd 'topology)

;;; =====================================================================
;;; L3b.  bdd-metric-open-fwd -- d-open implies rho-open, radius r/(1+r)
;;; =====================================================================

(define rbm-a-tail #f)

(define (rbm-a-subset! yy rr del)
  (mac 'subset-def)
  (let* ((landed (dk-peel!))
         (zz  (rbm-ball-pt-of landed))
         (dd  (list (list 'DIST 's) yy zz))
         (rho (list (list 'DIST '(BDD-METRIC s)) yy zz))
         (imp (list 'IMPLIES (list '= dd rr) (list '= rho del))))
    (dk-split! (dk-landed-find
                (lambda () (mac-h 'ball-membership
                                  (list 'IN zz (list 'BALL '(BDD-METRIC s) yy del))))
                (dk-head? 'AND)))
    (mac-h 'bdd-metric-carrier (list 'IN zz '(PTS (BDD-METRIC s))))
    (fact 'metric-dist-real 's yy zz)
    (fact 'bdd-metric-dist-reflect 's yy zz rr)
    (have! imp
      (lambda ()
        (di)
        (fact 'bdd-metric-distance 's yy zz)
        (subst (list '= rho (list '/ dd (list '+ 1 dd))))
        (subst (list '= dd rr))
        (rfl)))
    (have! (list 'NOT (list '= dd rr))
      (lambda ()
        (dk-only! imp (list 'NOT (list '= rho del)))
        (prop)))
    (have! (list 'IN zz (list 'BALL 's yy rr))
           (lambda () (mac 'ball-membership) (rbm-and! (lambda () (ass)))))
    (fact 'subset-mem-fwd (list 'BALL 's yy rr) 'uu zz)
    (ass)))

(define (rbm-a-tail!)
  (let* ((landed (dk-peel!))
         (yy  (rbm-pt-of landed 'uu))
         (ex  (dk-apply! rbm-a-tail yy))
         (rr  (dk-skolem! ex))
         (den (list '+ 1 rr))
         (rcp (list 'recip den))
         (prd (list '* rr rcp))
         (del (list '/ rr den)))
    (rbm-pos-parts! rr)
    (rbm-one-plus! rr)
    (fact 'rr-recip-pos den)
    (rbm-and2! (list '<= 0 rr) (list 'NOT (list '= 0 rr)))
    (fact 'rr-le-ne-lt 0 rr)
    (fact 'rr-mul-pos rr rcp)
    (rbm-and2! (list 'IN rr 'RR) (list 'IN rcp 'RR))
    (fact 'rr-mul-closed rr rcp)
    (have! (list 'IN del 'RR) (lambda () (mac 'binary-divide-def) (ass)))
    (have! (list 'POS-RR del)
      (lambda ()
        (mac 'binary-divide-def)
        (dk-split! (dk-landed-find (lambda () (mac-h '< (list '< 0 prd)))
                                   (dk-head? 'AND)))
        (mac 'pos-rr)
        (rbm-and! (lambda () (ass)))))
    (fact 'subset-mem-fwd 'uu '(PTS s) yy)
    (ew del)
    (rbm-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'POS-RR) (ass) (rbm-a-subset! yy rr del))))))

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL uu (IMPLIES (IS-OPEN s uu) (IS-OPEN (BDD-METRIC s) uu)))))))
(dk-peel!)
(fact 'bdd-metric-is-metric-space 's)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(define rbm-a-parts
  (dk-split! (dk-landed-find (lambda () (mac-h 'is-open '(IS-OPEN s uu)))
                             (dk-head? 'AND))))
(set! rbm-a-tail (find-first (dk-head? 'FORALL) rbm-a-parts))
(mac 'is-open)
(mac 'bdd-metric-carrier)
(rbm-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IS-METRIC-SPACE) (ass))
           ((eq? (car g) 'SUBSET) (ass))
           (#t (rbm-a-tail!))))))
(qed 'bdd-metric-open-fwd)
(gloss! 'bdd-metric-open-fwd
  "Every set open for a metric d is open for the bounded metric d/(1+d):
   the d-ball of radius r contains the rho-ball of radius r/(1+r).")
(topic! 'bdd-metric-open-fwd 'topology)

;;; =====================================================================
;;; L3.  bdd-metric-preserves-metric-top
;;; =====================================================================

(define rbm-sep1 #f)
(define rbm-sep2 #f)

(define (rbm-l3-ext!)
  (dk-peel!)
  (let ((v (cadr (cadr (dk-goal)))))
    (for-each
     (lambda (n)
       (dk-focus! n)
       (let* ((tgt (caddr (dk-goal)))
              (bwd? (equal? tgt rbm-sep2))
              (src (if bwd? rbm-sep1 rbm-sep2)))
         (for-each (lambda (f) (if (eq? (car f) 'AND) (dk-split! f)))
                   (dk-landed (lambda () (sep-me (list 'IN v src)))))
         (for-each
          (lambda (k)
            (dk-focus! k)
            (if (eq? (car (dk-goal)) 'IN)
                (ass)
                (begin
                  (fact (if bwd? 'bdd-metric-open-bwd 'bdd-metric-open-fwd) 's v)
                  (ass))))
          (dk-opened (lambda () (sep-mi))))))
     (dk-opened (lambda () (di))))))

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (== (METRIC-TOP (BDD-METRIC s)) (METRIC-TOP s))))))
(dk-peel!)
(mac 'metric-top)
(mac 'bdd-metric-carrier)
(set! rbm-sep1 (caddr (cadr (dk-goal))))
(set! rbm-sep2 (caddr (caddr (dk-goal))))
(have! (list 'FORALL 'x (list 'IFF (list 'IN 'x rbm-sep1) (list 'IN 'x rbm-sep2)))
       (lambda () (rbm-l3-ext!)))
(fact 'class-extensionality rbm-sep1 rbm-sep2)
(subst (list '= rbm-sep1 rbm-sep2))
(qrfl)
(qed 'bdd-metric-preserves-metric-top)
