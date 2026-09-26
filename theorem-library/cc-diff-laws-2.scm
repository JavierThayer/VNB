;;; cc-diff-laws-2.scm -- the rest of the elementary theory of IS-CC-DIFF-AT,
;;; the derivative of a map RR -> CC (structure-library/cc-coords.scm).
;;; Continues theorem-library/cc-coords-laws.scm (batch 14-A), which defined the
;;; predicate coordinatewise and proved the transfer equivalence
;;; `cc-diff-at-iff-coords' and the three rules `cc-diff-at-sum',
;;; `cc-diff-at-real-mul' and `cc-diff-at-product'.
;;;
;;; Contents, in the order of the batch-14 brief:
;;;
;;;   (1) cc-diff-at-implies-continuous   differentiable at t => continuous at t
;;;   (2) cc-diff-at-const                a constant map has derivative 0
;;;   (3) cc-diff-at-cc-mul               a COMPLEX constant multiple
;;;   (4) cc-diff-at-difference           the difference rule
;;;   (5) cc-diff-at-unique               the derivative is unique
;;;   (6) cc-diff-at-chain-real           g o h for a REAL inner map h
;;;
;;; EVERY STATEMENT IS IN TRANSFER FORM, as cc-coords-laws.scm's are: the
;;; combined function is a PARAMETER of the theorem, tied to the combination by
;;; a pointwise equation, so that no statement mentions a VNB-LAMBDA and no
;;; consumer owes a beta-reduction under a binder.  (1) and (5) need no such
;;; parameter and are stated directly.
;;;
;;; THE SHAPE OF EVERY PROOF is the one cc-coords-laws.scm established: unfold
;;; the IS-CC-DIFF-AT hypotheses into their two coordinate IS-DIFF-ATs, rewrite
;;; the target derivative by the coordinate law of the operation
;;; (cc-re-sub / cc-re-real-mul / ...), run the REAL law on the coordinates, and
;;; carry the conclusion onto the wanted function with `diff-transfer-ptwise-eq'.
;;;
;;; WHAT IS NEW HERE, mechanically:
;;;
;;; * (1) is the ONE place where the space RR-MS has to be spoken of in the
;;;   `PTS' vocabulary: `cc-continuous-at-iff-coords' quantifies over a metric
;;;   space `s' and states every typing over PTS(s).  Instantiated at RR-MS its
;;;   hypotheses read (IN g (FUN (PTS RR-MS) CC)), which is the context's
;;;   (IN g (FUN RR CC)) one `slot 'PTS' away -- on the GOAL for a claim, and
;;;   through `slot-h' for the eigenvariable's typing inside the pointwise lane.
;;;
;;; * (3) does NOT redo the product rule coordinatewise.  A complex constant
;;;   multiple is the product with a CONSTANT FUNCTION, so (2) supplies
;;;   IS-CC-DIFF-AT of that function with derivative 0 and `cc-diff-at-product'
;;;   does the rest; all that is left is the arithmetic
;;;   c.L = L.c + g(t).0 in CC, one `crs' after the constant lambda's own beta.
;;;
;;; * (4) is the first consumer of `deriv-difference'
;;;   (theorem-library/deriv-difference.scm, the same batch): without it the
;;;   real coordinate of a difference would go through `deriv-scalar-mult' at
;;;   -1 and `deriv-sum', which is exactly the detour cc-coords-laws.scm:1226
;;;   records having had to take.
;;;
;;; * (6) needs the value of a COMPOSE term, which is `compose-apply' (PROVEN,
;;;   theorem-library/compose-apply-proof.scm); `deriv-chain' concludes about
;;;   (COMPOSE g f), and the transfer moves that onto the coordinate lambda of
;;;   the composite.  The derivative is k.L with k REAL and L complex, so the
;;;   coordinate laws it wants are cc-re-real-mul / cc-im-real-mul, not the
;;;   full product laws.
;;;
;;; NOT HERE, DELIBERATELY: the reciprocal and the quotient rule.  The brief
;;; forbids the route through `normed-field-mul-inverses' (an ASSERTED support:
;;; citing it would bill).  See the report for what a CC-specific route would
;;; need; nothing in this file depends on it.
;;;
;;; LOAD WINDOW.  lo = theorem-library/cc-coords-laws (cc-diff-at-iff-coords's
;;; siblings, cc-continuous-at-iff-coords, cc-re-add / -sub / -real-mul and the
;;; rest of the coordinate laws) and theorem-library/deriv-difference (the same
;;; batch), whichever is later; every other citation is far below --
;;; differentiation (deriv-const, derivative-unique, diff-implies-continuous),
;;; chain-rule (deriv-chain), compose-apply-proof (compose-apply),
;;; diff-transfer (diff-transfer-ptwise-eq), cc-real-imag (cc-re-im-of,
;;; real-part-in-rr), cc-metric-space-proof (cc-sub-in-cc), cc-complete-proof
;;; (cc-re-sub, cc-im-sub), rr-metric-space (rr-is-metric-space).  hi is
;;; unconstrained: nothing cites these names yet.  Concretely
;;; (scratchpad/window.py, 2026-09-21): lo = 3283, the load.scm line of
;;; "theorem-library/cc-coords-laws" -- and, once it is wired,
;;; theorem-library/deriv-difference, which window.py cannot see yet.  The
;;; proposed slot is the line immediately after "theorem-library/cc-coords-laws".
;;;
;;; Helper prefix: `cdl-'.

;;; =====================================================================
;;; File-local driver helpers.
;;; =====================================================================

(define (cdl-head e) (and (pair? e) (car e)))

(define (cdl-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cdl-find: no context formula" what))
          ((pred (car l)) (car l))
          (#t (loop (cdr l))))))

;;; the pointwise hypothesis of a transfer-form statement: the FORALL that
;;; mentions the combined function FN.
(define (cdl-ptw fn)
  (cdl-find (list 'pointwise fn)
    (lambda (x) (and (pair? x) (eq? (car x) 'FORALL) (dk-contains? x fn)))))

;;; unfold an IS-CC-DIFF-AT hypothesis into its five conjuncts
(define (cdl-unfold! form)
  (dk-split! (dk-landed-find (lambda () (mac-h 'is-cc-diff-at form))
                             (lambda (x) (eq? (car x) 'AND)))))

;;; the coordinate IS-DIFF-AT hypothesis of FN for the projection PROJ
(define (cdl-diff-of fn proj)
  (cdl-find (list 'diff-of fn proj)
    (lambda (x) (and (pair? x) (eq? (car x) 'IS-DIFF-AT)
                     (dk-contains? x fn) (dk-contains? x proj)))))

;;; (IN LAM (FUN RR RR)) for LAM = vnb-lambda(sv_, rr, PROJ(FN(sv_))).
(define (cdl-lam-in-fun! lam fn proj)
  (dk-have! (list 'IN lam '(FUN RR RR))
    (lambda ()
      (dk-lam-t!)
      (let ((v (cadr (car (dk-landed* (lambda () (di)))))))
        (fact 'fun-apply-type-c fn 'RR 'CC v)
        (fact (if (eq? proj 'real-part) 'real-part-in-rr 'imag-part-in-rr)
              (list fn v))
        (ass)))))

;;; =====================================================================
;;; (1) DIFFERENTIABLE IMPLIES CONTINUOUS.
;;;
;;; Both coordinate maps are differentiable at t, hence continuous at t
;;; (`diff-implies-continuous', Prop 2.4), hence g is continuous into CC-MS by
;;; the backward half of `cc-continuous-at-iff-coords' at s = RR-MS.  The
;;; coordinate lambdas are the SAME terms in both theorems -- IS-CC-DIFF-AT's
;;; definition builds them -- so no transfer is needed here, only the PTS(RR-MS)
;;; reading of the three typings and of the two pointwise equations.
;;; =====================================================================

(sp (make-wff "forall([g in fun(rr,cc), tv_ in rr, lv in cc],
     is-cc-diff-at(g, tv_, lv) implies is-continuous-at(rr-ms, cc-ms, g, tv_))"))
(dk-peel!)
(cdl-unfold! '(IS-CC-DIFF-AT g tv_ lv))

(define cdc-re  (cdl-diff-of 'g 'real-part))
(define cdc-im  (cdl-diff-of 'g 'imag-part))
(define cdc-rel (cadr cdc-re))                     ; lambda s. real-part(g(s))
(define cdc-iml (cadr cdc-im))                     ; lambda s. imag-part(g(s))

(fact 'rr-is-metric-space)
(fact 'diff-implies-continuous cdc-rel 'tv_ (cadddr cdc-re))
(fact 'diff-implies-continuous cdc-iml 'tv_ (cadddr cdc-im))
(dk-project! (list 'IN cdc-rel '(FUN RR RR)) 'IS-DIFF-AT cdc-re)
(dk-project! (list 'IN cdc-iml '(FUN RR RR)) 'IS-DIFF-AT cdc-im)

;;; the same three typings, read in the PTS(RR-MS) vocabulary the transfer wants
(dk-have! '(IN g (FUN (PTS RR-MS) CC)) (lambda () (slot 'PTS) (ass)))
(dk-have! (list 'IN cdc-rel '(FUN (PTS RR-MS) RR)) (lambda () (slot 'PTS) (ass)))
(dk-have! (list 'IN cdc-iml '(FUN (PTS RR-MS) RR)) (lambda () (slot 'PTS) (ass)))
(dk-have! '(IN tv_ (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))

;;; ... and the two pointwise equations, which are pure beta
(define (cdc-ptwise! lam proj)
  (dk-have! (list 'FORALL 'u_ (list 'IMPLIES '(IN u_ (PTS RR-MS))
              (list '= (list proj '(g u_)) (list lam 'u_))))
    (lambda ()
      (di)
      (slot-h 'PTS '(IN u_ (PTS RR-MS)))
      (fact 'fun-apply-type-c 'g 'RR 'CC 'u_)
      (fact (if (eq? proj 'real-part) 'real-part-in-rr 'imag-part-in-rr) '(g u_))
      (dk-lam-b!)
      (rfl))))
(cdc-ptwise! cdc-rel 'real-part)
(cdc-ptwise! cdc-iml 'imag-part)

(fact 'cc-continuous-at-iff-coords 'RR-MS 'g cdc-rel cdc-iml 'tv_)
(dk-have! (list 'AND (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS cdc-rel 'tv_)
                     (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS cdc-iml 'tv_)))
(prop)
(qed 'cc-diff-at-implies-continuous)
(topic! 'cc-diff-at-implies-continuous 'analysis)
(alias! 'cc-diff-at-implies-continuous
  "a differentiable CC-valued function of a real variable is continuous")

;;; =====================================================================
;;; (2) THE CONSTANT.
;;;
;;; Both coordinates of a constant map are constant, so `deriv-const' does the
;;; work twice; the only fact needed about 0 is that its two coordinates are 0,
;;; which is `cc-re-im-of' at 0 = 0 + 0.i.
;;; =====================================================================

(sp (make-wff "forall([cv in cc, g in fun(rr,cc), tv_ in rr],
     forall([x_ in rr], g(x_) = cv) implies
     is-cc-diff-at(g, tv_, 0))"))
(dk-peel!)
(define cdk-ptw (cdl-ptw 'g))
(fact 'cc-i-in)
(fact 'rr-zero-in)
(fact 'rr-subset-cc 0)
(have! '(= 0 (+ 0 (* 0 +i))) (lambda () (crs)))
(dk-split! (dk-fact! 'cc-re-im-of 0 0 0))          ; re(0) = 0, im(0) = 0
(fact 'real-part-in-rr 'cv)
(fact 'imag-part-in-rr 'cv)

(mac 'is-cc-diff-at)
(dk-conj-close!
 (lambda ()
   (let ((gl (dk-goal)))
     (if (eq? (cdl-head gl) 'IN)
         (ass)
         (let* ((lam  (cadr gl))
                (dl   (cadddr gl))
                (proj (if (dk-contains? gl 'real-part) 'real-part 'imag-part)))
           (subst (list '= dl 0))                  ; re(0) / im(0) -> 0
           (have! (list 'AND (list 'IN (list proj 'cv) 'RR) '(IN tv_ RR)))
           (let* ((res (dk-fact! 'deriv-const (list proj 'cv) 'tv_))
                  (cl  (cadr res)))                ; lambda x in RR. proj(cv)
             (cdl-lam-in-fun! lam 'g proj)
             (dk-have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                          (list '== (list lam 'x_) (list cl 'x_))))
               (lambda ()
                 (di)
                 (fact 'fun-apply-type-c 'g 'RR 'CC 'x_)
                 (dk-lam-b!)
                 (inst+ cdk-ptw 'x_)
                 (subst '(= (g x_) cv))
                 (qrfl)))
             (fact 'diff-transfer-ptwise-eq lam cl 'tv_ 0)
             (ass)))))))
(qed 'cc-diff-at-const)
(topic! 'cc-diff-at-const 'analysis)
(alias! 'cc-diff-at-const
  "a constant CC-valued function of a real variable has derivative zero")

;;; =====================================================================
;;; (3) MULTIPLICATION BY A COMPLEX CONSTANT.
;;;
;;; c.g is the product of g with the constant function at c, whose derivative
;;; is 0 by (2); `cc-diff-at-product' then gives the derivative
;;; L.c + g(t).0, and c.L = L.c + g(t).0 is one `crs' in CC after the constant
;;; lambda's own beta.  Nothing is redone coordinatewise.
;;; =====================================================================

(sp (make-wff "forall([cv in cc, g in fun(rr,cc), pd in fun(rr,cc), tv_ in rr, lv in cc],
     forall([x_ in rr], pd(x_) = cv * g(x_)) implies
     is-cc-diff-at(g, tv_, lv) implies
     is-cc-diff-at(pd, tv_, cv * lv))"))
(dk-peel!)
(define ccm-ptw (cdl-ptw 'pd))
(define ccm-const '(VNB-LAMBDA cdw_ RR cv))

(dk-have! (list 'IN ccm-const '(FUN RR CC))
  (lambda ()
    (dk-lam-t!)
    (di)
    (ass)))
(dk-have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR) (list '= (list ccm-const 'x_) 'cv)))
  (lambda () (di) (dk-lam-b!) (rfl)))
(fact 'cc-diff-at-const 'cv ccm-const 'tv_)        ; the constant map, derivative 0

(dk-have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
             (list '= '(pd x_) (list '* '(g x_) (list ccm-const 'x_)))))
  (lambda ()
    (di)
    (fact 'fun-apply-type-c 'g 'RR 'CC 'x_)
    (dk-lam-b!)
    (inst+ ccm-ptw 'x_)
    (subst '(= (pd x_) (* cv (g x_))))
    (crs)))
(define ccm-res (dk-fact! 'cc-diff-at-product 'g ccm-const 'pd 'tv_ 'lv 0))
(define ccm-val (cadddr ccm-res))                  ; lv * const(tv_) + g(tv_) * 0
(fact 'fun-apply-type-c 'g 'RR 'CC 'tv_)
(have! (list '= '(* cv lv) ccm-val) (lambda () (dk-lam-b!) (crs)))
(subst (list '= '(* cv lv) ccm-val))
(ass)
(qed 'cc-diff-at-cc-mul)
(topic! 'cc-diff-at-cc-mul 'analysis)
(alias! 'cc-diff-at-cc-mul
  "a complex multiple of a differentiable CC-valued function is differentiable")

;;; =====================================================================
;;; (4) THE DIFFERENCE RULE.  The mirror of `cc-diff-at-sum', with cc-re-sub /
;;; cc-im-sub in place of cc-re-add / cc-im-add and `deriv-difference' in place
;;; of `deriv-sum'.
;;; =====================================================================

(sp (make-wff "forall([g in fun(rr,cc), h in fun(rr,cc), sb_ in fun(rr,cc), tv_ in rr,
                       lv in cc, mv in cc],
     forall([x_ in rr], sb_(x_) = g(x_) - h(x_)) implies
     is-cc-diff-at(g, tv_, lv) implies
     is-cc-diff-at(h, tv_, mv) implies
     is-cc-diff-at(sb_, tv_, lv - mv))"))
(dk-peel!)
(define ccb-ptw (cdl-ptw 'sb_))
(cdl-unfold! '(IS-CC-DIFF-AT g tv_ lv))
(cdl-unfold! '(IS-CC-DIFF-AT h tv_ mv))
(fact 'cc-sub-in-cc 'lv 'mv)
(fact 'cc-re-sub 'lv 'mv)
(fact 'cc-im-sub 'lv 'mv)
(mac 'is-cc-diff-at)
(dk-conj-close!
 (lambda ()
   (let ((gl (dk-goal)))
     (if (eq? (cdl-head gl) 'IN)
         (ass)
         (let* ((lam  (cadr gl))
                (dl   (cadddr gl))
                (proj (if (dk-contains? gl 'real-part) 'real-part 'imag-part))
                (dg   (cdl-diff-of 'g proj))
                (dh   (cdl-diff-of 'h proj)))
           (subst (list '= dl (list '- (list proj 'lv) (list proj 'mv))))
           (let* ((res (dk-fact! 'deriv-difference (cadr dg) (cadr dh) 'tv_
                                 (cadddr dg) (cadddr dh)))
                  (sl  (cadr res)))
             (cdl-lam-in-fun! lam 'sb_ proj)
             (dk-have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                          (list '== (list lam 'x_) (list sl 'x_))))
               (lambda ()
                 (di)
                 (fact 'fun-apply-type-c 'g 'RR 'CC 'x_)
                 (fact 'fun-apply-type-c 'h 'RR 'CC 'x_)
                 (fact 'fun-apply-type-c 'sb_ 'RR 'CC 'x_)
                 (dk-lam-b!)
                 (inst+ ccb-ptw 'x_)
                 (subst '(= (sb_ x_) (- (g x_) (h x_))))
                 (fact (if (eq? proj 'real-part) 'cc-re-sub 'cc-im-sub)
                       '(g x_) '(h x_))
                 (subst (list '= (list proj '(- (g x_) (h x_)))
                              (list '- (list proj '(g x_)) (list proj '(h x_)))))
                 (qrfl)))
             (fact 'diff-transfer-ptwise-eq lam sl 'tv_ (cadddr res))
             (ass)))))))
(qed 'cc-diff-at-difference)
(topic! 'cc-diff-at-difference 'analysis)
(alias! 'cc-diff-at-difference
  "the difference of two differentiable CC-valued functions is differentiable")

;;; =====================================================================
;;; (5) UNIQUENESS OF THE DERIVATIVE.
;;;
;;; The two coordinate lambdas of g do not depend on the derivative, so the two
;;; hypotheses give the SAME lambda two real derivatives; `derivative-unique'
;;; (Prop 2.7) identifies them coordinate by coordinate, and
;;; `cc-re-im-decompose' rebuilds the two complex numbers from their equal
;;; coordinates.
;;; =====================================================================

(sp (make-wff "forall([g in fun(rr,cc), tv_ in rr, lv in cc, mv in cc],
     is-cc-diff-at(g, tv_, lv) implies
     is-cc-diff-at(g, tv_, mv) implies
     lv = mv)"))
(dk-peel!)
(cdl-unfold! '(IS-CC-DIFF-AT g tv_ lv))
(cdl-unfold! '(IS-CC-DIFF-AT g tv_ mv))
(define (cdu-agree! proj)
  (let* ((dl (cdl-find (list 'diff-l proj)
               (lambda (x) (and (pair? x) (eq? (car x) 'IS-DIFF-AT)
                                (dk-contains? x proj) (dk-contains? x 'lv)))))
         (dm (cdl-find (list 'diff-m proj)
               (lambda (x) (and (pair? x) (eq? (car x) 'IS-DIFF-AT)
                                (dk-contains? x proj) (dk-contains? x 'mv))))))
    (have! (list 'AND dl dm))
    (fact 'derivative-unique (cadr dl) 'tv_ (cadddr dl) (cadddr dm))))
(cdu-agree! 'real-part)
(cdu-agree! 'imag-part)
(fact 'cc-re-im-decompose 'lv)
(fact 'cc-re-im-decompose 'mv)
(subst '(= lv (+ (real-part lv) (* +i (imag-part lv)))))
(subst '(= (real-part lv) (real-part mv)))
(subst '(= (imag-part lv) (imag-part mv)))
(fact 'eq-sym 'mv '(+ (real-part mv) (* +i (imag-part mv))))
(ass)
(qed 'cc-diff-at-unique)
(topic! 'cc-diff-at-unique 'analysis)
(alias! 'cc-diff-at-unique
  "the derivative of a CC-valued function of a real variable is unique")

;;; =====================================================================
;;; (6) THE CHAIN RULE WITH A REAL INNER MAP.
;;;
;;; h : RR -> RR differentiable at t with derivative k, g : RR -> CC
;;; differentiable at h(t) with derivative L: then g o h is differentiable at t
;;; with derivative k.L.  Coordinatewise this is the REAL chain rule
;;; (`deriv-chain') applied to h and to each coordinate lambda of g; the
;;; composite it concludes about is a COMPOSE term, whose values are
;;; `compose-apply', and the transfer moves the conclusion onto the coordinate
;;; lambda of the composite map.
;;;
;;; The derivative is k.L with k REAL, so re(k.L) = k.re(L) and im(k.L) =
;;; k.im(L) -- cc-re-real-mul / cc-im-real-mul, not the full product laws.
;;; `deriv-chain' produces the factors in the order re(L).k, so one `crs' per
;;; coordinate reverses them.
;;; =====================================================================

(sp (make-wff "forall([g in fun(rr,cc), h in fun(rr,rr), cm in fun(rr,cc), tv_ in rr,
                       kv in rr, lv in cc],
     forall([x_ in rr], cm(x_) = g(h(x_))) implies
     is-diff-at(h, tv_, kv) implies
     is-cc-diff-at(g, h(tv_), lv) implies
     is-cc-diff-at(cm, tv_, kv * lv))"))
(dk-peel!)
(define cch-ptw (cdl-ptw 'cm))
(fact 'fun-apply-type-c 'h 'RR 'RR 'tv_)
(cdl-unfold! '(IS-CC-DIFF-AT g (h tv_) lv))
(fact 'rr-subset-cc 'kv)
(have! '(AND (IN kv CC) (IN lv CC)))
(fact 'cc-mul-closed 'kv 'lv)
(fact 'cc-re-real-mul 'kv 'lv)
(fact 'cc-im-real-mul 'kv 'lv)
(fact 'real-part-in-rr 'lv)
(fact 'imag-part-in-rr 'lv)
(mac 'is-cc-diff-at)
(dk-conj-close!
 (lambda ()
   (let ((gl (dk-goal)))
     (if (eq? (cdl-head gl) 'IN)
         (ass)
         (let* ((lam  (cadr gl))
                (dl   (cadddr gl))
                (rl?  (dk-contains? gl 'real-part))
                (proj (if rl? 'real-part 'imag-part))
                (dg   (cdl-diff-of 'g proj))
                (clam (cadr dg)))
           (subst (list '= dl (list '* 'kv (list proj 'lv))))
           (dk-project! (list 'IN clam '(FUN RR RR)) 'IS-DIFF-AT dg)
           (let* ((res  (dk-fact! 'deriv-chain 'h clam 'tv_ 'kv (list proj 'lv)))
                  (comp (cadr res))                ; (COMPOSE clam h)
                  (rval (cadddr res)))             ; proj(lv) * kv
             (have! (list '= (list '* 'kv (list proj 'lv)) rval) (lambda () (crs)))
             (subst (list '= (list '* 'kv (list proj 'lv)) rval))
             (cdl-lam-in-fun! lam 'cm proj)
             (dk-have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                          (list '== (list lam 'x_) (list comp 'x_))))
               (lambda ()
                 (di)
                 (fact 'fun-apply-type-c 'h 'RR 'RR 'x_)
                 (fact 'fun-apply-type-c 'g 'RR 'CC '(h x_))
                 (fact 'fun-apply-type-c 'cm 'RR 'CC 'x_)
                 (fact (if rl? 'real-part-in-rr 'imag-part-in-rr) '(g (h x_)))
                 (have! (list 'AND '(IN h (FUN RR RR)) (list 'IN clam '(FUN RR RR))))
                 (inst+ (dk-fact! 'compose-apply 'RR 'RR 'RR clam 'h) 'x_)
                 (subst (list '= (list comp 'x_) (list clam '(h x_))))
                 (dk-lam-b!)
                 (inst+ cch-ptw 'x_)
                 (subst '(= (cm x_) (g (h x_))))
                 (qrfl)))
             (fact 'diff-transfer-ptwise-eq lam comp 'tv_ rval)
             (ass)))))))
(qed 'cc-diff-at-chain-real)
(topic! 'cc-diff-at-chain-real 'analysis)
(alias! 'cc-diff-at-chain-real
  "the chain rule for a CC-valued function composed with a real function")
