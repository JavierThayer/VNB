;;; diff-on-laws-2.scm -- THE DERIVATIVE LAWS ON AN OPEN SET, over a normed
;;; field: uniqueness, the constant and the identity, the sum, the product and
;;; the chain rule.  Continues theorem-library/diff-on-laws.scm (batch 12-G),
;;; which proved the read-offs, the bridge `diff-at-iff-diff-on' and
;;; `diff-on-implies-continuous' and stopped at the missing continuity algebra;
;;; that algebra is theorem-library/ms-continuity-algebra.scm (batch 13-A,
;;; STAGE 1), which this file consumes.
;;;
;;; Helper prefix: d2-.
;;;
;;; THE THREE MECHANISMS.
;;;
;;; (1) THE DOMAIN-NAMED FORM OF A CONTINUITY LAW.  The algebra states its
;;; conclusions about a lambda over PTS(mss_).  IS-DIFF-ON's factor phi is a
;;; lambda over U, and the space is W = SUBSPACE-MS(NF-METRIC-SPACE K, U),
;;; which CONTAINS U -- so `subst' of (== U (PTS W)) on the goal would rewrite
;;; U inside W as well and produce PTS(SUBSPACE-MS(M, PTS(SUBSPACE-MS(M,U)))).
;;; The cure is to give the domain a NAME: each law is restated with a fresh
;;; variable d2d_ and the hypothesis (== (PTS mss_) d2d_), and its proof is the
;;; original citation plus ONE `subst' of (== d2d_ (PTS mss_)) on the goal --
;;; a rewrite in the safe direction, since PTS(mss_) does not contain d2d_.
;;; At the point of use d2d_ is U and the hypothesis is `subspace-pts'.
;;;
;;; (2) THE TYPINGS ARE STATED NATIVELY IN THE U / CARR(K) VOCABULARY, not
;;; transported from PTS(W) / PTS(M): a FUN class is the one place where BOTH
;;; the domain and the codomain would have to be rewritten, and the lambdas are
;;; two `lam-t' leaves each anyway.
;;;
;;; (3) UNIQUENESS GOES BY THE NORM, NOT BY INVERSES.  From
;;; phi(x).(x-a) = psi(x).(x-a) on U one gets ||phi x - psi x|| . ||x - a|| = 0
;;; by `nf-norm-mult', and for x /= a in U the second factor is nonzero by the
;;; DEFINITENESS of the norm (`nf-norm-zero-iff', surfaced below from the
;;; `is-norm' conjunct of IS-NORMED-FIELD), so phi and psi agree off a.  They
;;; are both continuous at a, and a is a LIMIT POINT of U, so they agree at a
;;; too (`ms-cont-agree-off-pt').  `normed-field-mul-inverses' and
;;; `normed-field-zero-not-one' are ASSERTED supports and are not cited: the
;;; route through them would have billed them.
;;;
;;; WHY THE NON-TRIVIALITY HYPOTHESIS IS EXPLICIT.  "Every point of an open U
;;; is a limit point of U" is FALSE over a field whose norm is trivial (the
;;; norm that is 1 off zero: every singleton is open).  The hypothesis
;;;
;;;    d2-small(K):  forall eps > 0. forsome h in CARR(K). h /= ZERO(K)
;;;                                  and ||h|| < eps
;;;
;;; is carried as an antecedent of `nf-open-limit-point' and of
;;; `diff-on-unique', and is PROVEN for rr-normed-field (`rr-nf-small-elements';
;;; the CC case is 13-B's, since it needs `cc-is-normed-field').  It is not a
;;; conjunct of IS-DIFF-ON: differentiability, continuity and the sum / product
;;; / chain rules need nothing of the kind.
;;;
;;; Dependencies: structure-library/diff-on.scm, metric-subspace.scm;
;;; theorem-library/metric-subspace-laws.scm (subspace-pts, subspace-dist,
;;; subspace-is-metric-space), diff-on-laws.scm (the read-offs, the nf-norm
;;; toolkit, the RR instance slots rr-nf-carr / rr-nf-zero / rr-nf-fnrm-apply,
;;; diff-on-implies-continuous), ms-continuity-algebra.scm (STAGE 1),
;;; rake-nf-norm.scm, rr-halving, rr-order-basics, set-basics
;;; (subclass-of-set-is-set).
;;; Load slot: immediately after theorem-library/ms-continuity-algebra.

;;; ---- file-local driver helpers --------------------------------------

(define (d2-head e) (and (pair? e) (car e)))

(define d2-M '(NF-METRIC-SPACE K))
(define d2-W '(SUBSPACE-MS (NF-METRIC-SPACE K) U))

(define (d2-add a b) (list '(ADD K) a b))
(define (d2-mul a b) (list '(MUL K) a b))
(define (d2-neg a)   (list '(NEG K) a))
(define (d2-sub a b) (d2-add a (d2-neg b)))
(define (d2-nrm a)   (list '(FNRM K) a))

;;; The non-triviality hypothesis, at a named field.
(define (d2-small k)
  (list 'FORALL 'd2e_
    (list 'IMPLIES '(POS-RR d2e_)
      (list 'FORSOME 'd2h_
        (list 'AND (list 'IN 'd2h_ (list 'CARR k))
          (list 'AND (list 'NOT (list '= 'd2h_ (list 'ZERO k)))
                     (list '< (list (list 'FNRM k) 'd2h_) 'd2e_)))))))

;;; POS-RR t -> (IN t RR), (< 0 t), by citation.
(define (d2-pos! t)
  (fact 'rr-pos-rr-in-rr t)
  (fact 'rr-lt-of-pos-rr t))

;;; =====================================================================
;;; (1) THE DOMAIN-NAMED FORM OF EACH CONTINUITY LAW.
;;;
;;; Each is the STAGE 1 law with the lambda's domain given a name d2d_ and the
;;; hypothesis (== (PTS mss_) d2d_).  The proof is the citation and one
;;; `subst'; see mechanism (1) in the header for why the rewrite cannot go the
;;; other way.
;;; =====================================================================

;;; (FORALL mss_ (FORALL d2d_ (IMPLIES (== (PTS mss_) d2d_) BODY)))
(define (d2-on-stmt body)
  (list 'FORALL 'mss_ (list 'FORALL 'd2d_
    (list 'IMPLIES '(== (PTS mss_) d2d_) body))))

(define (d2-on-thm! name stmt cite!)
  (sp (make-wff stmt))
  (dk-peel!)
  (cite!)
  (subst '(== d2d_ (PTS mss_)))
  (ass)
  (if (not (proof-done? *ps*))
      (error "d2-on-thm!: proof did not close" name (dk-goal)))
  (qed name))

(d2-on-thm! 'ms-const-continuous-on
  (d2-on-stmt
   '(FORALL mst_ (IMPLIES (IS-METRIC-SPACE mss_)
      (IMPLIES (IS-METRIC-SPACE mst_)
        (FORALL msc_ (IMPLIES (IN msc_ (PTS mst_))
          (FORALL msa_ (IMPLIES (IN msa_ (PTS mss_))
            (IS-CONTINUOUS-AT mss_ mst_ (VNB-LAMBDA msz_ d2d_ msc_) msa_)))))))))
  (lambda () (fact 'ms-const-continuous-at 'mss_ 'mst_ 'msc_ 'msa_)))
(topic! 'ms-const-continuous-on 'analysis)
(alias! 'ms-const-continuous-on
        "a constant map on a named domain is continuous")

(d2-on-thm! 'ms-identity-continuous-on
  (d2-on-stmt
   '(IMPLIES (IS-METRIC-SPACE mss_)
      (FORALL msa_ (IMPLIES (IN msa_ (PTS mss_))
        (IS-CONTINUOUS-AT mss_ mss_ (VNB-LAMBDA msz_ d2d_ msz_) msa_)))))
  (lambda () (fact 'ms-identity-continuous-at 'mss_ 'msa_)))
(topic! 'ms-identity-continuous-on 'analysis)

(d2-on-thm! 'nf-sum-continuous-on
  (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
    (d2-on-stmt
     (list 'FORALL 'msg_ (list 'FORALL 'msh_ (list 'FORALL 'msa_
       (list 'IMPLIES (list 'IS-CONTINUOUS-AT 'mss_ d2-M 'msg_ 'msa_)
         (list 'IMPLIES (list 'IS-CONTINUOUS-AT 'mss_ d2-M 'msh_ 'msa_)
           (list 'IS-CONTINUOUS-AT 'mss_ d2-M
                 '(VNB-LAMBDA msz_ d2d_ ((ADD K) (msg_ msz_) (msh_ msz_)))
                 'msa_)))))))))
  (lambda () (fact 'nf-sum-continuous-at 'K 'mss_ 'msg_ 'msh_ 'msa_)))
(topic! 'nf-sum-continuous-on 'analysis)

(d2-on-thm! 'nf-product-continuous-on
  (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
    (d2-on-stmt
     (list 'FORALL 'msg_ (list 'FORALL 'msh_ (list 'FORALL 'msa_
       (list 'IMPLIES (list 'IS-CONTINUOUS-AT 'mss_ d2-M 'msg_ 'msa_)
         (list 'IMPLIES (list 'IS-CONTINUOUS-AT 'mss_ d2-M 'msh_ 'msa_)
           (list 'IS-CONTINUOUS-AT 'mss_ d2-M
                 '(VNB-LAMBDA msz_ d2d_ ((MUL K) (msg_ msz_) (msh_ msz_)))
                 'msa_)))))))))
  (lambda () (fact 'nf-product-continuous-at 'K 'mss_ 'msg_ 'msh_ 'msa_)))
(topic! 'nf-product-continuous-on 'analysis)

(d2-on-thm! 'ms-compose-continuous-on
  (d2-on-stmt
   '(FORALL mst_ (FORALL msu_ (FORALL msf_ (FORALL msg_ (FORALL msa_
      (IMPLIES (IS-CONTINUOUS-AT mss_ mst_ msf_ msa_)
        (IMPLIES (IS-CONTINUOUS-AT mst_ msu_ msg_ (msf_ msa_))
          (IS-CONTINUOUS-AT mss_ msu_
            (VNB-LAMBDA msz_ d2d_ (msg_ (msf_ msz_))) msa_)))))))))
  (lambda () (fact 'ms-compose-continuous-at 'mss_ 'mst_ 'msu_ 'msf_ 'msg_ 'msa_)))
(topic! 'ms-compose-continuous-on 'analysis)

;;; THE TRANSFER is the one law whose HYPOTHESES name the domain as well, and
;;; there is no hypothesis-side rewrite: the two forms the cited theorem wants
;;; are rebuilt on `have!' lanes, where `subst' works on the goal.
(sp (make-wff
     '(FORALL mss_ (FORALL mst_ (FORALL d2d_ (FORALL d2c_
        (IMPLIES (== (PTS mss_) d2d_)
          (IMPLIES (== (PTS mst_) d2c_)
            (FORALL msg_ (FORALL msf_ (FORALL msa_
              (IMPLIES (IS-CONTINUOUS-AT mss_ mst_ msg_ msa_)
                (IMPLIES (IN msf_ (FUN d2d_ d2c_))
                  (IMPLIES (FORALL msy_ (IMPLIES (IN msy_ d2d_)
                             (= (msf_ msy_) (msg_ msy_))))
                    (IS-CONTINUOUS-AT mss_ mst_ msf_ msa_)))))))))))))))
(define d2-tr-landed (dk-peel!))
(define d2-tr-agree
  (dk-pick (lambda (fm) (and (member fm d2-tr-landed) (eq? (d2-head fm) 'FORALL)
                             (dk-contains? fm 'msf_)))
           "the pointwise-equality universal"))
(dk-have! '(IN msf_ (FUN (PTS mss_) (PTS mst_)))
  (lambda () (subst '(== (PTS mss_) d2d_)) (subst '(== (PTS mst_) d2c_)) (ass)))
(dk-have! '(FORALL msy_ (IMPLIES (IN msy_ (PTS mss_)) (= (msf_ msy_) (msg_ msy_))))
  (lambda ()
    (let ((y (dk-di-var!)))
      (dk-have! (list 'IN y 'd2d_)
        (lambda () (subst '(== d2d_ (PTS mss_))) (ass)))
      (dk-apply! d2-tr-agree y)
      (ass))))
(fact 'ms-cont-transfer-ptwise-eq 'mss_ 'mst_ 'msg_ 'msf_ 'msa_)
(ass)
(qed 'ms-cont-transfer-on)
(topic! 'ms-cont-transfer-on 'analysis)
(alias! 'ms-cont-transfer-on
        "continuity transfers along pointwise equality on a named domain")

;;; =====================================================================
;;; (2) THE LAMBDA TYPINGS, in the U / CARR(K) vocabulary.
;;; =====================================================================

(define (d2-lam-thm! name lam guards body)
  (sp (make-wff
       (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
         (list 'FORALL 'U (list 'IMPLIES '(IN U SET)
           (let loop ((g guards))
             (cond ((null? g) (list 'IN lam '(FUN U (CARR K))))
                   ((car (car g))
                    (list 'FORALL (car (car g))
                      (list 'IMPLIES (cadr (car g)) (loop (cdr g)))))
                   (#t (list 'IMPLIES (cadr (car g)) (loop (cdr g))))))))))))
  (dk-peel!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (d2-head (dk-goal)) 'FORALL)
         (let ((z (dk-di-var!))) (body z) (ass))
         (ass)))
   (dk-opened (lambda () (lam-t))))
  (if (not (proof-done? *ps*))
      (error "d2-lam-thm!: proof did not close" name (dk-goal)))
  (qed name))

(d2-lam-thm! 'nf-lam-const-in-fun '(VNB-LAMBDA d2x_ U d2c_)
  '((d2c_ (IN d2c_ (CARR K))))
  (lambda (z) #t))
(topic! 'nf-lam-const-in-fun 'analysis)

;;; the identity is the one lambda that needs U inside the carrier.
(d2-lam-thm! 'nf-lam-id-in-fun '(VNB-LAMBDA d2x_ U d2x_)
  '((#f (SUBSET U (CARR K))))
  (lambda (z) (fact 'subset-mem-fwd 'U '(CARR K) z)))
(topic! 'nf-lam-id-in-fun 'analysis)

(d2-lam-thm! 'nf-lam-sum-in-fun
  '(VNB-LAMBDA d2x_ U ((ADD K) (d2f_ d2x_) (d2g_ d2x_)))
  '((d2f_ (IN d2f_ (FUN U (CARR K)))) (d2g_ (IN d2g_ (FUN U (CARR K)))))
  (lambda (z)
    (fact 'fun-apply-type-c 'd2f_ 'U '(CARR K) z)
    (fact 'fun-apply-type-c 'd2g_ 'U '(CARR K) z)
    (fact 'nf-add-in-carr 'K (list 'd2f_ z) (list 'd2g_ z))))
(topic! 'nf-lam-sum-in-fun 'analysis)

(d2-lam-thm! 'nf-lam-prod-in-fun
  '(VNB-LAMBDA d2x_ U ((MUL K) (d2f_ d2x_) (d2g_ d2x_)))
  '((d2f_ (IN d2f_ (FUN U (CARR K)))) (d2g_ (IN d2g_ (FUN U (CARR K)))))
  (lambda (z)
    (fact 'fun-apply-type-c 'd2f_ 'U '(CARR K) z)
    (fact 'fun-apply-type-c 'd2g_ 'U '(CARR K) z)
    (fact 'nf-mul-in-carr 'K (list 'd2f_ z) (list 'd2g_ z))))
(topic! 'nf-lam-prod-in-fun 'analysis)

;;; =====================================================================
;;; (3) THE DEFINITENESS OF THE NORM, AND SMALL ELEMENTS OF RR.
;;; =====================================================================

;;; ||u|| = 0 iff u = ZERO(K): the second conjunct of the `is-norm' universal,
;;; surfaced the way diff-on-laws.scm surfaced the other three.
(sp (make-wff (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
     (forall-guarded '(d2u_) '((IN d2u_ (CARR K)))
       '(IFF (= ((FNRM K) d2u_) 0) (= d2u_ (ZERO K))))))))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda () (mac-h 'is-normed-field '(IS-NORMED-FIELD K)))))
(dk-split-all!
 (dk-landed* (lambda () (mac-h 'is-norm '(is-norm (FNRM K) (ADD K) (MUL K)
                                                  (ZERO K) (CARR K))))))
(dk-split! (dk-apply!
            (dk-pick (lambda (fm)
                       (and (pair? fm) (eq? (car fm) 'FORALL)
                            (pair? (caddr fm)) (eq? (car (caddr fm)) 'IMPLIES)
                            (pair? (caddr (caddr fm)))
                            (eq? (car (caddr (caddr fm))) 'AND)
                            (let ((c1 (cadr (caddr (caddr fm)))))
                              (and (pair? c1) (eq? (car c1) '<=)
                                   (equal? (cadr c1) 0)))))
                     "the is-norm universal")
            'd2u_))
(ass)
(qed 'nf-norm-zero-iff)
(topic! 'nf-norm-zero-iff 'algebra)
(alias! 'nf-norm-zero-iff "a field norm vanishes only at zero")

;;; The direction every argument below uses, as its own theorem.  `prop' can
;;; take an IFF apart, but only in a SHALLOW context: its atom cap is 12 and a
;;; deep eps/delta context puts the relevant pair out of reach and makes it
;;; decline with an EMPTY countermodel (CLAUDE.md, "the tactics' real
;;; behaviour").  Here the context is four formulas.
(sp (make-wff (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
     (forall-guarded '(d2u_) '((IN d2u_ (CARR K)))
       '(IMPLIES (= ((FNRM K) d2u_) 0) (= d2u_ (ZERO K))))))))
(dk-peel!)
(fact 'nf-norm-zero-iff 'K 'd2u_)
(prop)
(qed 'nf-norm-zero-implies)
(topic! 'nf-norm-zero-implies 'algebra)
(alias! 'nf-norm-zero-implies "an element of norm zero is zero")

;;; A nonzero element of norm below any given positive real: for the reals,
;;; half of it.  This is the non-triviality hypothesis of the header, PROVEN
;;; at rr-normed-field.  (The CC case belongs to 13-B: it needs
;;; `cc-is-normed-field', which is still an asserted axiom.)
(sp (make-wff (d2-small 'RR-NORMED-FIELD)))
(dk-peel!)
(d2-pos! 'd2e_)
(let ((hf (dk-skolem! (dk-fact! 'rr-pos-halvable 'd2e_))))
  (d2-pos! hf)
  (fact 'rr-nf-carr)
  (fact 'rr-nf-zero)
  (fact 'rr-nf-fnrm-apply hf)
  (fact 'rr-lt-implies-le 0 hf)
  (fact 'rr-abs-of-nonneg hf)
  (fact 'rr-pos-ne-zero hf)
  (ew hf)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (cond ((eq? (d2-head g) 'IN)
              (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass))
             ((eq? (d2-head g) 'NOT)
              (subst '(== (ZERO RR-NORMED-FIELD) 0)) (ass))
             (#t
              (subst (list '== (list '(FNRM RR-NORMED-FIELD) hf) (list 'abs hf)))
              (subst (list '= (list 'abs hf) hf))
              (dk-ineq! (list '= (list '+ hf hf) 'd2e_) (list '< 0 hf)
                        (list 'IN hf 'RR) '(IN d2e_ RR))))))))
(qed 'rr-nf-small-elements)
(topic! 'rr-nf-small-elements 'analysis)
(alias! 'rr-nf-small-elements
        "the real norm has nonzero elements of arbitrarily small size")

;;; =====================================================================
;;; (4) EVERY POINT OF AN OPEN SET IS A LIMIT POINT OF IT.
;;;
;;; This is the hypothesis `ms-cont-agree-off-pt' carries, discharged for the
;;; SUBSPACE metric on U -- which is the space IS-DIFF-ON's phi is continuous
;;; on.  Given r > 0 and a in U, take rho with BALL(M, a, rho) inside U, put
;;; w below both r and rho, and let h be a nonzero element of norm < w.  Then
;;; b = a + h lies in the ball (d(a,b) = ||a - b|| = ||-h|| = ||h|| < rho), so
;;; in U; d_W(a,b) = d_M(a,b) = ||h|| <= r; and b /= a because otherwise
;;; d(a,b) = d(a,a) = 0, i.e. ||h|| = 0, i.e. h = ZERO(K) by `nf-norm-zero-iff'.
;;;
;;; THE TRIVIAL NORM IS EXACTLY WHAT THE HYPOTHESIS EXCLUDES: with ||x|| = 1
;;; for x /= 0 every singleton is open and has no limit point, and the
;;; statement is false.  Nothing else in this file needs the hypothesis.
;;; =====================================================================

(define d2-view '(NORMED-FIELD-AS-COMMUTATIVE-RING K))

(define (d2-occurs? sub e)
  (cond ((equal? sub e) #t)
        ((pair? e) (or (d2-occurs? sub (car e)) (d2-occurs? sub (cdr e))))
        (#t #f)))

(define (d2-subst-if! eq)
  (if (d2-occurs? (cadr eq) (dk-goal)) (subst eq)))

;;; A ring identity of K on the typed ARGS, by `crs' through the view.
(define (d2-ring-id! args)
  (fact 'normed-field-as-commutative-ring-is-commutative-ring 'K)
  (fact 'commutative-ring-is-ring d2-view)
  (fact 'normed-field-ring-view-carr 'K)
  (fact 'normed-field-ring-view-add 'K)
  (fact 'normed-field-ring-view-mul 'K)
  (fact 'normed-field-ring-view-neg 'K)
  (fact 'normed-field-ring-view-zero 'K)
  (fact 'normed-field-ring-view-one 'K)
  (for-each (lambda (u)
              (dk-have! (list 'IN u (list 'CARR d2-view))
                (lambda () (subst (list '== (list 'CARR d2-view) '(CARR K))) (ass))))
            args)
  (d2-subst-if! (list '== '(ADD K) (list 'ADD d2-view)))
  (d2-subst-if! (list '== '(MUL K) (list 'MUL d2-view)))
  (d2-subst-if! (list '== '(NEG K) (list 'NEG d2-view)))
  (d2-subst-if! (list '== '(ZERO K) (list 'ZERO d2-view)))
  (d2-subst-if! (list '== '(ONE K) (list 'ONE d2-view)))
  (crs))

;;; From (< x y) in context, land (NOT (= x y)).  `ineq' cannot prove a NOT
;;; goal, so the disequality is reached through `rr-lt-not-le' and the
;;; reflexivity the assumed equation would give.
(define (d2-lt-ne! x y)
  (dk-have! (list 'NOT (list '= x y))
    (lambda ()
      (di)
      (fact 'rr-lt-not-le x y)
      (dk-have! (list '<= y x)
        (lambda () (subst (list '= x y)) (fact 'rr-leq-reflexive y) (ass)))
      (ai (list 'NOT (list '<= y x))))))

(sp (make-wff
     (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
       (list 'IMPLIES (d2-small 'K)
         (list 'FORALL 'U (list 'IMPLIES (list 'IS-OPEN d2-M 'U)
           (list 'FORALL 'd2a_ (list 'IMPLIES '(IN d2a_ U)
             (list 'FORALL 'd2r_ (list 'IMPLIES '(POS-RR d2r_)
               (list 'FORSOME 'd2b_
                 (list 'AND '(IN d2b_ U)
                   (list 'AND '(NOT (= d2b_ d2a_))
                     (list '<= (list (list 'DIST d2-W) 'd2a_ 'd2b_)
                               'd2r_)))))))))))))))
(define d2-lp-landed (dk-peel!))
(define d2-lp-small
  (dk-pick (lambda (fm) (and (member fm d2-lp-landed) (eq? (d2-head fm) 'FORALL)
                             (dk-contains? fm 'FNRM)))
           "the small-elements hypothesis"))
(fact 'nf-metric-carrier 'K)
(fact 'nf-metric-space-is-metric-space 'K)
(fact 'nf-open-subset-carr 'K 'U)
(fact 'subset-mem-fwd 'U '(CARR K) 'd2a_)
(dk-have! (list 'SUBSET 'U (list 'PTS d2-M))
  (lambda () (subst (list '== (list 'PTS d2-M) '(CARR K))) (ass)))
(dk-have! (list 'IN 'd2a_ (list 'PTS d2-M))
  (lambda () (subst (list '== (list 'PTS d2-M) '(CARR K))) (ass)))
(fact 'subspace-is-metric-space d2-M 'U)
(d2-pos! 'd2r_)
(mac-h 'IS-OPEN (list 'IS-OPEN d2-M 'U))
(dk-split-all!)
(let* ((rho (dk-skolem!
             (dk-apply! (dk-pick (lambda (fm)
                                   (and (pair? fm) (eq? (d2-head fm) 'FORALL)
                                        (dk-contains? fm 'BALL)))
                                 "the open-set ball witness")
                        'd2a_))))
  (d2-pos! rho)
  (let ((w (dk-skolem! (dk-fact! 'rr-min-pos rho 'd2r_))))
    (fact 'rr-pos-rr-of-lt w)
    (let* ((h (dk-skolem! (dk-apply! d2-lp-small w)))
           (bb (d2-add 'd2a_ h))
           (dmab (list (list 'DIST d2-M) 'd2a_ bb))
           (nh (d2-nrm h)))
      (fact 'nf-add-in-carr 'K 'd2a_ h)
      (fact 'nf-neg-in-carr 'K bb)
      (fact 'nf-add-in-carr 'K 'd2a_ (d2-neg bb))
      (fact 'nf-norm-in-rr 'K h)
      (dk-have! (list '= (d2-sub 'd2a_ bb) (d2-neg h))
        (lambda () (d2-ring-id! (list 'd2a_ h))))
      (fact 'nf-norm-neg 'K h)
      (fact 'nf-metric-distance 'K 'd2a_ bb)
      (dk-have! (list '= dmab nh)
        (lambda ()
          (subst (list '= dmab (d2-nrm (d2-sub 'd2a_ bb))))
          (subst (list '= (d2-sub 'd2a_ bb) (d2-neg h)))
          (ass)))
      (dk-have! (list '< nh rho)
        (lambda () (dk-ineq! (list '< nh w) (list '<= w rho)
                             (list 'IN nh 'RR) (list 'IN w 'RR)
                             (list 'IN rho 'RR))))
      (dk-have! (list '<= nh 'd2r_)
        (lambda () (dk-ineq! (list '< nh w) (list '<= w 'd2r_)
                             (list 'IN nh 'RR) (list 'IN w 'RR)
                             '(IN d2r_ RR))))
      (dk-have! (list 'IN bb (list 'PTS d2-M))
        (lambda () (subst (list '== (list 'PTS d2-M) '(CARR K))) (ass)))
      (d2-lt-ne! nh rho)
      (dk-have! (list 'IN bb (list 'BALL d2-M 'd2a_ rho))
        (lambda ()
          (mac 'ball-membership)
          (dk-conj-close!
           (lambda ()
             (let ((g (dk-goal)))
               (cond ((eq? (d2-head g) 'IN) (ass))
                     ((eq? (d2-head g) 'NOT)
                      (subst (list '= dmab nh)) (ass))
                     (#t (subst (list '= dmab nh))
                         (dk-ineq! (list '< nh rho) (list 'IN nh 'RR)
                                   (list 'IN rho 'RR))))))))) 
      (fact 'subset-mem-fwd (list 'BALL d2-M 'd2a_ rho) 'U bb)
      (fact 'subspace-dist d2-M 'U 'd2a_ bb)
      (fact 'metric-self-zero d2-M 'd2a_)
      (fact 'nf-norm-zero-iff 'K h)
      (ew bb)
      (dk-conj-close!
       (lambda ()
         (let ((g (dk-goal)))
           (cond ((eq? (d2-head g) 'IN) (ass))
                 ((eq? (d2-head g) 'NOT)
                  (di)
                  (dk-have! (list '= nh 0)
                    (lambda ()
                      (subst (list '= nh dmab))
                      (subst (list '= bb 'd2a_))
                      (ass)))
                  (fact 'nf-norm-zero-implies 'K h)
                  (ai (list 'NOT (list '= h '(ZERO K)))))
                 (#t
                  (subst (list '== (list (list 'DIST d2-W) 'd2a_ bb) dmab))
                  (subst (list '= dmab nh))
                  (ass)))))))))
(qed 'nf-open-limit-point)
(topic! 'nf-open-limit-point 'analysis)
(alias! 'nf-open-limit-point
        "every point of an open set in a nontrivially normed field is a limit point of it")

;;; =====================================================================
;;; (5) CANCELLATION BY A NONZERO FACTOR, AND THE UNIQUENESS OF THE
;;; DERIVATIVE.
;;;
;;; `normed-field-mul-inverses' and `normed-field-zero-not-one' are ASSERTED
;;; supports; citing either would put it on this bill and on every bill below.
;;; The cancellation is therefore proved through the NORM, which is a theorem
;;; all the way down: (u - v).w = u.w - v.w = 0, so ||u-v||.||w|| = ||0|| = 0,
;;; and ||w|| /= 0 because w /= 0, so ||u-v|| = 0 by `rr-no-zero-divisors' and
;;; u - v = 0 by the definiteness of the norm.
;;; =====================================================================

;;; ZERO(K) lies in the carrier, and its norm is 0.  The first is a conjunct of
;;; the IS-NORMED-FIELD iff; the second is the definiteness read at ZERO(K).
(sp (make-wff '(FORALL K (IMPLIES (IS-NORMED-FIELD K) (IN (ZERO K) (CARR K))))))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda () (mac-h 'is-normed-field '(IS-NORMED-FIELD K)))))
(ass)
(qed 'nf-zero-in-carr)
(topic! 'nf-zero-in-carr 'algebra)

(sp (make-wff '(FORALL K (IMPLIES (IS-NORMED-FIELD K)
     (= ((FNRM K) (ZERO K)) 0)))))
(dk-peel!)
(fact 'nf-zero-in-carr 'K)
(fact 'nf-norm-zero-iff 'K '(ZERO K))
(dk-have! '(= (ZERO K) (ZERO K)) (lambda () (rfl)))
(prop)
(qed 'nf-norm-of-zero)
(topic! 'nf-norm-of-zero 'algebra)
(alias! 'nf-norm-of-zero "the norm of zero is zero")

;;; u - v = 0 gives u = v: (u - v) + v = u and 0 + v = v, chained by `eq-trans'
;;; -- NEVER by substituting the bare variable u, which would rewrite the u
;;; inside the right-hand side of its own equation.
(sp (make-wff (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
     (forall-guarded '(d2u_ d2v_) '((IN d2u_ (CARR K)) (IN d2v_ (CARR K)))
       (list 'IMPLIES (list '= (d2-sub 'd2u_ 'd2v_) '(ZERO K))
                      '(= d2u_ d2v_)))))))
(dk-peel!)
(fact 'nf-neg-in-carr 'K 'd2v_)
(fact 'nf-add-in-carr 'K 'd2u_ (d2-neg 'd2v_))
(fact 'nf-zero-in-carr 'K)
(dk-have! (list '= (d2-add (d2-sub 'd2u_ 'd2v_) 'd2v_) 'd2u_)
  (lambda () (d2-ring-id! '(d2u_ d2v_))))
(dk-have! (list '= (d2-add '(ZERO K) 'd2v_) 'd2v_)
  (lambda () (d2-ring-id! '(d2u_ d2v_))))
(fact 'eq-sym (d2-add (d2-sub 'd2u_ 'd2v_) 'd2v_) 'd2u_)
(dk-have! (list '= (d2-add (d2-sub 'd2u_ 'd2v_) 'd2v_) 'd2v_)
  (lambda () (subst (list '= (d2-sub 'd2u_ 'd2v_) '(ZERO K))) (ass)))
(fact 'eq-trans 'd2u_ (d2-add (d2-sub 'd2u_ 'd2v_) 'd2v_) 'd2v_)
(ass)
(qed 'nf-sub-zero-eq)
(topic! 'nf-sub-zero-eq 'algebra)
(alias! 'nf-sub-zero-eq "elements whose difference is zero are equal")

;;; CANCELLATION.  u.w = v.w and w /= 0 give u = v.
(sp (make-wff (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
     (forall-guarded '(d2u_ d2v_ d2w_)
       '((IN d2u_ (CARR K)) (IN d2v_ (CARR K)) (IN d2w_ (CARR K)))
       (list 'IMPLIES '(NOT (= d2w_ (ZERO K)))
         (list 'IMPLIES (list '= (d2-mul 'd2u_ 'd2w_) (d2-mul 'd2v_ 'd2w_))
                        '(= d2u_ d2v_))))))))
(dk-peel!)
(fact 'nf-neg-in-carr 'K 'd2v_)
(fact 'nf-add-in-carr 'K 'd2u_ (d2-neg 'd2v_))
(fact 'nf-mul-in-carr 'K (d2-sub 'd2u_ 'd2v_) 'd2w_)
(fact 'nf-mul-in-carr 'K 'd2u_ 'd2w_)
(fact 'nf-mul-in-carr 'K 'd2v_ 'd2w_)
(fact 'nf-zero-in-carr 'K)
(fact 'nf-norm-of-zero 'K)
(fact 'nf-norm-in-rr 'K (d2-sub 'd2u_ 'd2v_))
(fact 'nf-norm-in-rr 'K 'd2w_)
(fact 'nf-norm-mult 'K (d2-sub 'd2u_ 'd2v_) 'd2w_)
;; (u - v).w = u.w - v.w = 0
(dk-have! (list '= (d2-mul (d2-sub 'd2u_ 'd2v_) 'd2w_)
                   (d2-sub (d2-mul 'd2u_ 'd2w_) (d2-mul 'd2v_ 'd2w_)))
  (lambda () (d2-ring-id! '(d2u_ d2v_ d2w_))))
(dk-have! (list '= (d2-mul (d2-sub 'd2u_ 'd2v_) 'd2w_) '(ZERO K))
  (lambda ()
    (subst (list '= (d2-mul (d2-sub 'd2u_ 'd2v_) 'd2w_)
                    (d2-sub (d2-mul 'd2u_ 'd2w_) (d2-mul 'd2v_ 'd2w_))))
    (subst (list '= (d2-mul 'd2u_ 'd2w_) (d2-mul 'd2v_ 'd2w_)))
    (d2-ring-id! (list 'd2u_ 'd2v_ 'd2w_ (d2-mul 'd2v_ 'd2w_)))))
;; ||u-v|| . ||w|| = 0
(dk-have! (list '= (list '* (d2-nrm (d2-sub 'd2u_ 'd2v_)) (d2-nrm 'd2w_)) 0)
  (lambda ()
    (subst (list '= (list '* (d2-nrm (d2-sub 'd2u_ 'd2v_)) (d2-nrm 'd2w_))
                    (d2-nrm (d2-mul (d2-sub 'd2u_ 'd2v_) 'd2w_))))
    (subst (list '= (d2-mul (d2-sub 'd2u_ 'd2v_) 'd2w_) '(ZERO K)))
    (ass)))
;; ||w|| /= 0
(dk-have! (list 'NOT (list '= (d2-nrm 'd2w_) 0))
  (lambda ()
    (di)
    (fact 'nf-norm-zero-implies 'K 'd2w_)
    (ai '(NOT (= d2w_ (ZERO K))))))
(fact 'rr-no-zero-divisors (d2-nrm (d2-sub 'd2u_ 'd2v_)) (d2-nrm 'd2w_))
(dk-have! (list '= (d2-nrm (d2-sub 'd2u_ 'd2v_)) 0) (lambda () (prop)))
(fact 'nf-norm-zero-implies 'K (d2-sub 'd2u_ 'd2v_))
(fact 'nf-sub-zero-eq 'K 'd2u_ 'd2v_)
(ass)
(qed 'nf-mul-cancel)
(topic! 'nf-mul-cancel 'algebra)
(alias! 'nf-mul-cancel "a nonzero factor cancels in a normed field")

;;; =====================================================================
;;; (6) THE DERIVATIVE ON AN OPEN SET IS UNIQUE.
;;;
;;; phi and psi are the two Caratheodory factors.  For x in U with x /= a,
;;; x - a /= 0 (`nf-sub-zero-eq') and phi(x).(x-a) = psi(x).(x-a) (both equal
;;; f(x) - f(a)), so phi(x) = psi(x) by `nf-mul-cancel'.  The two factors are
;;; continuous at a and a is a limit point of U, so phi(a) = psi(a) --
;;; `ms-cont-agree-off-pt' -- and those are L and L'.
;;;
;;; THE TWO UNIVERSALS ms-cont-agree-off-pt WANTS ARE STATED OVER PTS(W) and
;;; what the argument produces is stated over U; they are rebuilt on `have!'
;;; lanes, with the SAME BINDER NAMES the theorem uses (msr_, msb_, msy_), so
;;; that `fact' detaches them.
;;; =====================================================================

(define (d2-cara-univ phi)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (d2-head fm) 'FORALL)
                             (dk-contains? fm phi)))
           "the Caratheodory universal"))

(sp (make-wff
     (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
       (list 'IMPLIES (d2-small 'K)
         '(FORALL U (FORALL d2f_ (FORALL d2a_ (FORALL d2l_ (FORALL d2m_
            (IMPLIES (IS-DIFF-ON K U d2f_ d2a_ d2l_)
              (IMPLIES (IS-DIFF-ON K U d2f_ d2a_ d2m_)
                (= d2l_ d2m_))))))))))))) 
(dk-peel!)
(fact 'diff-on-open 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-pt-in 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'nf-metric-carrier 'K)
(fact 'nf-metric-space-is-metric-space 'K)
(fact 'nf-open-subset-carr 'K 'U)
(fact 'subset-mem-fwd 'U '(CARR K) 'd2a_)
(dk-have! (list 'SUBSET 'U (list 'PTS d2-M))
  (lambda () (subst (list '== (list 'PTS d2-M) '(CARR K))) (ass)))
(fact 'subspace-is-metric-space d2-M 'U)
(fact 'subspace-pts d2-M 'U)
(fact 'nf-neg-in-carr 'K 'd2a_)
(define d2-uq-lim (dk-fact! 'nf-open-limit-point 'K 'U 'd2a_))
(mac-h 'IS-DIFF-ON '(IS-DIFF-ON K U d2f_ d2a_ d2l_))
(dk-split-all!)
(define d2-phi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the first factor")))
(dk-split-all!)
(define d2-cara1 (d2-cara-univ d2-phi))
(mac-h 'IS-DIFF-ON '(IS-DIFF-ON K U d2f_ d2a_ d2m_))
(dk-split-all!)
(define d2-psi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the second factor")))
(dk-split-all!)
(define d2-cara2 (d2-cara-univ d2-psi))

;;; the factors agree off a, stated over U
(dk-have! (list 'FORALL 'd2y_
            (list 'IMPLIES '(IN d2y_ U)
              (list 'IMPLIES '(NOT (= d2y_ d2a_))
                    (list '= (list d2-phi 'd2y_) (list d2-psi 'd2y_)))))
  (lambda ()
    (let ((y (dk-di-var!)))
      (di)
      (fact 'subset-mem-fwd 'U '(CARR K) y)
      (fact 'fun-apply-type-c d2-phi 'U '(CARR K) y)
      (fact 'fun-apply-type-c d2-psi 'U '(CARR K) y)
      (fact 'nf-add-in-carr 'K y (d2-neg 'd2a_))
      (dk-have! (list 'NOT (list '= (d2-sub y 'd2a_) '(ZERO K)))
        (lambda ()
          (di)
          (fact 'nf-sub-zero-eq 'K y 'd2a_)
          (ai (list 'NOT (list '= y 'd2a_)))))
      (dk-apply! d2-cara1 y)
      (dk-apply! d2-cara2 y)
      (let ((lhs (d2-sub (list 'd2f_ y) '(d2f_ d2a_)))
            (p1  (d2-mul (list d2-phi y) (d2-sub y 'd2a_)))
            (p2  (d2-mul (list d2-psi y) (d2-sub y 'd2a_))))
        (fact 'eq-sym lhs p1)
        (fact 'eq-trans p1 lhs p2))
      (fact 'nf-mul-cancel 'K (list d2-phi y) (list d2-psi y) (d2-sub y 'd2a_))
      (ass))))
(define d2-uq-agreeU
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (d2-head fm) 'FORALL)
                             (dk-contains? fm d2-phi) (dk-contains? fm d2-psi)))
           "the agreement universal over U"))

;;; the two universals, restated over PTS(W)
(dk-have! (list 'FORALL 'msr_
            (list 'IMPLIES '(POS-RR msr_)
              (list 'FORSOME 'msb_
                (list 'AND (list 'IN 'msb_ (list 'PTS d2-W))
                  (list 'AND '(NOT (= msb_ d2a_))
                    (list '<= (list (list 'DIST d2-W) 'd2a_ 'msb_) 'msr_))))))
  (lambda ()
    (let* ((peeled (dk-peel!))
           (r (cadr (dk-pick (lambda (fm) (and (member fm peeled)
                                               (eq? (d2-head fm) 'POS-RR)))
                             "POS-RR r")))
           (b (dk-skolem! (dk-apply! d2-uq-lim r))))
      (ew b)
      (dk-conj-close!
       (lambda ()
         (if (eq? (d2-head (dk-goal)) 'IN)
             (begin (subst (list '== (list 'PTS d2-W) 'U)) (ass))
             (ass)))))))

(dk-have! (list 'FORALL 'msy_
            (list 'IMPLIES (list 'IN 'msy_ (list 'PTS d2-W))
              (list 'IMPLIES '(NOT (= msy_ d2a_))
                    (list '= (list d2-phi 'msy_) (list d2-psi 'msy_)))))
  (lambda ()
    (let ((y (dk-di-var!)))
      (di)
      (dk-have! (list 'IN y 'U)
        (lambda () (subst (list '== 'U (list 'PTS d2-W))) (ass)))
      (dk-apply! d2-uq-agreeU y)
      (ass))))

(fact 'ms-cont-agree-off-pt d2-W d2-M d2-phi d2-psi 'd2a_)
(fact 'eq-sym (list d2-phi 'd2a_) 'd2l_)
(fact 'eq-trans 'd2l_ (list d2-phi 'd2a_) (list d2-psi 'd2a_))
(fact 'eq-trans 'd2l_ (list d2-psi 'd2a_) 'd2m_)
(ass)
(qed 'diff-on-unique)
(topic! 'diff-on-unique 'analysis)
(alias! 'diff-on-unique
        "the derivative on an open set is unique when the norm is not trivial")

;;; =====================================================================
;;; (7) THE RULES.  Constants, the identity, the sum.
;;;
;;; Each exhibits its Caratheodory factor as a LAMBDA OVER U, types it by (2),
;;; proves it continuous by the domain-named laws of (1), and closes the
;;; Caratheodory equation by `crs' through the ring view after `dk-lam-b!' has
;;; reduced every application of the lambdas at the peeled point.
;;; =====================================================================

(sp (make-wff '(FORALL K (IMPLIES (IS-NORMED-FIELD K) (IN (ONE K) (CARR K))))))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda () (mac-h 'is-normed-field '(IS-NORMED-FIELD K)))))
(ass)
(qed 'nf-one-in-carr)
(topic! 'nf-one-in-carr 'algebra)

;;; An open set of a normed field is a SET -- what `lam-t' asks of the domain
;;; of every lambda built over U.
(sp (make-wff (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
     (list 'FORALL 'U (list 'IMPLIES (list 'IS-OPEN d2-M 'U) '(IN U SET)))))))
(dk-peel!)
(fact 'nf-metric-carrier 'K)
(fact 'nf-metric-space-is-metric-space 'K)
(fact 'nf-open-subset-carr 'K 'U)
(dk-have! (list 'SUBSET 'U (list 'PTS d2-M))
  (lambda () (subst (list '== (list 'PTS d2-M) '(CARR K))) (ass)))
(fact 'subspace-is-metric-space d2-M 'U)
(fact 'subspace-pts d2-M 'U)
(fact 'ms-pts-is-set d2-W)
(subst (list '== 'U (list 'PTS d2-W)))
(ass)
(qed 'nf-open-is-set)
(topic! 'nf-open-is-set 'topology)
(alias! 'nf-open-is-set "an open set of a normed field is a set")

;;; ---- the shared setup -----------------------------------------------

(define (d2-space-setup!)
  (fact 'nf-metric-carrier 'K)
  (fact 'nf-metric-space-is-metric-space 'K)
  (fact 'nf-open-subset-carr 'K 'U)
  (dk-have! (list 'SUBSET 'U (list 'PTS d2-M))
    (lambda () (subst (list '== (list 'PTS d2-M) '(CARR K))) (ass)))
  (fact 'subspace-is-metric-space d2-M 'U)
  (fact 'subspace-pts d2-M 'U)
  (fact 'nf-open-is-set 'K 'U))

(define (d2-in-ptsW! t)
  (dk-have! (list 'IN t (list 'PTS d2-W))
    (lambda () (subst (list '== (list 'PTS d2-W) 'U)) (ass))))

(define (d2-in-ptsM! t)
  (dk-have! (list 'IN t (list 'PTS d2-M))
    (lambda () (subst (list '== (list 'PTS d2-M) '(CARR K))) (ass))))

;;; Drive the IS-DIFF-ON goal: unfold, close every conjunct but the existential
;;; from the context, exhibit PHI, and hand each of the factor's four conjuncts
;;; to BRANCH (which sees the goal and closes it).
(define (d2-diff-on! phi branch)
  (mac 'IS-DIFF-ON)
  (dk-conj-close!
   (lambda ()
     (if (not (eq? (d2-head (dk-goal)) 'FORSOME))
         (ass)
         (begin
           (ew phi)
           (dk-conj-close! branch))))))

;;; ---- the constant ----------------------------------------------------

(sp (make-wff
     (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
       (list 'FORALL 'U (list 'IMPLIES (list 'IS-OPEN d2-M 'U)
         (list 'FORALL 'd2c_ (list 'IMPLIES '(IN d2c_ (CARR K))
           (list 'FORALL 'd2a_ (list 'IMPLIES '(IN d2a_ U)
             (list 'IS-DIFF-ON 'K 'U '(VNB-LAMBDA d2x_ U d2c_)
                   'd2a_ '(ZERO K))))))))))))
(dk-peel!)
(d2-space-setup!)
(fact 'nf-zero-in-carr 'K)
(fact 'subset-mem-fwd 'U '(CARR K) 'd2a_)
(d2-in-ptsW! 'd2a_)
(d2-in-ptsM! '(ZERO K))
(fact 'nf-lam-const-in-fun 'K 'U 'd2c_)
(fact 'nf-lam-const-in-fun 'K 'U '(ZERO K))
(fact 'ms-const-continuous-on d2-W 'U d2-M '(ZERO K) 'd2a_)
(d2-diff-on! '(VNB-LAMBDA d2x_ U (ZERO K))
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (d2-head g) 'FORALL)
            (let ((x (dk-di-var!)))
              (fact 'subset-mem-fwd 'U '(CARR K) x)
              (dk-lam-b!)
              (d2-ring-id! (list 'd2c_ x 'd2a_))))
           ((eq? (d2-head g) '=) (dk-lam-b!) (rfl))
           (#t (ass))))))
(qed 'diff-on-const)
(topic! 'diff-on-const 'analysis)
(alias! 'diff-on-const "a constant is differentiable with derivative zero")

;;; ---- the identity ----------------------------------------------------

(sp (make-wff
     (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
       (list 'FORALL 'U (list 'IMPLIES (list 'IS-OPEN d2-M 'U)
         (list 'FORALL 'd2a_ (list 'IMPLIES '(IN d2a_ U)
           (list 'IS-DIFF-ON 'K 'U '(VNB-LAMBDA d2x_ U d2x_)
                 'd2a_ '(ONE K)))))))))) 
(dk-peel!)
(d2-space-setup!)
(fact 'nf-one-in-carr 'K)
(fact 'subset-mem-fwd 'U '(CARR K) 'd2a_)
(d2-in-ptsW! 'd2a_)
(d2-in-ptsM! '(ONE K))
(fact 'nf-lam-id-in-fun 'K 'U)
(fact 'nf-lam-const-in-fun 'K 'U '(ONE K))
(fact 'ms-const-continuous-on d2-W 'U d2-M '(ONE K) 'd2a_)
(d2-diff-on! '(VNB-LAMBDA d2x_ U (ONE K))
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (d2-head g) 'FORALL)
            (let ((x (dk-di-var!)))
              (fact 'subset-mem-fwd 'U '(CARR K) x)
              (dk-lam-b!)
              (d2-ring-id! (list x 'd2a_))))
           ((eq? (d2-head g) '=) (dk-lam-b!) (rfl))
           (#t (ass))))))
(qed 'diff-on-identity)
(topic! 'diff-on-identity 'analysis)
(alias! 'diff-on-identity "the identity is differentiable with derivative one")

;;; ---- the sum ---------------------------------------------------------
;;;
;;; The factor is x |-> phi(x) + psi(x), and the Caratheodory equation is
;;;   (f+g)(x) - (f+g)(a) = (f(x)-f(a)) + (g(x)-g(a))
;;;                       = phi(x).(x-a) + psi(x).(x-a)
;;;                       = (phi(x)+psi(x)).(x-a),
;;; the first and the last steps ring identities of K and the middle one the
;;; two hypotheses substituted in.

(sp (make-wff
     (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
       '(FORALL U (FORALL d2f_ (FORALL d2g_ (FORALL d2a_ (FORALL d2l_ (FORALL d2m_
          (IMPLIES (IS-DIFF-ON K U d2f_ d2a_ d2l_)
            (IMPLIES (IS-DIFF-ON K U d2g_ d2a_ d2m_)
              (IS-DIFF-ON K U
                (VNB-LAMBDA d2x_ U ((ADD K) (d2f_ d2x_) (d2g_ d2x_)))
                d2a_ ((ADD K) d2l_ d2m_))))))))))))))
(dk-peel!)
(fact 'diff-on-open 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-pt-in 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-in-fun 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-in-fun 'K 'U 'd2g_ 'd2a_ 'd2m_)
(fact 'diff-on-deriv-in-carr 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-deriv-in-carr 'K 'U 'd2g_ 'd2a_ 'd2m_)
(d2-space-setup!)
(fact 'subset-mem-fwd 'U '(CARR K) 'd2a_)
(d2-in-ptsW! 'd2a_)
(fact 'nf-add-in-carr 'K 'd2l_ 'd2m_)
(fact 'nf-lam-sum-in-fun 'K 'U 'd2f_ 'd2g_)
(mac-h 'IS-DIFF-ON '(IS-DIFF-ON K U d2f_ d2a_ d2l_))
(dk-split-all!)
(define d2-sphi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the first factor")))
(dk-split-all!)
(define d2-scara1 (d2-cara-univ d2-sphi))
(mac-h 'IS-DIFF-ON '(IS-DIFF-ON K U d2g_ d2a_ d2m_))
(dk-split-all!)
(define d2-spsi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the second factor")))
(dk-split-all!)
(define d2-scara2 (d2-cara-univ d2-spsi))
(fact 'nf-lam-sum-in-fun 'K 'U d2-sphi d2-spsi)
(fact 'nf-sum-continuous-on 'K d2-W 'U d2-sphi d2-spsi 'd2a_)
(d2-diff-on!
 (list 'VNB-LAMBDA 'd2x_ 'U (d2-add (list d2-sphi 'd2x_) (list d2-spsi 'd2x_)))
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (d2-head g) 'FORALL)
        (let ((x (dk-di-var!)))
          (fact 'subset-mem-fwd 'U '(CARR K) x)
          (dk-lam-b!)
          (fact 'fun-apply-type-c 'd2f_ 'U '(CARR K) x)
          (fact 'fun-apply-type-c 'd2f_ 'U '(CARR K) 'd2a_)
          (fact 'fun-apply-type-c 'd2g_ 'U '(CARR K) x)
          (fact 'fun-apply-type-c 'd2g_ 'U '(CARR K) 'd2a_)
          (fact 'fun-apply-type-c d2-sphi 'U '(CARR K) x)
          (fact 'fun-apply-type-c d2-spsi 'U '(CARR K) x)
          (dk-apply! d2-scara1 x)
          (dk-apply! d2-scara2 x)
          (let* ((fx (list 'd2f_ x)) (fa '(d2f_ d2a_))
                 (gx (list 'd2g_ x)) (ga '(d2g_ d2a_))
                 (dxa (d2-sub x 'd2a_))
                 (p1 (list d2-sphi x)) (p2 (list d2-spsi x)))
            (dk-have! (list '= (d2-sub (d2-add fx gx) (d2-add fa ga))
                               (d2-add (d2-sub fx fa) (d2-sub gx ga)))
              (lambda () (d2-ring-id! (list fx fa gx ga))))
            (subst (list '= (d2-sub (d2-add fx gx) (d2-add fa ga))
                            (d2-add (d2-sub fx fa) (d2-sub gx ga))))
            (subst (list '= (d2-sub fx fa) (d2-mul p1 dxa)))
            (subst (list '= (d2-sub gx ga) (d2-mul p2 dxa)))
            (d2-ring-id! (list p1 p2 x 'd2a_)))))
       ((eq? (d2-head g) '=)
        (dk-lam-b!)
        (subst (list '= (list d2-sphi 'd2a_) 'd2l_))
        (subst (list '= (list d2-spsi 'd2a_) 'd2m_))
        (rfl))
       (#t (ass))))))
(qed 'diff-on-sum)
(topic! 'diff-on-sum 'analysis)
(alias! 'diff-on-sum "the derivative of a sum is the sum of the derivatives")

;;; ---- the product -----------------------------------------------------
;;;
;;; The factor is x |-> phi(x).g(x) + psi(x).f(a), from
;;;   f(x)g(x) - f(a)g(a) = (f(x)-f(a)).g(x) + (g(x)-g(a)).f(a).
;;;
;;; THE ALPHA-VARIANTS BELOW ARE NOT DECORATION.  The factor is a SUM of two
;;; PRODUCTS, so the two product lambdas are substituted, as TERMS, into the
;;; sum law's own lambda -- and `subst-free' is capture-avoiding, so a
;;; substituted lambda whose binder is spelled like the binder it lands under
;;; is renamed and every later `equal?' lookup of the rebuilt term matches
;;; nothing, silently (CLAUDE.md, "Writing proof drivers").  The cure is to
;;; give the inner lambdas a binder of their own: `d2v_' for the products,
;;; `msz_' for the constant, `d2x_' for the outer sum.  Each variant costs one
;;; citation plus the `ass' that closes it, `ass' being alpha-aware.

(d2-lam-thm! 'nf-lam-const-z-in-fun '(VNB-LAMBDA msz_ U d2c_)
  '((d2c_ (IN d2c_ (CARR K))))
  (lambda (z) #t))
(topic! 'nf-lam-const-z-in-fun 'analysis)

(d2-lam-thm! 'nf-lam-prod-v-in-fun
  '(VNB-LAMBDA d2v_ U ((MUL K) (d2f_ d2v_) (d2g_ d2v_)))
  '((d2f_ (IN d2f_ (FUN U (CARR K)))) (d2g_ (IN d2g_ (FUN U (CARR K)))))
  (lambda (z)
    (fact 'fun-apply-type-c 'd2f_ 'U '(CARR K) z)
    (fact 'fun-apply-type-c 'd2g_ 'U '(CARR K) z)
    (fact 'nf-mul-in-carr 'K (list 'd2f_ z) (list 'd2g_ z))))
(topic! 'nf-lam-prod-v-in-fun 'analysis)

(d2-on-thm! 'nf-product-continuous-v
  (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
    (d2-on-stmt
     (list 'FORALL 'msg_ (list 'FORALL 'msh_ (list 'FORALL 'msa_
       (list 'IMPLIES (list 'IS-CONTINUOUS-AT 'mss_ d2-M 'msg_ 'msa_)
         (list 'IMPLIES (list 'IS-CONTINUOUS-AT 'mss_ d2-M 'msh_ 'msa_)
           (list 'IS-CONTINUOUS-AT 'mss_ d2-M
                 '(VNB-LAMBDA d2v_ d2d_ ((MUL K) (msg_ d2v_) (msh_ d2v_)))
                 'msa_)))))))))
  (lambda () (fact 'nf-product-continuous-at 'K 'mss_ 'msg_ 'msh_ 'msa_)))
(topic! 'nf-product-continuous-v 'analysis)

(sp (make-wff
     (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
       '(FORALL U (FORALL d2f_ (FORALL d2g_ (FORALL d2a_ (FORALL d2l_ (FORALL d2m_
          (IMPLIES (IS-DIFF-ON K U d2f_ d2a_ d2l_)
            (IMPLIES (IS-DIFF-ON K U d2g_ d2a_ d2m_)
              (IS-DIFF-ON K U
                (VNB-LAMBDA d2x_ U ((MUL K) (d2f_ d2x_) (d2g_ d2x_)))
                d2a_ ((ADD K) ((MUL K) d2l_ (d2g_ d2a_))
                              ((MUL K) d2m_ (d2f_ d2a_)))))))))))))))) 
(dk-peel!)
(fact 'diff-on-open 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-pt-in 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-in-fun 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-in-fun 'K 'U 'd2g_ 'd2a_ 'd2m_)
(fact 'diff-on-deriv-in-carr 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-deriv-in-carr 'K 'U 'd2g_ 'd2a_ 'd2m_)
(define d2-pg-cont (dk-fact! 'diff-on-implies-continuous 'K 'U 'd2g_ 'd2a_ 'd2m_))
(d2-space-setup!)
(fact 'subset-mem-fwd 'U '(CARR K) 'd2a_)
(d2-in-ptsW! 'd2a_)
(fact 'fun-apply-type-c 'd2f_ 'U '(CARR K) 'd2a_)
(fact 'fun-apply-type-c 'd2g_ 'U '(CARR K) 'd2a_)
(d2-in-ptsM! '(d2f_ d2a_))
(fact 'nf-mul-in-carr 'K 'd2l_ '(d2g_ d2a_))
(fact 'nf-mul-in-carr 'K 'd2m_ '(d2f_ d2a_))
(fact 'nf-add-in-carr 'K (d2-mul 'd2l_ '(d2g_ d2a_)) (d2-mul 'd2m_ '(d2f_ d2a_)))
(fact 'nf-lam-prod-in-fun 'K 'U 'd2f_ 'd2g_)
(fact 'nf-lam-const-z-in-fun 'K 'U '(d2f_ d2a_))
(fact 'ms-const-continuous-on d2-W 'U d2-M '(d2f_ d2a_) 'd2a_)
(mac-h 'IS-DIFF-ON '(IS-DIFF-ON K U d2f_ d2a_ d2l_))
(dk-split-all!)
(define d2-pphi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the first factor")))
(dk-split-all!)
(define d2-pcara1 (d2-cara-univ d2-pphi))
(mac-h 'IS-DIFF-ON '(IS-DIFF-ON K U d2g_ d2a_ d2m_))
(dk-split-all!)
(define d2-ppsi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the second factor")))
(dk-split-all!)
(define d2-pcara2 (d2-cara-univ d2-ppsi))
(define d2-cf (list 'VNB-LAMBDA 'msz_ 'U '(d2f_ d2a_)))
(define d2-p1 (list 'VNB-LAMBDA 'd2v_ 'U (d2-mul (list d2-pphi 'd2v_) '(d2g_ d2v_))))
(define d2-p2 (list 'VNB-LAMBDA 'd2v_ 'U (d2-mul (list d2-ppsi 'd2v_)
                                                 (list d2-cf 'd2v_))))
(fact 'nf-lam-prod-v-in-fun 'K 'U d2-pphi 'd2g_)
(fact 'nf-lam-prod-v-in-fun 'K 'U d2-ppsi d2-cf)
(fact 'nf-product-continuous-v 'K d2-W 'U d2-pphi 'd2g_ 'd2a_)
(fact 'nf-product-continuous-v 'K d2-W 'U d2-ppsi d2-cf 'd2a_)
(fact 'nf-lam-sum-in-fun 'K 'U d2-p1 d2-p2)
(fact 'nf-sum-continuous-on 'K d2-W 'U d2-p1 d2-p2 'd2a_)
(d2-diff-on!
 (list 'VNB-LAMBDA 'd2x_ 'U (d2-add (list d2-p1 'd2x_) (list d2-p2 'd2x_)))
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (d2-head g) 'FORALL)
        (let ((x (dk-di-var!)))
          (fact 'subset-mem-fwd 'U '(CARR K) x)
          (dk-lam-b!)
          (fact 'fun-apply-type-c 'd2f_ 'U '(CARR K) x)
          (fact 'fun-apply-type-c 'd2g_ 'U '(CARR K) x)
          (fact 'fun-apply-type-c d2-pphi 'U '(CARR K) x)
          (fact 'fun-apply-type-c d2-ppsi 'U '(CARR K) x)
          (dk-apply! d2-pcara1 x)
          (dk-apply! d2-pcara2 x)
          (let* ((fx (list 'd2f_ x)) (fa '(d2f_ d2a_))
                 (gx (list 'd2g_ x)) (ga '(d2g_ d2a_))
                 (dxa (d2-sub x 'd2a_))
                 (p1 (list d2-pphi x)) (p2 (list d2-ppsi x)))
            (dk-have! (list '= (d2-sub (d2-mul fx gx) (d2-mul fa ga))
                               (d2-add (d2-mul (d2-sub fx fa) gx)
                                       (d2-mul (d2-sub gx ga) fa)))
              (lambda () (d2-ring-id! (list fx fa gx ga))))
            (subst (list '= (d2-sub (d2-mul fx gx) (d2-mul fa ga))
                            (d2-add (d2-mul (d2-sub fx fa) gx)
                                    (d2-mul (d2-sub gx ga) fa))))
            (subst (list '= (d2-sub fx fa) (d2-mul p1 dxa)))
            (subst (list '= (d2-sub gx ga) (d2-mul p2 dxa)))
            (d2-ring-id! (list p1 p2 fa gx x 'd2a_)))))
       ((eq? (d2-head g) '=)
        (dk-lam-b!)
        (subst (list '= (list d2-pphi 'd2a_) 'd2l_))
        (subst (list '= (list d2-ppsi 'd2a_) 'd2m_))
        (rfl))
       (#t (ass))))))
(qed 'diff-on-product)
(topic! 'diff-on-product 'analysis)
(alias! 'diff-on-product "the Leibniz rule on an open set")

;;; ---- the chain rule --------------------------------------------------
;;;
;;; f is differentiable on U at a, g on V at f(a), and f carries U into V.  The
;;; factor of g o f is x |-> psi(f(x)) . phi(x), from
;;;   g(f(x)) - g(f(a)) = psi(f(x)).(f(x)-f(a)) = psi(f(x)).phi(x).(x-a).
;;;
;;; THE ONE BRICK THAT WAS MISSING is the CORESTRICTION of a continuous map:
;;; `diff-on-implies-continuous' gives f continuous from SUBSPACE-MS(M,U) into
;;; M, and the composition law needs it continuous into SUBSPACE-MS(M,V), whose
;;; distance is the same on V (`subspace-dist') and whose FUN typing is
;;; `fun-codomain-iff' at the smaller codomain.

(sp (make-wff
     '(FORALL mss_ (FORALL mst_ (IMPLIES (IS-METRIC-SPACE mst_)
        (FORALL d2s_ (IMPLIES (SUBSET d2s_ (PTS mst_))
          (FORALL msf_ (FORALL msa_
            (IMPLIES (IS-CONTINUOUS-AT mss_ mst_ msf_ msa_)
              (IMPLIES (FORALL msy_ (IMPLIES (IN msy_ (PTS mss_))
                         (IN (msf_ msy_) d2s_)))
                (IS-CONTINUOUS-AT mss_ (SUBSPACE-MS mst_ d2s_) msf_ msa_)))))))))))) 
(define d2-cor-landed (dk-peel!))
(define d2-cor-into
  (dk-pick (lambda (fm) (and (member fm d2-cor-landed) (eq? (d2-head fm) 'FORALL)
                             (dk-contains? fm 'msf_)))
           "the into-V universal"))
(fact 'subspace-is-metric-space 'mst_ 'd2s_)
(fact 'subspace-pts 'mst_ 'd2s_)
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT mss_ mst_ msf_ msa_))
(dk-split-all!)
(dk-have! '(IN msf_ (FUN (PTS mss_)))
  (lambda () (fact 'fun-codomain-iff '(PTS mss_) '(PTS mst_) 'msf_) (prop)))
(dk-have! '(IN msf_ (FUN (PTS mss_) d2s_))
  (lambda () (fact 'fun-codomain-iff '(PTS mss_) 'd2s_ 'msf_) (prop)))
(mac 'IS-CONTINUOUS-AT)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((and (eq? (d2-head g) 'IN) (pair? (caddr g)) (eq? (car (caddr g)) 'FUN))
        (subst '(== (PTS (SUBSPACE-MS mst_ d2s_)) d2s_)) (ass))
       ((eq? (d2-head g) 'FORALL)
        (dk-peel!)
        (let* ((eps (cadr (dk-pick (dk-head? 'POS-RR) "POS-RR eps")))
               (del (dk-skolem!
                     (dk-apply! (dk-pick (lambda (fm)
                                           (and (pair? fm) (eq? (d2-head fm) 'FORALL)
                                                (dk-contains? fm 'FORSOME)
                                                (dk-contains? fm 'DIST)))
                                         "the eps universal")
                                eps))))
          (ew del)
          (dk-conj-close!
           (lambda ()
             (if (eq? (d2-head (dk-goal)) 'POS-RR)
                 (ass)
                 (let ((b (dk-di-var!)))
                   (dk-peel!)
                   (dk-apply! d2-cor-into 'msa_)
                   (dk-apply! d2-cor-into b)
                   (dk-apply! (dk-pick (lambda (fm)
                                         (and (pair? fm) (eq? (d2-head fm) 'FORALL)
                                              (dk-contains? fm del)))
                                       "the delta universal")
                              b)
                   (fact 'subspace-dist 'mst_ 'd2s_ '(msf_ msa_) (list 'msf_ b))
                   (subst (list '== (list '(DIST (SUBSPACE-MS mst_ d2s_))
                                          '(msf_ msa_) (list 'msf_ b))
                                    (list '(DIST mst_) '(msf_ msa_) (list 'msf_ b))))
                   (ass)))))))
       (#t (ass))))))
(qed 'ms-corestrict-continuous)
(topic! 'ms-corestrict-continuous 'analysis)
(alias! 'ms-corestrict-continuous
        "a continuous map taking its values in a subset is continuous into the subspace")

;;; The composite lambda is a function on U.
(sp (make-wff
     '(FORALL K (IMPLIES (IS-NORMED-FIELD K)
        (FORALL U (IMPLIES (IN U SET)
          (FORALL d2s_ (FORALL d2f_ (FORALL d2g_
            (IMPLIES (IN d2g_ (FUN d2s_ (CARR K)))
              (IMPLIES (FORALL d2y_ (IMPLIES (IN d2y_ U) (IN (d2f_ d2y_) d2s_)))
                (IN (VNB-LAMBDA msz_ U (d2g_ (d2f_ msz_)))
                    (FUN U (CARR K))))))))))))))
(define d2-cz-landed (dk-peel!))
(define d2-cz-into
  (dk-pick (lambda (fm) (and (member fm d2-cz-landed) (eq? (d2-head fm) 'FORALL)
                             (dk-contains? fm 'd2f_)))
           "the into-V universal"))
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (d2-head (dk-goal)) 'FORALL)
       (let ((z (dk-di-var!)))
         (dk-apply! d2-cz-into z)
         (fact 'fun-apply-type-c 'd2g_ 'd2s_ '(CARR K) (list 'd2f_ z))
         (ass))
       (ass)))
 (dk-opened (lambda () (lam-t))))
(qed 'nf-lam-comp-z-in-fun)
(topic! 'nf-lam-comp-z-in-fun 'analysis)

;;; ---- diff-on-chain ---------------------------------------------------

(define (d2-wof s) (list 'SUBSPACE-MS d2-M s))

(sp (make-wff
     (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
       '(FORALL U (FORALL d2s_ (FORALL d2f_ (FORALL d2g_ (FORALL d2a_
          (FORALL d2l_ (FORALL d2m_
            (IMPLIES (IS-DIFF-ON K U d2f_ d2a_ d2l_)
              (IMPLIES (IS-DIFF-ON K d2s_ d2g_ (d2f_ d2a_) d2m_)
                (IMPLIES (FORALL d2y_ (IMPLIES (IN d2y_ U) (IN (d2f_ d2y_) d2s_)))
                  (IS-DIFF-ON K U (VNB-LAMBDA d2x_ U (d2g_ (d2f_ d2x_)))
                              d2a_ ((MUL K) d2m_ d2l_)))))))))))))))) 
(define d2-ch-landed (dk-peel!))
(define d2-ch-into
  (dk-pick (lambda (fm) (and (member fm d2-ch-landed) (eq? (d2-head fm) 'FORALL)
                             (dk-contains? fm 'd2f_)))
           "the into-V universal"))
(fact 'diff-on-open 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-pt-in 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-in-fun 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-open 'K 'd2s_ 'd2g_ '(d2f_ d2a_) 'd2m_)
(fact 'diff-on-pt-in 'K 'd2s_ 'd2g_ '(d2f_ d2a_) 'd2m_)
(fact 'diff-on-in-fun 'K 'd2s_ 'd2g_ '(d2f_ d2a_) 'd2m_)
(fact 'diff-on-deriv-in-carr 'K 'U 'd2f_ 'd2a_ 'd2l_)
(fact 'diff-on-deriv-in-carr 'K 'd2s_ 'd2g_ '(d2f_ d2a_) 'd2m_)
(define d2-ch-fcont (dk-fact! 'diff-on-implies-continuous 'K 'U 'd2f_ 'd2a_ 'd2l_))
(d2-space-setup!)
(fact 'nf-open-subset-carr 'K 'd2s_)
(fact 'nf-open-is-set 'K 'd2s_)
(dk-have! (list 'SUBSET 'd2s_ (list 'PTS d2-M))
  (lambda () (subst (list '== (list 'PTS d2-M) '(CARR K))) (ass)))
(fact 'subspace-is-metric-space d2-M 'd2s_)
(fact 'subspace-pts d2-M 'd2s_)
(fact 'subset-mem-fwd 'U '(CARR K) 'd2a_)
(d2-in-ptsW! 'd2a_)
(fact 'nf-mul-in-carr 'K 'd2m_ 'd2l_)
(fact 'nf-lam-comp-z-in-fun 'K 'U 'd2s_ 'd2f_ 'd2g_)
;; the into-V universal, restated over PTS(W_U), for the corestriction
(dk-have! (list 'FORALL 'msy_
            (list 'IMPLIES (list 'IN 'msy_ (list 'PTS d2-W))
                           '(IN (d2f_ msy_) d2s_)))
  (lambda ()
    (let ((y (dk-di-var!)))
      (dk-have! (list 'IN y 'U)
        (lambda () (subst (list '== 'U (list 'PTS d2-W))) (ass)))
      (dk-apply! d2-ch-into y)
      (ass))))
(fact 'ms-corestrict-continuous d2-W d2-M 'd2s_ 'd2f_ 'd2a_)
(mac-h 'IS-DIFF-ON '(IS-DIFF-ON K U d2f_ d2a_ d2l_))
(dk-split-all!)
(define d2-chphi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the inner factor")))
(dk-split-all!)
(define d2-chcara1 (d2-cara-univ d2-chphi))
(mac-h 'IS-DIFF-ON '(IS-DIFF-ON K d2s_ d2g_ (d2f_ d2a_) d2m_))
(dk-split-all!)
(define d2-chpsi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the outer factor")))
(dk-split-all!)
(define d2-chcara2 (d2-cara-univ d2-chpsi))
(define d2-chq (list 'VNB-LAMBDA 'msz_ 'U (list d2-chpsi '(d2f_ msz_))))
(fact 'nf-lam-comp-z-in-fun 'K 'U 'd2s_ 'd2f_ d2-chpsi)
(fact 'ms-compose-continuous-on d2-W 'U (d2-wof 'd2s_) d2-M 'd2f_ d2-chpsi 'd2a_)
(fact 'nf-lam-prod-v-in-fun 'K 'U d2-chq d2-chphi)
(fact 'nf-product-continuous-v 'K d2-W 'U d2-chq d2-chphi 'd2a_)
(d2-diff-on!
 (list 'VNB-LAMBDA 'd2v_ 'U (d2-mul (list d2-chq 'd2v_) (list d2-chphi 'd2v_)))
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (d2-head g) 'FORALL)
        (let ((x (dk-di-var!)))
          (fact 'subset-mem-fwd 'U '(CARR K) x)
          (dk-lam-b!)
          (dk-apply! d2-ch-into x)
          (fact 'fun-apply-type-c 'd2f_ 'U '(CARR K) x)
          (fact 'fun-apply-type-c 'd2f_ 'U '(CARR K) 'd2a_)
          (fact 'fun-apply-type-c d2-chphi 'U '(CARR K) x)
          (fact 'fun-apply-type-c d2-chpsi 'd2s_ '(CARR K) (list 'd2f_ x))
          (dk-apply! d2-chcara1 x)
          (dk-apply! d2-chcara2 (list 'd2f_ x))
          (let* ((fx (list 'd2f_ x)) (fa '(d2f_ d2a_))
                 (dxa (d2-sub x 'd2a_))
                 (ph (list d2-chphi x)) (ps (list d2-chpsi fx)))
            (subst (list '= (d2-sub (list 'd2g_ fx) (list 'd2g_ fa))
                            (d2-mul ps (d2-sub fx fa))))
            (subst (list '= (d2-sub fx fa) (d2-mul ph dxa)))
            (d2-ring-id! (list ph ps x 'd2a_)))))
       ((eq? (d2-head g) '=)
        (dk-lam-b!)
        (subst (list '= (list d2-chpsi '(d2f_ d2a_)) 'd2m_))
        (subst (list '= (list d2-chphi 'd2a_) 'd2l_))
        (rfl))
       (#t (ass))))))
(qed 'diff-on-chain)
(topic! 'diff-on-chain 'analysis)
(alias! 'diff-on-chain "the chain rule on open sets")
