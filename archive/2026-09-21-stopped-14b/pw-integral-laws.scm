;;; pw-integral-laws.scm -- STAGE 1 of batch 14-B: the laws of
;;; IS-PW-ANTIDERIVATIVE and of PW-INT.
;;;
;;; The definitions are structure-library/pw-integral.scm; the design note is
;;; docs/paths-and-line-integrals-2026-09-21.md, section 3.2.  The statement
;;; checks -- what was verified about each definition BEFORE anything was proven
;;; -- are written out in the header of the definitions file.
;;;
;;; THE ORDER, which is the order of the brief:
;;;   1. the projections of the defining conjunction;
;;;   2. every IS-ANTIDERIVATIVE is an IS-PW-ANTIDERIVATIVE (one piece);
;;;   3. the UNIQUENESS obligation of the IOTA: two PW-antiderivatives of one phi
;;;      have the same endpoint difference;
;;;   4. PW-INT's value equation, its definedness, and its agreement with C-INT;
;;;   5. linearity.
;;;
;;; THE ROUTE TO (3), AND WHY IT IS NOT AN INDUCTION ON THE NUMBER OF PIECES.
;;; Two PW-antiderivatives of one phi carry TWO DIFFERENT partitions, and the
;;; difference pf - pg has derivative 0 only off the UNION of their partition
;;; points.  An induction on the number of pieces of one partition therefore does
;;; not reach the statement: it would need the common refinement of two finite
;;; sequences, i.e. a sorted merge, which is a serious piece of set-theoretic
;;; work with nothing else in the tree to buy from it.
;;;
;;; So the exceptional set is taken as a FINITE SET rather than as a partition
;;; for the length of the argument.  The workhorse is
;;;
;;;   pw-zero-deriv-endpoints:  H continuous on [a, b], D a finite set, and
;;;                             IS-DIFF-AT(H, t, 0) at every t of (a, b) OUTSIDE
;;;                             D  ==>  H(b) = H(a),
;;;
;;; proved by `finite-set-induction' on D (the models are
;;; theorem-library/nn-finite-subset-bounded.scm and card-subset-nn.scm): the base
;;; is `deriv-zero-implies-constant' (Cor 2.15) verbatim, and the step splits
;;; [a, b] at the inserted point when it falls inside, which is where the two
;;; halves of the induction hypothesis are used.  NO SORTING and NO REFINEMENT
;;; appear anywhere.  A partition feeds it through
;;; `partition-locates-point': the image of the index interval is a finite set,
;;; and a point of (a, b) outside that image is interior to some piece.
;;;
;;; Helper prefix: `pwi-'.

;;; =====================================================================
;;; File-local driver helpers.
;;; =====================================================================

;;; The one-piece partition of [a, b]:  k |-> a + k * (b - a).
;;; LINEAR and not an IF-tower on purpose -- monotonicity is then one citation of
;;; rr-mul-pos instead of a case analysis on the two indices, and p(0) = a,
;;; p(1) = b are each one `crs'.  The binder `kv_' is spelled like nothing any
;;; predicate body binds (IS-PARTITION binds i_ and j_; the design's own clauses
;;; bind idx_ and tv_), so `subst-free' never has to rename it.
(define (pwi-line-lam lo hi)
  (list 'VNB-LAMBDA 'kv_ 'NN (list '+ lo (list '* 'kv_ (list '- hi lo)))))

;;; Split an AND goal down to its leaves and run HANDLER on each.
(define (pwi-each-conjunct! handler)
  (dk-conj-close! (lambda () (handler (dk-goal)))))

;;; Peel a universal whose guard is a CONJUNCTION: `di' takes the binders, the
;;; NEXT `di' lands the antecedent, and the landing is split.  Returns the list
;;; of atoms that landed.  Loops on the LANDING, never on a count.
(define (pwi-peel-guarded!)
  (let ((landed (dk-peel!)))
    (dk-split-all! landed)))

;;; The context formula with head H that mentions SYM.
(define (pwi-find head sym)
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) head) (dk-contains? f sym)))
           (string-append "a " (symbol->string head) " mentioning "
                          (symbol->string sym))))

;;; =====================================================================
;;; 1.  THE PROJECTIONS.  `mac-h' REPLACES the hypothesis it unfolds, so a proof
;;; that needs one conjunct while keeping IS-PW-ANTIDERIVATIVE itself cannot get
;;; it by unfolding in the main branch.  Same reason antiderivative-map-in-fun
;;; exists beside IS-ANTIDERIVATIVE.
;;; =====================================================================

(define (pwi-project! goal)
  (quietly (lambda ()
    (sp (make-wff
         (list 'FORALL 'pf (list 'FORALL 'phi (list 'FORALL 'a (list 'FORALL 'b
           (list 'IMPLIES '(IS-PW-ANTIDERIVATIVE pf phi a b) goal)))))))
    (dk-peel-to! (car goal))
    (mac-h 'IS-PW-ANTIDERIVATIVE '(IS-PW-ANTIDERIVATIVE pf phi a b))
    (dk-split! (car (dk-asms)))
    (prop))))

(pwi-project! '(IN pf (FUN RR RR)))
(qed 'pw-antiderivative-map-in-fun)
(topic! 'pw-antiderivative-map-in-fun 'analysis)

(pwi-project! '(IN phi (FUN RR RR)))
(qed 'pw-antiderivative-fn-in-fun)
(topic! 'pw-antiderivative-fn-in-fun 'analysis)

(pwi-project! '(AND (IN a RR) (AND (IN b RR) (< a b))))
(qed 'pw-antiderivative-endpoints)
(topic! 'pw-antiderivative-endpoints 'analysis)
(alias! 'pw-antiderivative-endpoints
        "a piecewise antiderivative is taken on a nondegenerate [a,b]")

(pwi-project! '(FORALL xv_ (IMPLIES (IN xv_ (CCINT a b))
                            (IS-CONTINUOUS-AT RR-MS RR-MS pf xv_))))
(qed 'pw-antiderivative-continuous)
(topic! 'pw-antiderivative-continuous 'analysis)

;;; =====================================================================
;;; 2.  EVERY IS-ANTIDERIVATIVE IS AN IS-PW-ANTIDERIVATIVE -- one piece.
;;;
;;; This is what keeps the sixty existing Chapter 4 results usable: the partition
;;; is [a, b] itself, and the derivative clause of Def 4.6 is the new clause at
;;; the single index 0.
;;;
;;; The mechanical points.  The index `idx_' of the new clause is only known to
;;; satisfy idx_ < 1, so p(idx_) and p(succ idx_) are not syntactically a and b:
;;; nn-lt-succ-le + nn-succ-le-cancel + nn-le-zero-is-zero make idx_ = 0 in three
;;; citations, and the two VALUES are then read off by `subst' of that equation
;;; inside a `have!' lane.  Going the other way -- substituting a for p(idx_) in
;;; the goal -- would rewrite the `a' that occurs INSIDE the lambda body.
;;; =====================================================================

(define pwi-ab-lam (pwi-line-lam 'a 'b))

;;; (IS-PARTITION (k |-> a + k*(b-a)) 1 a b), with a, b in RR and a < b in context.
(define (pwi-one-piece-partition!)
  (mac 'is-partition)
  (fact 'nn-one-in)
  (fact 'nn-zero-in)
  (fact 'nn-le-refl 1)
  (fact 'rr-sub-in-rr 'b 'a)
  (pwi-each-conjunct!
   (lambda (g)
     (cond
       ;; (IN 1 NN), (<= 1 1), (IN a RR), (IN b RR), (< a b)
       ((and (memq (car g) '(IN <)) (not (pair? (cadr g)))) (ass))
       ;; (IN 1 NN) written with a compound -- not reached; the FUN typing:
       ((eq? (car g) 'IN) (dk-lam-fun!))
       ;; (= (p 0) a) and (= (p 1) b)
       ((eq? (car g) '=) (dk-lam-b!) (crs))
       ;; monotonicity
       (else (pwi-partition-monotone!))))))

(define (pwi-partition-monotone!)
  (let ((landed (pwi-peel-guarded!)))
    landed)
  (let* ((g  (dk-goal))                       ; (< (p i_) (p j_))
         (iv (caddr (cadr g)))
         (jv (caddr (caddr g))))
    (fact 'interval-elt-in-nn 0 1 iv)
    (fact 'interval-elt-in-nn 0 1 jv)
    (fact 'nn-in-rr iv)
    (fact 'nn-in-rr jv)
    (dk-lam-b!)
    (let ((dba (list '- 'b 'a))
          (dji (list '- jv iv)))
      (fact 'rr-sub-in-rr 'b 'a)
      (fact 'rr-sub-in-rr jv iv)
      (fact 'rr-mul-in-rr iv dba)
      (fact 'rr-mul-in-rr dji dba)
      (have! (list '< 0 dba) (lambda () (dk-ineq! '(< a b))))
      (have! (list '< 0 dji) (lambda () (dk-ineq! (list '< iv jv))))
      (fact 'rr-mul-pos dji dba)
      (let ((lo (list '+ 'a (list '* iv dba)))
            (hi (list '+ 'a (list '* jv dba))))
        (have! (list '= hi (list '+ lo (list '* dji dba))) (lambda () (crs)))
        (subst (list '= hi (list '+ lo (list '* dji dba))))
        (dk-ineq! (list '< 0 (list '* dji dba)))))))

(quietly (lambda ()
(sp (make-wff
     '(FORALL pf (FORALL phi (FORALL a (FORALL b
        (IMPLIES (IS-ANTIDERIVATIVE pf phi a b)
                 (IS-PW-ANTIDERIVATIVE pf phi a b))))))))
(dk-peel-to! 'IS-PW-ANTIDERIVATIVE)
(dk-split! (dk-landed-1
             (lambda () (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE pf phi a b)))))
(mac 'IS-PW-ANTIDERIVATIVE)
(pwi-each-conjunct!
 (lambda (g)
   (cond
     ((eq? (car g) 'FORSOME)
      (ew 1)
      (ew pwi-ab-lam)
      (dk-each-leaf!
       (lambda () (di))
       (lambda ()
         (if (eq? (car (dk-goal)) 'IS-PARTITION)
             (pwi-one-piece-partition!)
             (pwi-anti-diff-clause!)))))
     (#t (ass)))))))
(qed 'antiderivative-is-pw-antiderivative)
(topic! 'antiderivative-is-pw-antiderivative 'analysis)
(alias! 'antiderivative-is-pw-antiderivative
        "an antiderivative is a piecewise antiderivative, with one piece")
