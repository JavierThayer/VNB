;;; theorem-library/rake-finsum-cm-ptwise.scm -- finsum-comm-monoid-type-ptwise,
;;; the COMMUTATIVE-MONOID twin of `finsum-type-ptwise'.  Rake batch 5c-K.
;;;
;;;   m a commutative monoid, S a finite set, and f typed POINTWISE on S
;;;   (forall z in S. f z in CARR(m))   =>   FINSUM(m, f, S) in CARR(m).
;;;
;;; WHY IT IS WANTED.  `finsum-comm-monoid-type' (proven,
;;; theorem-library/rake-finsum-typing.scm) wants f in FUN(S, CARR m); a summand
;;; that has been back-peeled off a larger family, or built as a lambda, is never
;;; that -- it is typed only pointwise.  The ABELIAN-GROUP side has carried the
;;; pointwise form since batch J (`finsum-type-ptwise',
;;; theorem-library/rake-finsum-laws.scm); the comm-monoid side did not, and batch
;;; 5b-H's report names exactly this as the MISSING BRICK blocking its X10/X11 and
;;; the RR-POS-STAR measure leaves downstream of them (RR-POS-STAR is a commutative
;;; monoid under `eplus' and has no additive inverses, so the abelian-group FINSUM
;;; laws do not reach it at all).
;;;
;;; THE ROUTE is `finsum-type-ptwise's, unchanged: FINSUM(m,f,S) is DEFINED as
;;; SUM-AG(m, ENUM-FAM(m,f,FIN-ENUM S,|S|), |S|), so the whole content is that the
;;; enumerated family lands in the carrier on ORD-SEGMENT(|S|), which
;;; `enum-fam-value' reads off in one step; `sum-ag-comm-monoid-type-ptwise'
;;; (theorem-library/rake-finsum-core.scm) is the fold-length lemma at the other
;;; end.  `enum-fam-value' is stated with no structure hypothesis at all, so the
;;; abelian-group and comm-monoid proofs differ in exactly two citations.
;;;
;;; The FUN typing of FIN-ENUM(S) is taken INLINE, by unfolding the definitional
;;; `bijection-membership-iff' on the hypothesis, as both of the models do.
;;;
;;; LOAD WINDOW [252, end).  lo = 252 is forced by
;;; theorem-library/rake-finsum-core (251, sum-ag-comm-monoid-type-ptwise); the
;;; next-latest citations are theorem-library/rake-finsum-laws (249,
;;; enum-fam-value), theorem-library/finsum-insert (233, fin-enum-is-bijection),
;;; theorem-library/fun-apply-type-proof (160, fun-apply-type-c),
;;; theorem-library/ord-segment-nn-subset-proof (152, ord-segment-nn-subset) and
;;; structure-library/bijection (81, bijection-membership-iff).  Nothing cites
;;; this theorem yet -- it is a new name, not a PSS support -- so no citer forces
;;; `hi'.
;;;
;;; NOTHING TO RETIRE: this file installs a new theorem and proves no support.
;;;
;;; Helper prefix: r7k2-.

(define (r7k2-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; r7k2: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "r7k2: proof not complete" name))))

;; (FORALL v (IMPLIES (IN v DOM) BODY)), DOM a term
(define (r7k2-guarded-forall? f dom)
  (and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3)
       (let ((b (caddr f)))
         (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
              (let ((a (cadr b)))
                (and (pair? a) (eq? (car a) 'IN) (= (length a) 3)
                     (equal? (caddr a) dom)))))))

;; ... whose INNER formula satisfies PRED
(define (r7k2-guarded-forall-inner? f dom pred)
  (and (r7k2-guarded-forall? f dom)
       (pred (caddr (caddr f)))))

;; the eigenvariable of the ORD-SEGMENT typing among LANDED
(define (r7k2-seg-var landed)
  (let ((f (any-pred (lambda (g) (and (pair? g) (eq? (car g) 'IN) (symbol? (cadr g))
                                      (pair? (caddr g)) (eq? (car (caddr g)) 'ORD-SEGMENT)))
                     landed)))
    (if f (cadr f)
        (error "r7k2-seg-var: no ORD-SEGMENT typing landed"
               (map expression->string landed)))))

;;; ---------------------------------------------------------------------------
;;; finsum-comm-monoid-type-ptwise.  Stated in the shape `finsum-type-ptwise'
;;; uses (structure hypothesis, then S in SET and CARD S in NN, then the
;;; pointwise typing of f), so a citer can move between the two with one
;;; renaming and `dk-fact!' takes the same argument order.

(define r7k2-stmt
  '(FORALL m (IMPLIES (IS-COMM-MONOID m)
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
       (FORALL f (IMPLIES (FORALL z (IMPLIES (IN z S) (IN (f z) (CARR m))))
         (IN (FINSUM m f S) (CARR m))))))))))

(sp (make-wff r7k2-stmt))
(dk-peel!)
(let* ((gl  (dk-goal))
       (fs  (cadr gl))                       ; (FINSUM m f S)
       (mv  (cadr fs)) (fv (caddr fs)) (sv (cadddr fs))
       (nc  (list 'CARD sv))
       (phi (list 'FIN-ENUM sv))
       (seg (list 'ORD-SEGMENT nc))
       (ca  (list 'CARR mv))
       (fam (list 'ENUM-FAM mv fv phi nc))
       ;; picked BEFORE the bijection is opened: surjectivity is a guarded
       ;; universal over S too (CLAUDE.md, "never name an ASSUMPTION by shape").
       (typ (dk-pick (lambda (a) (r7k2-guarded-forall-inner? a sv
                                   (lambda (i) (and (pair? i) (eq? (car i) 'IN)))))
                     "forall z in S. f z in CARR(m)")))
  (mac 'FINSUM)
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
                                 (list 'IN (list fam 'i_) ca)))
         (lambda ()
           (let* ((landed (dk-peel!))
                  (iv     (r7k2-seg-var landed)))
             (dk-fact! 'ord-segment-nn-subset nc iv)
             (dk-fact! 'fun-apply-type-c phi seg sv iv)      ; (IN (phi i_) S)
             (dk-fact! 'enum-fam-value nc mv fv phi iv)
             (dk-apply! typ (list phi iv))                   ; (IN (f (phi i_)) (CARR m))
             (subst (list '== (list fam iv) (list fv (list phi iv))))
             (ass))))
  (dk-fact! 'sum-ag-comm-monoid-type-ptwise nc mv fam)
  (ass))
(r7k2-check! 'finsum-comm-monoid-type-ptwise)
(qed 'finsum-comm-monoid-type-ptwise)
(topic! 'finsum-comm-monoid-type-ptwise 'algebra)
