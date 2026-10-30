;;; mb-complete.scm -- construction-of-measures.pdf Prop. 3.2: a measure is complete iff
;;; "for every A, B subset X, if A (triangle) B is mu-null and A in A then B in A".
;;; Agent M-B, 2026-10-26.  DESTINATION: theorem-library/mb-complete.scm.  Library: measure.
;;;
;;;   sym-difference-unfold       the unfold of SYM-DIFFERENCE, as a theorem mac-h can name
;;;   null-set-subset             a subset of a null set is null (Def. 3.1, "clearly")
;;;   null-set-in-omega           a null set lies inside omega
;;;   complete-iff-symdiff        Prop. 3.2
;;;
;;; THE ROUTE (the notes'): necessity -- B \ A and A \ B lie in A triangle B, so they are null,
;;; so they are in cA by completeness, and B = (A \ (A \ B)) u (B \ A).  Sufficiency -- a null
;;; N is the symmetric difference of the empty set and N (up to inclusion), and the empty set
;;; is in cA.
;;; CITATIONS: is-measure, is-null-set, is-complete-measure, is-sigma-algebra, subset-trans,
;;; subset-def, power-set-membership, union-membership, complement-in-membership,
;;; empty-set-has-no-members, empty-subset-any, class-extensionality, sigma-algebra-empty-in,
;;; sigma-algebra-difference-closed, sigma-algebra-union-closed-2.
;;; LOAD WINDOW: after structure-library/mb-vocab and outer-measure-construction; no citer
;;; outside the M-B files (mb-completion cites null-set-subset and null-set-in-omega).
;;; Helper prefix: mbk-.

(define (mbk-qed! name) (qed name) (topic! name 'analysis))

(define (mbk-measure-parts! om ca mu)
  (let* ((iff (dk-fact! 'is-measure om ca mu))
         (rhs (caddr iff))
         (c1 (cadr rhs)) (c2 (cadr (caddr rhs))))
    (map (lambda (c) (dk-project! c 'IS-MEASURE (list 'IS-MEASURE om ca mu)))
         (list c1 c2))))

;;; goal (SUBSET X Y): open by subset-def, cite MEMB! on the fresh point, keep what mentions it,
;;; prop
(define (mbk-subset-prop! memb!)
  (mac 'subset-def)
  (let ((w (dk-di-var!)))
    (memb! w)
    (if (apply dk-only! (filter (lambda (f) (dk-contains? f w)) (dk-asms))) (prop))))

;;; goal (= X Y) for classes: extensionality, with MEMB! citing the membership laws at the point
(define (mbk-ext! x y memb!)
  (dk-have! (list 'FORALL 'mkw_ (list 'IFF (list 'IN 'mkw_ x) (list 'IN 'mkw_ y)))
    (lambda ()
      (let ((w (dk-di-var! (lambda (g) (cadr (cadr g))))))
        (memb! w)
        (if (apply dk-only! (filter (lambda (f) (dk-contains? f w)) (dk-asms))) (prop)))))
  (fact 'class-extensionality x y))

;;; ---------------------------------------------------------------------------
(sp (make-wff '(FORALL sda_ (FORALL sdb_
  (== (SYM-DIFFERENCE sda_ sdb_) (UNION (COMPLEMENT-IN sda_ sdb_) (COMPLEMENT-IN sdb_ sda_)))))))
(dk-peel!)
(mac 'SYM-DIFFERENCE)
(qrfl)
(mbk-qed! 'sym-difference-unfold)

;;; ---------------------------------------------------------------------------
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL nsa_ (FORALL nsb_
  (IMPLIES (IS-NULL-SET omega cA mu nsa_)
    (IMPLIES (SUBSET nsb_ nsa_) (IS-NULL-SET omega cA mu nsb_))))))))))
(dk-peel!)
(let ((nla (dk-skolem! (dk-landed-1 (lambda () (mac-h 'IS-NULL-SET '(IS-NULL-SET omega cA mu nsa_)))) #t)))
  (fact 'subset-trans 'nsb_ 'nsa_ nla)
  (mac 'IS-NULL-SET)
  (ew nla)
  (dk-conj-close! dk-ass!))
(mbk-qed! 'null-set-subset)

;;; ---------------------------------------------------------------------------
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL nsa_
  (IMPLIES (IS-MEASURE omega cA mu)
    (IMPLIES (IS-NULL-SET omega cA mu nsa_) (SUBSET nsa_ omega)))))))))
(dk-peel!)
(let* ((parts (mbk-measure-parts! 'omega 'cA 'mu))
       (sig (car parts)))
  (dk-project! '(SUBSET cA (POWER omega)) 'IS-SIGMA-ALGEBRA sig)
  (let ((nla (dk-skolem! (dk-landed-1 (lambda () (mac-h 'IS-NULL-SET '(IS-NULL-SET omega cA mu nsa_)))) #t)))
    (let ((s1 (caddr (dk-cite! 'subset-def 'nsa_ nla)))
          (s2 (caddr (dk-cite! 'subset-def 'cA '(POWER omega)))))
      (dk-have! s1 (lambda () (mac-h 'subset-def (list 'SUBSET 'nsa_ nla)) (ass)))
      (dk-have! s2 (lambda () (mac-h 'subset-def '(SUBSET cA (POWER omega))) (ass)))
      (inst*! s2 nla)
      (let ((pw (caddr (dk-cite! 'power-set-membership 'omega nla))))
        (dk-have! pw (lambda () (mac-h 'power-set-membership (list 'IN nla '(POWER omega))) (ass)))
        (let ((all (caddr pw)))
          (dk-have! all (lambda () (dk-split! pw) (ass)))
          (mbk-subset-prop!
            (lambda (w)
              (inst*! s1 w)
              (inst*! all w))))))))
(mbk-qed! 'null-set-in-omega)

;;; ---------------------------------------------------------------------------
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu
  (IMPLIES (IS-MEASURE omega cA mu)
    (IFF (IS-COMPLETE-MEASURE omega cA mu)
         (FORALL a_ (FORALL b_
           (IMPLIES (SUBSET a_ omega)
             (IMPLIES (SUBSET b_ omega)
               (IMPLIES (IS-NULL-SET omega cA mu (SYM-DIFFERENCE a_ b_))
                 (IMPLIES (IN a_ cA) (IN b_ cA))))))))))))))
(dk-peel!)
(mbk-measure-parts! 'omega 'cA 'mu)
(dk-iff! (lambda (g) (or (dk-head-is? g 'FORALL)
                         (and (dk-head-is? g 'IMPLIES) (dk-head-is? (cadr g) 'IS-COMPLETE-MEASURE))))
  ;; necessity
  (lambda ()
    (dk-peel!)
    (let* ((nh (dk-pick (lambda (f) (and (dk-head-is? f 'IS-NULL-SET) (dk-contains? f 'SYM-DIFFERENCE)))
                        "the null hypothesis"))
           (a (cadr (list-ref nh 4))) (b (caddr (list-ref nh 4)))
           (ba (list 'COMPLEMENT-IN b a)) (ab (list 'COMPLEMENT-IN a b))
           (un (list 'UNION ab ba))
           (a2 (list 'COMPLEMENT-IN a ab))
           (u2 (list 'UNION a2 ba))
           (comp '(FORALL nls_ (IMPLIES (IS-NULL-SET omega cA mu nls_) (IN nls_ cA)))))
      (dk-have! comp
        (lambda () (mac-h 'IS-COMPLETE-MEASURE '(IS-COMPLETE-MEASURE omega cA mu)) (dk-split-all!) (ass)))
      (fact 'sym-difference-unfold a b)
      (dk-rewrite-h! (list 'IS-NULL-SET 'omega 'cA 'mu (list 'SYM-DIFFERENCE a b))
                     (list 'SYM-DIFFERENCE a b) un)
      (for-each
        (lambda (piece)
          (dk-have! (list 'SUBSET piece un)
            (lambda ()
              (mbk-subset-prop!
                (lambda (w)
                  (dk-cite! 'union-membership ab ba w)
                  (dk-cite! 'complement-in-membership a b w)
                  (dk-cite! 'complement-in-membership b a w)))))
          (dk-cite! 'null-set-subset 'omega 'cA 'mu un piece)
          (inst*! comp piece))
        (list ba ab))
      (fact 'sigma-algebra-difference-closed 'omega 'cA a ab)
      (fact 'sigma-algebra-union-closed-2 'omega 'cA a2 ba)
      (mbk-ext! b u2
        (lambda (w)
          (dk-cite! 'union-membership a2 ba w)
          (dk-cite! 'complement-in-membership a ab w)
          (dk-cite! 'complement-in-membership a b w)
          (dk-cite! 'complement-in-membership b a w)))
      (subst (list '= b u2))
      (ass)))
  ;; sufficiency
  (lambda ()
    (dk-peel!)
    (let ((crit (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'SYM-DIFFERENCE)))
                         "the criterion")))
      (mac 'IS-COMPLETE-MEASURE)
      (dk-conj-close!
        (lambda ()
          (if (dk-asm? (dk-goal))
              (ass)
              (let* ((nv (list-ref (car (dk-peel!)) 4))
                     (sd (list 'SYM-DIFFERENCE 'EMPTY-SET nv))
                     (un (list 'UNION (list 'COMPLEMENT-IN 'EMPTY-SET nv) (list 'COMPLEMENT-IN nv 'EMPTY-SET))))
                (fact 'sigma-algebra-empty-in 'omega 'cA)
                (fact 'empty-subset-any 'omega)
                (dk-cite! 'null-set-in-omega 'omega 'cA 'mu nv)
                (fact 'sym-difference-unfold 'EMPTY-SET nv)
                (dk-have! (list 'SUBSET un nv)
                  (lambda ()
                    (mbk-subset-prop!
                      (lambda (w)
                        (dk-cite! 'union-membership (list 'COMPLEMENT-IN 'EMPTY-SET nv)
                                  (list 'COMPLEMENT-IN nv 'EMPTY-SET) w)
                        (dk-cite! 'complement-in-membership 'EMPTY-SET nv w)
                        (dk-cite! 'complement-in-membership nv 'EMPTY-SET w)
                        (dk-cite! 'empty-set-has-no-members w)))))
                (dk-cite! 'null-set-subset 'omega 'cA 'mu nv un)
                (dk-have! (list 'IS-NULL-SET 'omega 'cA 'mu sd)
                  (lambda () (subst (list '= sd un)) (ass)))
                (let ((inst (inst*! crit 'EMPTY-SET nv)))
                  (if (dk-only! inst '(SUBSET EMPTY-SET omega) (list 'SUBSET nv 'omega)
                                (list 'IS-NULL-SET 'omega 'cA 'mu sd) '(IN EMPTY-SET cA))
                      (prop))))))))))
(mbk-qed! 'complete-iff-symdiff)
