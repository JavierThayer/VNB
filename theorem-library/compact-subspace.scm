;;; compact-subspace.scm -- a CLOSED SUBSET of a COMPACT space is COMPACT as a
;;; subspace (structure-library/metric-subspace.scm,
;;; theorem-library/metric-subspace-laws.scm).
;;;
;;;     forall s.  IS-COMPACT(s)  =>  forall A.  IS-CLOSED(s, A)
;;;                =>  IS-COMPACT( SUBSPACE-MS(s, A) )
;;;
;;; THE WITNESS FAMILIES ARE BUILT, NOT CHOSEN.  Given a cover C of the
;;; subspace, the classical argument picks, for each W in C, an open U of s with
;;; W = U ^ A -- a choice function over C.  It is avoided the same way
;;; `subspace-open-is-trace' avoids it: quantify the witness INSIDE a separation.
;;;
;;;     D = { U in POWER(PTS s) : IS-OPEN(s,U) and
;;;                               (U ^ A in C  or  U = PTS(s) \ A) }
;;;
;;; D is an open cover of s -- a point of A lies in some W of C, which is a TRACE
;;; (subspace-open-is-trace), and a point outside A lies in the complement, which
;;; is OPEN because A is closed.  Compactness of s gives a finite F subset D, and
;;; the subcover of the subspace is
;;;
;;;     G = { W in IMAGE(U |-> U ^ A, F) : W in C }.
;;;
;;; G is finite because it is a subclass of the image of a finite set
;;; (`card-image-finite' then `card-subset-nn'), it is a subfamily of C by
;;; construction, and it covers A: a point of A is in some U0 of F, U0 is in D,
;;; and the complement disjunct is impossible for a point of A, so U0 ^ A is in C
;;; -- and it is the image of U0.  POWER(PTS s) is what makes D a SET, which is
;;; what the two CARD bricks need; nothing here assumes C is a set.
;;;
;;; THE EMPTY CASES COME OUT RIGHT AND ARE NOT SPECIAL-CASED.  A = EMPTY-SET is
;;; closed (its complement is PTS(s), open), and the argument then produces
;;; G = EMPTY-SET, whose CARD is 0 in NN and whose BIG-UNION is EMPTY-SET = A.
;;; The same run covers PTS(s) = EMPTY-SET.  No inhabitedness guard anywhere.
;;;
;;; WINDOW (scratchpad/window.py).  lo = 1195 on the file's own citations
;;; (card-image-finite 1195, card-subset-nn 1194, power-mem-intro / power-mem-in
;;; 938, subset-mem-fwd / subclass-of-set-is-set 852), but it must ALSO load after
;;; theorem-library/metric-subspace-laws (subspace-is-metric-space, subspace-pts,
;;; subspace-open-is-trace), which window.py cannot see while those theorems are
;;; not in the band: the slot is immediately after metric-subspace-laws, i.e.
;;; after "theorem-library/rake-balls" (1348).  hi = none: nothing cites it yet.
;;;
;;; Helper prefix: csub-.

;;; ---- file-local driver helpers --------------------------------------

(define (csub-head g) (and (pair? g) (car g)))
(define (csub-concl g) (if (eq? (csub-head g) 'IMPLIES) (caddr g) g))

;;; Split an AND goal to its atoms and run CLOSER on each.
(define (csub-and! closer)
  (if (eq? (csub-head (dk-goal)) 'AND)
      (for-each (lambda (k) (dk-focus! k) (csub-and! closer))
                (dk-opened (lambda () (di))))
      (closer)))

;;; `bu-me' the membership MEM and return the index eigenvariable, taken from
;;; the landing that is a membership in FAM -- never by shape.
(define (csub-bu-skolem! mem fam)
  (let* ((new (dk-landed (lambda () (bu-me mem))))
         (f   (or (find-first (lambda (h) (and (pair? h) (eq? (car h) 'IN)
                                               (equal? (caddr h) fam)))
                              new)
                  (error "csub-bu-skolem!: no landed membership in" fam))))
    (cadr f)))

;;; The pointwise membership rule for a subclass of a SEP: from (IN e SEP) take
;;; the condition apart and close the goal from the context.
(define (csub-sep-close! e sp)
  (sep-me (list 'IN e sp))
  (dk-split-all!)
  (ass))

;;; =====================================================================
;;; (1) AN OPEN SET IS A MEMBER OF THE POWER SET OF THE POINTS.
;;;
;;; The one packaging this file needs twice, and the only place `power-mem-intro'
;;; appears: its antecedent is the POINTWISE form of SUBSET, spelled with the
;;; binder `z_' the theorem itself uses, so it is cut in that spelling and proved
;;; by one `subset-mem-fwd' rather than by rewriting SUBSET in a hypothesis.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL ou_ (IMPLIES (IS-OPEN s ou_)
       (IN ou_ (POWER (PTS s)))))))))
(dk-peel!)
(have! '(IN (PTS s) SET)
  (lambda () (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s)) (dk-split-all!) (ass)))
(have! '(SUBSET ou_ (PTS s))
  (lambda () (mac-h 'IS-OPEN '(IS-OPEN s ou_)) (dk-split-all!) (ass)))
(fact 'subclass-of-set-is-set 'ou_ '(PTS s))
(have! '(FORALL z_ (IMPLIES (IN z_ ou_) (IN z_ (PTS s))))
  (lambda ()
    (let ((e (dk-di-var!)))
      (fact 'subset-mem-fwd 'ou_ '(PTS s) e)
      (ass))))
(fact 'power-mem-intro '(PTS s) 'ou_)
(ass)
(qed 'open-in-power)
(topic! 'open-in-power 'topology)
(alias! 'open-in-power "an open set belongs to the power set of the points")

;;; =====================================================================
;;; (2) A CLOSED SUBSET OF A COMPACT SPACE IS COMPACT AS A SUBSPACE.
;;; =====================================================================

(define csub-space '(SUBSPACE-MS s A))
(define csub-comp '(COMPLEMENT-IN (PTS s) A))

;;; The trace family D, as a function of the cover eigenvariable.
(define (csub-dd cv)
  (list 'SEP 'du_ '(POWER (PTS s))
        (list 'AND '(IS-OPEN s du_)
              (list 'OR (list 'IN '(INTERSECTION du_ A) cv)
                        (list '= 'du_ csub-comp)))))

;;; `(== (BIG-UNION b FAM b) RHS)' by class extensionality.  BODY is run on the
;;; peeled point with the two arguments (z, the big union as the GOAL spells it).
(define (csub-extensional! rhs body)
  (let ((bu (cadr (dk-goal))))
    (have! (list 'FORALL 'zz_ (list 'IFF (list 'IN 'zz_ bu) (list 'IN 'zz_ rhs)))
      (lambda ()
        (let ((z (dk-di-var! (lambda (g) (cadr (cadr g))))))
          (body z bu))))
    (fact 'class-extensionality bu rhs)
    (subst (list '= bu rhs))
    (qrfl)))

(sp (make-wff '(FORALL s (IMPLIES (IS-COMPACT s)
     (FORALL A (IMPLIES (IS-CLOSED s A)
       (IS-COMPACT (SUBSPACE-MS s A))))))))
(dk-peel!)
(mac-h 'IS-CLOSED '(IS-CLOSED s A))
(dk-split-all!)                    ; IS-METRIC-SPACE s, SUBSET A (PTS s), the complement open
(mac-h 'IS-COMPACT '(IS-COMPACT s))
(dk-split-all!)                    ; ... and the cover universal of s
(fact 'subspace-is-metric-space 's 'A)
(have! '(IN (PTS s) SET)
  (lambda () (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s)) (dk-split-all!) (ass)))
(fact 'complement-in-set-closure '(PTS s) 'A)
(mac 'IS-COMPACT)
(csub-and!
 (lambda ()
   (if (eq? (csub-head (dk-goal)) 'IS-METRIC-SPACE)
       (ass)
       (begin
         (di)                                          ; peel the cover variable
         (let ((cv (caddr (cadr (dk-goal)))))
           (di)                                        ; land IS-OPEN-COVER(sub, cv)
           (mac-h 'IS-OPEN-COVER (list 'IS-OPEN-COVER csub-space cv))
           (dk-split-all!)
           (let* ((dd    (csub-dd cv))
                  (copen (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                                   (dk-contains? h cv)
                                                   (dk-contains? h 'IS-OPEN)))
                                  "the openness universal of the cover"))
                  (cbu   (cadr (dk-pick (lambda (h) (and (pair? h) (eq? (car h) '==)
                                                         (dk-contains? h cv)))
                                        "the cover's big union"))))
             ;; ---------- D is a set, and an open cover of s ----------
             (have! (list 'IN dd 'SET)
               (lambda () (sep-set) (fact 'power-set '(PTS s)) (ass)))
             (have! (list 'IS-OPEN-COVER 's dd)
               (lambda ()
                 (mac 'IS-OPEN-COVER)
                 (csub-and!
                  (lambda ()
                    (let ((g (dk-goal)))
                      (cond
                        ((eq? (csub-head g) 'IS-METRIC-SPACE) (ass))
                        ((eq? (csub-head g) 'FORALL)
                         (csub-sep-close! (dk-di-var!) dd))
                        (#t
                         (csub-extensional!
                          '(PTS s)
                          (lambda (z bu)
                            (dk-iff!
                             (lambda (g) (dk-contains? (csub-concl g) 'BIG-UNION))
                             ;; z in PTS s  ==>  z in BIG-UNION(D)
                             (lambda ()
                               (dk-peel!)
                               (use-em (list 'IN z 'A)
                                 (lambda ()
                                   (have! (list 'IN z cbu)
                                     (lambda ()
                                       (subst (list '== cbu (list 'PTS csub-space)))
                                       (mac 'subspace-pts)
                                       (ass)))
                                   (let ((w (csub-bu-skolem! (list 'IN z cbu) cv)))
                                     (dk-apply! copen w)
                                     (let* ((ex (dk-fact! 'subspace-open-is-trace 's 'A w))
                                            (u  (dk-skolem! ex)))
                                       (for-each
                                        (lambda (k)
                                          (dk-focus! k)
                                          (let ((g2 (dk-goal)))
                                            (if (equal? (caddr g2) dd)
                                                (in-sep!
                                                 (lambda () (fact 'open-in-power 's u) (ass))
                                                 (lambda ()
                                                   (both! (lambda () (ass))
                                                          (lambda ()
                                                            (oi-l)
                                                            (subst (list '= (list 'INTERSECTION u 'A) w))
                                                            (ass)))))
                                                (begin
                                                  (have! (list 'IN z (list 'INTERSECTION u 'A))
                                                    (lambda ()
                                                      (subst (list '= (list 'INTERSECTION u 'A) w))
                                                      (ass)))
                                                  (mac-h 'intersection-membership
                                                         (list 'IN z (list 'INTERSECTION u 'A)))
                                                  (dk-split-all!)
                                                  (ass)))))
                                        (dk-opened (lambda () (bu-mi u)))))))
                                 (lambda ()
                                   (for-each
                                    (lambda (k)
                                      (dk-focus! k)
                                      (let ((g2 (dk-goal)))
                                        (if (equal? (caddr g2) dd)
                                            (in-sep!
                                             (lambda () (fact 'open-in-power 's csub-comp) (ass))
                                             (lambda ()
                                               (both! (lambda () (ass))
                                                      (lambda () (oi-r) (rfl)))))
                                            (begin
                                              (mac 'complement-in-membership)
                                              (dk-conj-close! (lambda () (ass)))))))
                                    (dk-opened (lambda () (bu-mi csub-comp)))))))
                             ;; z in BIG-UNION(D)  ==>  z in PTS s
                             (lambda ()
                               (dk-peel!)
                               (let ((e (csub-bu-skolem! (list 'IN z bu) dd)))
                                 (sep-me (list 'IN e dd))
                                 (dk-split-all!)
                                 (fact 'power-mem-in '(PTS s) e z)
                                 (ass)))))))))))))
             ;; ---------- the finite subcover of s, and the family G ----------
             (dk-apply! (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                                  (dk-contains? h 'IS-OPEN-COVER)
                                                  (dk-contains? h 'FORSOME)))
                                 "the compactness universal of s")
                        dd)
             (let* ((fv  (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the finite subcover")))
                    (lam (list 'VNB-LAMBDA 'dw_ fv (list 'INTERSECTION 'dw_ 'A)))
                    (img (list 'IMAGE lam fv))
                    (gg  (list 'SEP 'gw_ img (list 'IN 'gw_ cv))))
               (fact 'subclass-of-set-is-set fv dd)
               (mac-h 'IS-OPEN-COVER (list 'IS-OPEN-COVER 's fv))
               (dk-split-all!)
               (let ((fbu (cadr (dk-pick (lambda (h) (and (pair? h) (eq? (car h) '==)
                                                          (dk-contains? h fv)))
                                         "the subcover's big union"))))
                 (fact 'image-set lam fv)
                 (fact 'card-image-finite lam fv)
                 (have! (list 'IN gg 'SET) (lambda () (sep-set) (ass)))
                 ;; CARD(G) in NN: a subclass of the image of a finite set
                 (have! (list 'AND (list 'IN img 'SET) (list 'IN (list 'CARD img) 'NN)))
                 (let* ((uni  (dk-fact! 'card-subset-nn img))
                        (inst (inst*! uni gg)))
                   (have! (cadr inst)
                     (lambda ()
                       (both! (lambda () (ass))
                              (lambda () (csub-sep-close! (dk-di-var!) gg)))))
                   (detach! inst))
                 (ew gg)
                 (csub-and!
                  (lambda ()
                    (let ((g (dk-goal)))
                      (cond
                        ;; G subset C
                        ((eq? (csub-head g) 'SUBSET)
                         (mac 'subset-def)
                         (csub-sep-close! (dk-di-var!) gg))
                        ;; CARD(G) in NN
                        ((eq? (csub-head g) 'IN) (ass))
                        ;; G is an open cover of the subspace
                        (#t
                         (mac 'IS-OPEN-COVER)
                         (mac 'subspace-pts)
                         (csub-and!
                          (lambda ()
                            (let ((g2 (dk-goal)))
                              (cond
                                ((eq? (csub-head g2) 'IS-METRIC-SPACE) (ass))
                                ((eq? (csub-head g2) 'FORALL)
                                 (let ((w (dk-di-var!)))
                                   (sep-me (list 'IN w gg))
                                   (dk-split-all!)
                                   (dk-apply! copen w)
                                   (ass)))
                                (#t
                                 (csub-extensional!
                                  'A
                                  (lambda (z bu)
                                    (dk-iff!
                                     (lambda (g3) (dk-contains? (csub-concl g3) 'BIG-UNION))
                                     ;; z in A  ==>  z in BIG-UNION(G)
                                     (lambda ()
                                       (dk-peel!)
                                       (fact 'subset-mem-fwd 'A '(PTS s) z)
                                       (have! (list 'IN z fbu)
                                         (lambda () (subst (list '== fbu '(PTS s))) (ass)))
                                       (let ((u0 (csub-bu-skolem! (list 'IN z fbu) fv)))
                                         (fact 'subset-mem-fwd fv dd u0)
                                         (sep-me (list 'IN u0 dd))
                                         (dk-split-all!)
                                         (use-cases
                                          (list (list 'IN (list 'INTERSECTION u0 'A) cv)
                                                (list '= u0 csub-comp))
                                          (lambda ()
                                            (for-each
                                             (lambda (k)
                                               (dk-focus! k)
                                               (let ((g4 (dk-goal)))
                                                 (if (equal? (caddr g4) gg)
                                                     (in-sep!
                                                      (lambda ()
                                                        (dk-image-goal!)
                                                        (ew u0)
                                                        (both! (lambda () (ass))
                                                               (lambda () (lam-b) (rfl))))
                                                      (lambda () (ass)))
                                                     (begin
                                                       (mac 'intersection-membership)
                                                       (dk-conj-close! (lambda () (ass)))))))
                                             (dk-opened
                                              (lambda ()
                                                (bu-mi (list 'INTERSECTION u0 'A))))))
                                          (lambda ()
                                            (have! (list 'IN z csub-comp)
                                              (lambda ()
                                                (subst (list '= csub-comp u0))
                                                (ass)))
                                            (mac-h 'complement-in-membership
                                                   (list 'IN z csub-comp))
                                            (dk-split-all!)
                                            (ai (list 'NOT (list 'IN z 'A)))))))
                                     ;; z in BIG-UNION(G)  ==>  z in A
                                     (lambda ()
                                       (dk-peel!)
                                       (let ((e (csub-bu-skolem! (list 'IN z bu) gg)))
                                         (sep-me (list 'IN e gg))
                                         (dk-split-all!)
                                         (dk-apply! copen e)
                                         (have! (list 'SUBSET e 'A)
                                           (lambda ()
                                             (mac-h 'IS-OPEN (list 'IS-OPEN csub-space e))
                                             (dk-split-all!)
                                             (mac-h 'subspace-pts
                                                    (list 'SUBSET e (list 'PTS csub-space)))
                                             (ass)))
                                         (fact 'subset-mem-fwd e 'A z)
                                         (ass))))))))))))))))))))))))
(qed 'closed-subset-of-compact-is-compact)
(topic! 'closed-subset-of-compact-is-compact 'topology)
(alias! 'closed-subset-of-compact-is-compact
        "a closed subset of a compact space is compact as a subspace")
