;;; rake-compact-fip.scm -- Prop 3.12 (1) <=> (2), the finite-intersection
;;; characterisation of compactness, PROVEN (2026-09-20, batch 11-E; helper
;;; prefix `rcf-').
;;;
;;;   compact-implies-fip   compact  =>  every closed family with the FIP has a
;;;                         common point
;;;   fip-implies-compact   the converse
;;;   compact-iff-fip       the equivalence, copied LITERALLY from its assertion
;;;                         site, structure-library/compactness.scm:103
;;;
;;; THE ARGUMENT is complementation in PTS(s), in both directions, and the only
;;; thing that makes it long is bookkeeping: the family of complements is an
;;; IMAGE, so every passage between a family and its complements is an
;;; image-membership plus one beta.
;;;
;;; (=>)  Let C have the FIP and suppose the intersection of C is EMPTY.  The
;;;   complements K = { PTS(s) \ A : A in C } are open (that IS the third
;;;   conjunct of IS-CLOSED) and they COVER: a point x of PTS(s) is not in the
;;;   intersection, and C is inhabited, so some A in C misses x and x lies in
;;;   PTS(s) \ A.  Compactness gives a finite subcover F'.  Its complements
;;;   again, TOGETHER WITH the member A0 that HAS-FIP guarantees, form a finite
;;;   INHABITED subfamily of C -- a member of F' is PTS(s) \ A for A in C, and
;;;   PTS(s) \ (PTS(s) \ A) = A because A, being closed, lies in PTS(s)
;;;   (`complement-in-double').  The FIP hands over a common point p of that
;;;   subfamily; p lies in A0, hence in PTS(s), hence in some member v of the
;;;   cover F'; but PTS(s) \ v is in the subfamily too, so p is outside v.
;;;
;;;   WHY A0 IS ADJOINED rather than a case split on "F' is inhabited": for the
;;;   EMPTY space the empty family IS a finite subcover, and HAS-FIP's
;;;   subfamily clause is guarded on the subfamily being inhabited (the guard
;;;   INTERSECTION-OF forced, see structure-library/compactness.scm:59).
;;;   Adjoining A0 makes the subfamily inhabited unconditionally and costs one
;;;   `card-union-nn' instead of a second branch of the whole argument.
;;;
;;; (<=)  Let cov be an open cover.  If cov has NO member it is itself the
;;;   finite subcover (it equals EMPTY-SET, whose CARD is 0).  Otherwise put
;;;   D = { PTS(s) \ U : U in cov }.  Suppose cov had no finite subcover; then
;;;   D has the FIP: its members are closed (`complement-in-double' again turns
;;;   PTS(s) \ (PTS(s) \ U) back into the open U), and a finite inhabited
;;;   subfamily G of D with EMPTY intersection would make the complements of G
;;;   -- which are members of cov -- a finite subcover, because a point outside
;;;   the intersection of G is outside some member PTS(s) \ U of G, i.e. inside
;;;   U.  The hypothesis then gives a common point p of D, which lies in
;;;   PTS(s) and outside every member of cov: the cover does not cover.
;;;
;;; THE STATEMENT WAS CHECKED BEFORE IT WAS PROVEN, for the species CLAUDE.md
;;; lists.  It survives all of them:
;;;   * THE EMPTY SPACE.  PTS(s) = {} is compact (the empty family is an open
;;;     cover of it and is its own finite subcover) and satisfies the right
;;;     side VACUOUSLY: a family with the FIP is inhabited, its member A0 is
;;;     closed hence a subset of {} hence {} itself, and {A0} is a finite
;;;     inhabited subfamily whose intersection is empty -- so no family has the
;;;     FIP.  Both sides TRUE, no case is lost.
;;;   * A FAMILY THAT IS NOT A SET.  Neither HAS-FIP nor IS-OPEN-COVER says
;;;     `(IN C SET)', and neither has to: every member is a subset of PTS(s),
;;;     so the family is a subclass of POWER(PTS s) and therefore a set
;;;     (`family-of-subsets-is-set', theorem-library/rake-complement-laws).
;;;     That is what licenses `image-set' and `card-image-finite' below.
;;;   * IS-CLOSED.  `IS-CLOSED(s,A)' is "A subset PTS(s) and PTS(s) \ A open",
;;;     so the complement family is open by DEFINITION in one direction, and
;;;     the other direction needs the double complement, which is why
;;;     rake-complement-laws exists.
;;;   * The two inhabitedness guards on HAS-FIP are USED, not routed around:
;;;     the family's guard supplies A0 above, the subfamily's is discharged by
;;;     adjoining it.
;;;
;;; CITATIONS (load.scm order at the time of writing):
;;;   primitive / definitional (library.scm, injection.scm, number-systems.scm):
;;;     class-extensionality, complement-in-membership, union-membership,
;;;     pairing, pairing-membership, membership-implies-sethood,
;;;     empty-set-has-no-members, image-membership-iff, image-set,
;;;     nn-zero-in, nn-succ-closed; the is-compact / is-open-cover / has-fip /
;;;     is-closed / is-open definitional unfolds.
;;;   proven: subset-mem-fwd, subclass-of-set-is-set (subset-lemmas);
;;;     complement-in-subset (card-inequalities); card-empty (card-finite);
;;;     card-singleton (card-singleton-proof); card-union-nn
;;;     (card-inequalities); card-image-finite (card-image-finite);
;;;     intersection-of-membership (intersection-of-laws);
;;;     complement-in-double, family-of-subsets-is-set (rake-complement-laws).
;;;   Tactics: dk-peel!, dk-skolem!, dk-apply!, dk-have!, dk-each-leaf!,
;;;     dk-conj-close!, dk-lam-b!/-h!, use-em, push-not-h, prop.  No oracle.
;;;
;;; LOAD WINDOW.  lo = theorem-library/intersection-of-laws and
;;; theorem-library/rake-complement-laws (this batch), whichever is later; the
;;; compactness vocabulary (structure-library/compactness) is far above.
;;; hi = end: nothing cites these names.  window.py's reading is in the report.
;;;
;;; BINDERS.  `rcv_' is the complement lambda's variable -- distinctive, so
;;; that `subst-free' cannot rename it out from under a rebuilt term
;;; (CLAUDE.md, "Writing proof drivers"); `rcu_' the family binder of the
;;; members-are-subsets lane.  Neither is a registered constant or a class name.

;;; =====================================================================
;;; Helpers, file-local (prefix `rcf-').
;;; =====================================================================

;;; The complement map on the family DOM, as a genuine function term, and the
;;; family of complements as its IMAGE.  Built here and nowhere else, so the
;;; driver's terms and the ones it matches against can only come from one
;;; place.
(define (rcf-lam pts dom) (list 'VNB-LAMBDA 'rcv_ dom (list 'COMPLEMENT-IN pts 'rcv_)))
(define (rcf-img pts dom) (list 'IMAGE (rcf-lam pts dom) dom))

;;; Head test tolerating an atom.
(define (rcf-head? e h) (and (pair? e) (eq? (car e) h)))

;;; (IN W (IMAGE lam DOM)) is in context: land the source point U with
;;; (IN U DOM) and the BETA-REDUCED equation (= (PTS \ U) W); return U.
(define (rcf-img-mem! pts dom w)
  (let* ((ex  (dk-landed-1 (lambda () (mac-h 'image-membership-iff
                                             (list 'IN w (rcf-img pts dom))))))
         (uv  (dk-skolem! ex))
         (eqn (dk-pick (lambda (f) (and (rcf-head? f '=) (pair? (cadr f))
                                        (equal? (car (cadr f)) (rcf-lam pts dom))))
                       "the applied-complement-lambda equation")))
    (dk-lam-b-h! eqn)
    uv))

;;; Goal (IN (PTS \ U) (IMAGE lam DOM)) with (IN U DOM) in context.
(define (rcf-img-mi! pts dom u)
  (dk-image-goal!)
  (witness! u
    (lambda ()
      (dk-conj-close!
       (lambda ()
         (if (rcf-head? (dk-goal) 'IN) (ass) (begin (dk-lam-b!) (rfl))))))))

;;; Goal (IN X (UNION A B)) with (IN X A) -- or (IN X B) -- in context.
(define (rcf-in-union! x a b)
  (let ((iff (dk-fact! 'union-membership a b x)))
    (dk-only! iff (list 'IN x a) (list 'IN x b))
    (prop)))

;;; Goal (IN A (PAIR A A)), for a SET A.
(define (rcf-in-pair-self! a)
  (dk-have! (list 'AND (list 'IN a 'SET) (list 'IN a 'SET)))
  (let* ((law (dk-fact! 'pairing-membership a a))
         (iff (dk-apply! law a)))
    (dk-have! (list '= a a) (lambda () (rfl)))
    (dk-only! iff (list '= a a))
    (prop)))

;;; FAM's intersection is EMPTY (NEG is the context's negated existential) and
;;; FAM is inhabited by WIT: land a member of FAM that misses XV, and return it.
;;; The inhabitedness is re-established in the SHAPE intersection-of-membership
;;; states it, because `prop' is not alpha-aware.
(define (rcf-missing-member! fam xv neg wit)
  (let* ((iff  (dk-fact! 'intersection-of-membership fam xv))
         (mem  (cadr iff))                       ; (IN xv (INTERSECTION-OF fam))
         (conj (caddr iff))
         (inh  (cadr conj))
         (alls (caddr conj)))
    (dk-have! (list 'NOT mem)
      (lambda ()
        (di)                                     ; assume the membership
        (dk-have! (cadr neg) (lambda () (witness! xv (lambda () (ass)))))
        (ai neg)))
    (dk-have! inh (lambda () (witness! wit (lambda () (ass)))))
    (dk-have! (list 'NOT alls)
      (lambda () (dk-only! iff (list 'NOT mem) inh) (prop)))
    (dk-skolem! (push-not-h (list 'NOT alls)))))

;;; (IN (PTS s) SET) out of IS-METRIC-SPACE(s), in a LANE (`mac-h' REPLACES the
;;; predicate and every later citation wants it).
(define (rcf-pts-in-set! sv)
  (dk-have! (list 'IN (list 'PTS sv) 'SET)
    (lambda ()
      (dk-split-all!
       (dk-landed (lambda () (mac-h 'is-metric-space (list 'IS-METRIC-SPACE sv)))))
      (ass))))

;;; The members-are-subsets law of a family of CLOSED sets, as a lane.
(define (rcf-closed-subsets! sv cv closed)
  (let ((pts (list 'PTS sv)))
    (have-f! (list 'FORALL 'rcu_
                   (list 'IMPLIES (list 'IN 'rcu_ cv) (list 'SUBSET 'rcu_ pts)))
      (lambda ()
        (let ((u (dk-di-var!)))
          (dk-apply! closed u)
          (dk-split-all!
           (dk-landed (lambda () (mac-h 'is-closed (list 'IS-CLOSED sv u)))))
          (dk-split-all!)
          (ass))))))

;;; The members-are-subsets law of a family of OPEN sets, as a lane.
(define (rcf-open-subsets! sv cv opens)
  (let ((pts (list 'PTS sv)))
    (have-f! (list 'FORALL 'rcu_
                   (list 'IMPLIES (list 'IN 'rcu_ cv) (list 'SUBSET 'rcu_ pts)))
      (lambda ()
        (let ((u (dk-di-var!)))
          (dk-apply! opens u)
          (dk-split-all!
           (dk-landed (lambda () (mac-h 'is-open (list 'IS-OPEN sv u)))))
          (dk-split-all!)
          (ass))))))

;;; Instantiate the subfamily law of HAS-FIP (or any curried universal) at
;;; TERM, proving with PROVE! each antecedent the context does not already
;;; hold; return what finally landed.
(define (rcf-apply-with! law term prove!)
  (let loop ((f (dk-deepest (lambda () (inst+ law term)))))
    (if (rcf-head? f 'IMPLIES)
        (begin
          (dk-have! (cadr f) (lambda () (prove! (cadr f))))
          (loop (dk-landed-1 (lambda () (detach! f)))))
        f)))

;;; =====================================================================
;;; 1.  compact-implies-fip
;;; =====================================================================

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IMPLIES (IS-COMPACT s)
       (FORALL C (IMPLIES (HAS-FIP s C)
         (FORSOME p (IN p (INTERSECTION-OF C))))))))))
(dk-peel!)

(define rcf1-sv  (cadr  (dk-pick (dk-head? 'IS-METRIC-SPACE) "the metric-space hypothesis")))
(define rcf1-cv  (caddr (dk-pick (dk-head? 'HAS-FIP) "the FIP hypothesis")))
(define rcf1-pts (list 'PTS rcf1-sv))
(define rcf1-goal (dk-goal))
(define rcf1-neg  (list 'NOT rcf1-goal))
(define rcf1-K   (rcf-img rcf1-pts rcf1-cv))

(rcf-pts-in-set! rcf1-sv)

;; HAS-FIP, opened: the family is inhabited, its members are closed, and every
;; finite inhabited subfamily meets.
(dk-split-all!
 (dk-landed (lambda () (mac-h 'has-fip (list 'HAS-FIP rcf1-sv rcf1-cv)))))
(dk-split-all!)

(define rcf1-a0
  (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the family-is-inhabited conjunct")))
(define rcf1-closed
  (dk-pick (lambda (f) (and (rcf-head? f 'FORALL) (dk-contains? f 'IS-CLOSED)))
           "the members-are-closed law"))
(define rcf1-fip
  (dk-pick (lambda (f) (and (rcf-head? f 'FORALL) (dk-contains? f 'INTERSECTION-OF)))
           "the finite-subfamily law"))
(define rcf1-subs (rcf-closed-subsets! rcf1-sv rcf1-cv rcf1-closed))

;; The family is a SET: its members are subsets of PTS(s).
(dk-fact! 'family-of-subsets-is-set rcf1-pts rcf1-cv)

;;; ---- the complement family covers -----------------------------------

;; (IN x BU) => (IN x (PTS s)): the member is a complement in PTS(s).
(define (rcf1-bu-to-pts! xv bu)
  (let* ((landed (dk-landed (lambda () (bu-me (list 'IN xv bu)))))
         (memK   (any-pred (lambda (f) (and (rcf-head? f 'IN) (equal? (caddr f) rcf1-K)))
                           landed))
         (wv     (cadr memK))
         (av     (rcf-img-mem! rcf1-pts rcf1-cv wv))
         (comp   (list 'COMPLEMENT-IN rcf1-pts av)))
    (dk-have! (list 'IN xv comp) (lambda () (subst (list '= comp wv)) (ass)))
    (fact 'complement-in-subset av rcf1-pts)
    (fact 'subset-mem-fwd comp rcf1-pts xv)
    (ass)))

;; (IN x (PTS s)) => (IN x BU): the intersection is empty, so some member of C
;; misses x and x lies in that member's complement.
(define (rcf1-pts-to-bu! xv bu)
  (let* ((av   (rcf-missing-member! rcf1-cv xv rcf1-neg rcf1-a0))
         (comp (list 'COMPLEMENT-IN rcf1-pts av)))
    (dk-have! (list 'IN xv comp)
      (lambda () (mac 'complement-in-membership) (dk-conj-close! (lambda () (ass)))))
    (dk-have! (list 'IN comp rcf1-K)
      (lambda () (rcf-img-mi! rcf1-pts rcf1-cv av)))
    (dk-each-leaf! (lambda () (bu-mi comp)) (lambda () (ass)))))

(define (rcf1-cover!)
  (mac 'is-open-cover)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (cond
         ((rcf-head? g 'IS-METRIC-SPACE) (ass))
         ((rcf-head? g 'FORALL)                       ; every member of K is open
          (let* ((uv (dk-di-var!))
                 (av (rcf-img-mem! rcf1-pts rcf1-cv uv)))
            (dk-apply! rcf1-closed av)
            (dk-split-all!
             (dk-landed (lambda () (mac-h 'is-closed (list 'IS-CLOSED rcf1-sv av)))))
            (dk-split-all!)
            (subst (list '= uv (list 'COMPLEMENT-IN rcf1-pts av)))
            (ass)))
         (#t                                          ; the union is PTS(s)
          (let ((bu (cadr g)))
            (dk-have! (list '= bu rcf1-pts)
              (lambda ()
                (bc* 'class-extensionality)
                (di)
                (let ((xv (cadr (cadr (dk-goal)))))
                  (dk-each-leaf!
                   (lambda () (di))
                   (lambda ()
                     (if (rcf-head? (caddr (dk-goal)) 'PTS)
                         (rcf1-bu-to-pts! xv bu)
                         (rcf1-pts-to-bu! xv bu)))))))
            (subst (list '= bu rcf1-pts))
            (qrfl))))))))

;;; ---- the finite subfamily, and the contradiction --------------------

(define (rcf1-main!)
  (dk-have! (list 'IS-OPEN-COVER rcf1-sv rcf1-K) rcf1-cover!)
  ;; compactness at K
  (dk-split-all!
   (dk-landed (lambda () (mac-h 'is-compact (list 'IS-COMPACT rcf1-sv)))))
  (dk-split-all!)
  (let* ((law (dk-pick (lambda (f) (and (rcf-head? f 'FORALL) (dk-contains? f 'IS-OPEN-COVER)))
                       "the finite-subcover law"))
         (fv  (dk-skolem! (dk-apply! law rcf1-K)))
         (pr  (list 'PAIR rcf1-a0 rcf1-a0))
         (fim (rcf-img rcf1-pts fv))
         (fam (list 'UNION fim pr)))
    ;; sethood and finiteness of the subfamily
    (dk-fact! 'image-set (rcf-lam rcf1-pts rcf1-cv) rcf1-cv)     ; K is a set
    (dk-fact! 'subclass-of-set-is-set fv rcf1-K)                 ; F' is a set
    (dk-fact! 'card-image-finite (rcf-lam rcf1-pts fv) fv)       ; CARD(Fim) in NN
    (dk-fact! 'image-set (rcf-lam rcf1-pts fv) fv)               ; Fim is a set
    (dk-fact! 'membership-implies-sethood rcf1-a0 rcf1-cv)       ; A0 is a set
    (dk-have! (list 'AND (list 'IN rcf1-a0 'SET) (list 'IN rcf1-a0 'SET)))
    (dk-fact! 'pairing rcf1-a0 rcf1-a0)                          ; {A0} is a set
    (dk-fact! 'card-singleton rcf1-a0)                           ; CARD{A0} = succ 0
    (fact 'nn-zero-in)
    (fact 'nn-succ-closed 0)
    (dk-have! (list 'IN (list 'CARD pr) 'NN)
      (lambda () (subst (list '= (list 'CARD pr) '(succ 0))) (ass)))
    (dk-fact! 'card-union-nn fim pr)                             ; CARD(fam) in NN
    ;; the subfamily is included in C -- this is the double complement
    (dk-have! (list 'SUBSET fam rcf1-cv)
      (lambda ()
        (let* ((wv  (subset-by-element!))
               (iff (dk-fact! 'union-membership fim pr wv)))
          (dk-have! (list 'OR (list 'IN wv fim) (list 'IN wv pr))
            (lambda () (dk-only! iff (list 'IN wv fam)) (prop)))
          (use-em (list 'IN wv fim)
            ;; w is the complement of a member of the cover, i.e. a member of C
            (lambda ()
              (let* ((vv  (rcf-img-mem! rcf1-pts fv wv))
                     (ign (fact 'subset-mem-fwd fv rcf1-K vv))
                     (av  (rcf-img-mem! rcf1-pts rcf1-cv vv)))
                (dk-apply! rcf1-subs av)
                (let ((dbl (dk-fact! 'complement-in-double rcf1-pts av)))
                  (subst (list '= wv (list 'COMPLEMENT-IN rcf1-pts vv)))
                  (subst (list '= vv (list 'COMPLEMENT-IN rcf1-pts av)))
                  (subst dbl)
                  (ass))))
            ;; w is A0
            (lambda ()
              (dk-have! (list 'IN wv pr)
                (lambda () (dk-only! (list 'OR (list 'IN wv fim) (list 'IN wv pr))
                                     (list 'NOT (list 'IN wv fim)))
                           (prop)))
              (let* ((law2 (dk-fact! 'pairing-membership rcf1-a0 rcf1-a0))
                     (iff2 (dk-apply! law2 wv)))
                (dk-have! (list '= wv rcf1-a0)
                  (lambda () (dk-only! iff2 (list 'IN wv pr)) (prop)))
                (subst (list '= wv rcf1-a0))
                (ass)))))))
    ;; A0 is a member of the subfamily -- which is what makes the subfamily
    ;; INHABITED, the guard HAS-FIP carries since 2026-09-20.
    (dk-have! (list 'IN rcf1-a0 pr) (lambda () (rcf-in-pair-self! rcf1-a0)))
    (dk-have! (list 'IN rcf1-a0 fam) (lambda () (rcf-in-union! rcf1-a0 fim pr)))
    ;; the FIP at the subfamily
    (let* ((got (rcf-apply-with! rcf1-fip fam
                  (lambda (ante)
                    (witness! rcf1-a0 (lambda () (ass))))))
           (pv  (dk-skolem! got))
           (iff (dk-fact! 'intersection-of-membership fam pv))
           (alls (caddr (caddr iff))))
      (dk-have! alls
        (lambda () (dk-only! iff (list 'IN pv (list 'INTERSECTION-OF fam))) (prop)))
      ;; p lies in A0, hence in PTS(s)
      (dk-apply! alls rcf1-a0)
      (dk-apply! rcf1-subs rcf1-a0)
      (fact 'subset-mem-fwd rcf1-a0 rcf1-pts pv)
      ;; ... hence in a member v of the finite subcover, whose complement is in
      ;; the subfamily: p is both in and out of v.
      (dk-split-all!
       (dk-landed (lambda () (mac-h 'is-open-cover (list 'IS-OPEN-COVER rcf1-sv fv)))))
      (dk-split-all!)
      (let* ((ueq (dk-pick (lambda (f) (and (pair? f) (memq (car f) '(== =))
                                            (dk-contains? f 'BIG-UNION)))
                           "the subcover's union equation"))
             (bu  (cadr ueq)))
        (dk-have! (list 'IN pv bu)
          (lambda () (subst (list '= bu rcf1-pts)) (ass)))
        (let* ((landed (dk-landed (lambda () (bu-me (list 'IN pv bu)))))
               (memF   (any-pred (lambda (f) (and (rcf-head? f 'IN) (equal? (caddr f) fv)))
                                 landed))
               (vv     (cadr memF))
               (comp   (list 'COMPLEMENT-IN rcf1-pts vv)))
          (dk-have! (list 'IN comp fim) (lambda () (rcf-img-mi! rcf1-pts fv vv)))
          (dk-have! (list 'IN comp fam) (lambda () (rcf-in-union! comp fim pr)))
          (dk-apply! alls comp)
          (dk-split-all!
           (dk-landed (lambda () (mac-h 'complement-in-membership (list 'IN pv comp)))))
          (dk-split-all!)
          (dk-only! (list 'NOT (list 'IN pv vv)) (list 'IN pv vv))
          (prop))))))

(use-em rcf1-goal (lambda () (ass)) rcf1-main!)

(qed 'compact-implies-fip)
(gloss! 'compact-implies-fip
  "In a compact metric space every family of closed sets with the finite
   intersection property has a common point.  Dually: if the family had empty
   intersection its complements would cover, a finite subcover would give a
   finite subfamily with empty intersection, and that is what the finite
   intersection property forbids.")
(topic! 'compact-implies-fip 'topology)

;;; =====================================================================
;;; 2.  fip-implies-compact
;;; =====================================================================

;;; A point of the union of a family of COMPLEMENTS in PTS(s) is a point of
;;; PTS(s): each member is a complement, and a complement is a subset.
(define (rcf-bu-to-pts! pts dom xv bu)
  (let* ((fam    (rcf-img pts dom))
         (landed (dk-landed (lambda () (bu-me (list 'IN xv bu)))))
         (memF   (any-pred (lambda (f) (and (rcf-head? f 'IN) (equal? (caddr f) fam)))
                           landed))
         (wv     (cadr memF))
         (vv     (rcf-img-mem! pts dom wv))
         (comp   (list 'COMPLEMENT-IN pts vv)))
    (dk-have! (list 'IN xv comp) (lambda () (subst (list '= comp wv)) (ass)))
    (fact 'complement-in-subset vv pts)
    (fact 'subset-mem-fwd comp pts xv)
    (ass)))

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IMPLIES (FORALL C (IMPLIES (HAS-FIP s C)
                 (FORSOME p (IN p (INTERSECTION-OF C)))))
              (IS-COMPACT s))))))
(dk-peel!)

(define rcf2-sv  (cadr (dk-pick (dk-head? 'IS-METRIC-SPACE) "the metric-space hypothesis")))
(define rcf2-pts (list 'PTS rcf2-sv))
(define rcf2-h   (dk-pick (lambda (f) (and (rcf-head? f 'FORALL) (dk-contains? f 'HAS-FIP)))
                          "the finite-intersection hypothesis"))
(rcf-pts-in-set! rcf2-sv)

;;; ---- the cover with no member is its own finite subcover -------------

(define (rcf2-empty-cover! cov neg)
  (dk-have! (list '= cov 'EMPTY-SET)
    (lambda ()
      (bc* 'class-extensionality)
      (di)
      (let ((xv (cadr (cadr (dk-goal)))))
        (dk-each-leaf!
         (lambda () (di))
         (lambda ()
           (if (equal? (caddr (dk-goal)) 'EMPTY-SET)   ; EMPTY-SET is an ATOM
               (begin
                 (dk-have! (cadr neg) (lambda () (witness! xv (lambda () (ass)))))
                 (dk-only! neg (cadr neg))
                 (prop))
               (begin
                 (fact 'empty-set-has-no-members xv)
                 (dk-only! (list 'NOT (list 'IN xv 'EMPTY-SET)) (list 'IN xv 'EMPTY-SET))
                 (prop))))))))
  (witness! cov
    (lambda ()
      (dk-conj-close!
       (lambda ()
         (let ((g (dk-goal)))
           (cond ((rcf-head? g 'SUBSET) (mac 'subset-def) (di) (ass))
                 ((rcf-head? g 'IS-OPEN-COVER) (ass))
                 (#t                                    ; (IN (CARD cov) NN)
                  (fact 'card-empty)
                  (fact 'nn-zero-in)
                  (subst (list '= cov 'EMPTY-SET))
                  (subst '(= (CARD EMPTY-SET) 0))
                  (ass)))))))))

;;; ---- the main case ---------------------------------------------------

;;; The subfamily clause of HAS-FIP for the family D of complements: a finite
;;; inhabited subfamily G of D with EMPTY intersection would make the
;;; complements of G a finite subcover, which NEG2 forbids.
(define (rcf2-subfamily! cov opens subs dd goal-ex neg2)
  (let* ((landed (dk-peel!))
         (gsub   (any-pred (lambda (f) (and (rcf-head? f 'SUBSET) (equal? (caddr f) dd)))
                           landed))
         (gv     (cadr gsub))
         (w0     (dk-skolem! (any-pred (dk-head? 'FORSOME) landed)))
         (goal2  (dk-goal))
         (neg3   (list 'NOT goal2))
         (subf   (rcf-img rcf2-pts gv)))
    (use-em goal2
      (lambda () (ass))
      (lambda ()
        (dk-fact! 'subclass-of-set-is-set gv dd)                     ; G is a set
        (dk-fact! 'card-image-finite (rcf-lam rcf2-pts gv) gv)       ; the subcover is finite
        ;; the complements of G: a finite subcover of cov
        (dk-have! goal-ex
          (lambda ()
            (witness! subf
              (lambda ()
                (dk-conj-close!
                 (lambda ()
                   (let ((g (dk-goal)))
                     (cond
                       ((rcf-head? g 'SUBSET)
                        (let ((wv (subset-by-element!)))
                          (rcf2-back-to-cov! cov subs gv dd wv)))
                       ((rcf-head? g 'IN) (ass))
                       (#t (rcf2-subcover-is-cover! cov opens subs gv dd neg3 w0))))))))))
        (dk-only! goal-ex neg2)
        (prop)))))

;;; With (IN WV (IMAGE lam G)) in context and G a subfamily of D, the goal
;;; (IN WV cov) -- or (IS-OPEN s WV) after one more citation: WV is the
;;; complement of the complement of a member of cov.  Returns that member.
(define (rcf2-source! cov subs gv dd wv)
  (let* ((vv  (rcf-img-mem! rcf2-pts gv wv))
         (ign (fact 'subset-mem-fwd gv dd vv))
         (av  (rcf-img-mem! rcf2-pts cov vv))
         (ig2 (dk-apply! subs av))
         (dbl (dk-fact! 'complement-in-double rcf2-pts av)))
    (subst (list '= wv (list 'COMPLEMENT-IN rcf2-pts vv)))
    (subst (list '= vv (list 'COMPLEMENT-IN rcf2-pts av)))
    (subst dbl)
    av))

(define (rcf2-back-to-cov! cov subs gv dd wv)
  (rcf2-source! cov subs gv dd wv)
  (ass))

(define (rcf2-subcover-is-cover! cov opens subs gv dd neg3 w0)
  (mac 'is-open-cover)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (cond
         ((rcf-head? g 'IS-METRIC-SPACE) (ass))
         ((rcf-head? g 'FORALL)                         ; the members are open
          (let* ((uv (dk-di-var!))
                 (av (rcf2-source! cov subs gv dd uv)))
            (dk-apply! opens av)
            (ass)))
         (#t                                            ; ... and they cover
          (let ((bu (cadr g)))
            (dk-have! (list '= bu rcf2-pts)
              (lambda ()
                (bc* 'class-extensionality)
                (di)
                (let ((xv (cadr (cadr (dk-goal)))))
                  (dk-each-leaf!
                   (lambda () (di))
                   (lambda ()
                     (if (rcf-head? (caddr (dk-goal)) 'PTS)
                         (rcf-bu-to-pts! rcf2-pts gv xv bu)
                         (rcf2-pts-to-bu! cov subs gv dd neg3 w0 xv bu)))))))
            (subst (list '= bu rcf2-pts))
            (qrfl))))))))

;; x in PTS(s) lies in the complement of a member of G that misses it -- and
;; that complement is a member of cov, hence of the subcover.
(define (rcf2-pts-to-bu! cov subs gv dd neg3 w0 xv bu)
  (let* ((vv   (rcf-missing-member! gv xv neg3 w0))
         (ign  (fact 'subset-mem-fwd gv dd vv))
         (av   (rcf-img-mem! rcf2-pts cov vv))
         (ig2  (dk-apply! subs av))
         (dbl  (dk-fact! 'complement-in-double rcf2-pts av))
         (comp (list 'COMPLEMENT-IN rcf2-pts vv)))
    (dk-have! (list 'NOT (list 'IN xv (list 'COMPLEMENT-IN rcf2-pts av)))
      (lambda () (subst (list '= (list 'COMPLEMENT-IN rcf2-pts av) vv)) (ass)))
    (let ((iff (dk-fact! 'complement-in-membership rcf2-pts av xv)))
      (dk-have! (list 'IN xv av)
        (lambda ()
          (dk-only! iff (list 'NOT (list 'IN xv (list 'COMPLEMENT-IN rcf2-pts av)))
                    (list 'IN xv rcf2-pts))
          (prop))))
    (dk-have! (list 'IN xv comp)
      (lambda ()
        (subst (list '= vv (list 'COMPLEMENT-IN rcf2-pts av)))
        (subst dbl)
        (ass)))
    (dk-have! (list 'IN comp (rcf-img rcf2-pts gv))
      (lambda () (rcf-img-mi! rcf2-pts gv vv)))
    (dk-each-leaf! (lambda () (bu-mi comp)) (lambda () (ass)))))

;;; The whole of the inhabited case.
(define (rcf2-main! cov u0 goal-ex)
  (dk-split-all!
   (dk-landed (lambda () (mac-h 'is-open-cover (list 'IS-OPEN-COVER rcf2-sv cov)))))
  (dk-split-all!)
  (let* ((opens (dk-pick (lambda (f) (and (rcf-head? f 'FORALL) (dk-contains? f 'IS-OPEN)))
                         "the members-are-open law"))
         (ueq   (dk-pick (lambda (f) (and (pair? f) (memq (car f) '(== =))
                                          (dk-contains? f 'BIG-UNION)))
                         "the cover's union equation"))
         (bu    (cadr ueq))
         (subs  (rcf-open-subsets! rcf2-sv cov opens))
         (dd    (rcf-img rcf2-pts cov))
         (neg2  (list 'NOT goal-ex)))
    (dk-fact! 'family-of-subsets-is-set rcf2-pts cov)     ; cov is a set
    (dk-fact! 'image-set (rcf-lam rcf2-pts cov) cov)      ; so is D
    (use-em goal-ex
      (lambda () (ass))
      (lambda ()
        ;; D has the finite-intersection property
        (dk-have! (list 'HAS-FIP rcf2-sv dd)
          (lambda ()
            (mac 'has-fip)
            (dk-conj-close!
             (lambda ()
               (let ((g (dk-goal)))
                 (cond
                   ((rcf-head? g 'IS-METRIC-SPACE) (ass))
                   ((rcf-head? g 'FORSOME)                     ; D is inhabited
                    (witness! (list 'COMPLEMENT-IN rcf2-pts u0)
                      (lambda () (rcf-img-mi! rcf2-pts cov u0))))
                   ((dk-contains? g 'IS-CLOSED)                ; its members are closed
                    (let* ((uv (dk-di-var!))
                           (av (rcf-img-mem! rcf2-pts cov uv)))
                      (subst (list '= uv (list 'COMPLEMENT-IN rcf2-pts av)))
                      (mac 'is-closed)
                      (dk-conj-close!
                       (lambda ()
                         (let ((g2 (dk-goal)))
                           (cond
                             ((rcf-head? g2 'IS-METRIC-SPACE) (ass))
                             ((rcf-head? g2 'SUBSET)
                              (fact 'complement-in-subset av rcf2-pts) (ass))
                             (#t
                              (dk-apply! subs av)
                              (subst (dk-fact! 'complement-in-double rcf2-pts av))
                              (dk-apply! opens av)
                              (ass))))))))
                   (#t (rcf2-subfamily! cov opens subs dd goal-ex neg2))))))))
        ;; ... so it has a common point, which no member of the cover contains
        (let* ((pv   (dk-skolem! (dk-apply! rcf2-h dd)))
               (iff  (dk-fact! 'intersection-of-membership dd pv))
               (alls (caddr (caddr iff))))
          (dk-have! alls
            (lambda () (dk-only! iff (list 'IN pv (list 'INTERSECTION-OF dd))) (prop)))
          (let ((comp0 (list 'COMPLEMENT-IN rcf2-pts u0)))
            (dk-have! (list 'IN comp0 dd) (lambda () (rcf-img-mi! rcf2-pts cov u0)))
            (dk-apply! alls comp0)
            (dk-split-all!
             (dk-landed (lambda () (mac-h 'complement-in-membership (list 'IN pv comp0)))))
            (dk-split-all!))
          (dk-have! (list 'IN pv bu) (lambda () (subst (list '= bu rcf2-pts)) (ass)))
          (let* ((landed (dk-landed (lambda () (bu-me (list 'IN pv bu)))))
                 (memc   (any-pred (lambda (f) (and (rcf-head? f 'IN) (equal? (caddr f) cov)))
                                   landed))
                 (vv     (cadr memc))
                 (comp   (list 'COMPLEMENT-IN rcf2-pts vv)))
            (dk-have! (list 'IN comp dd) (lambda () (rcf-img-mi! rcf2-pts cov vv)))
            (dk-apply! alls comp)
            (dk-split-all!
             (dk-landed (lambda () (mac-h 'complement-in-membership (list 'IN pv comp)))))
            (dk-split-all!)
            (dk-only! (list 'NOT (list 'IN pv vv)) (list 'IN pv vv))
            (prop)))))))

(mac 'IS-COMPACT)
(dk-conj-close!
 (lambda ()
   (if (rcf-head? (dk-goal) 'IS-METRIC-SPACE)
       (ass)
       (let* ((cov   (caddr (car (dk-peel!))))
              (inh   (list 'FORSOME 'rcu_ (list 'IN 'rcu_ cov)))
              (goal  (dk-goal)))
         (use-em inh
           (lambda () (rcf2-main! cov (dk-skolem! inh) goal))
           (lambda () (rcf2-empty-cover! cov (list 'NOT inh))))))))

(qed 'fip-implies-compact)
(gloss! 'fip-implies-compact
  "If every family of closed sets with the finite intersection property has a
   common point, the metric space is compact.  Given an open cover with no
   finite subcover, the complements of its members form a closed family with
   the finite intersection property -- a finite subfamily with empty
   intersection IS a finite subcover -- so they have a common point, which is
   a point of the space in no member of the cover.")
(topic! 'fip-implies-compact 'topology)

;;; =====================================================================
;;; 3.  compact-iff-fip -- the support's statement, LITERAL
;;;     (structure-library/compactness.scm:103-107).
;;; =====================================================================

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IFF (IS-COMPACT s)
          (FORALL C (IMPLIES (HAS-FIP s C)
            (FORSOME p (IN p (INTERSECTION-OF C))))))))))
(dk-peel!)
(define rcf3-sv (cadr (dk-pick (dk-head? 'IS-METRIC-SPACE) "the metric-space hypothesis")))
(define rcf3-fwd (dk-fact! 'compact-implies-fip rcf3-sv))
(define rcf3-bwd (dk-fact! 'fip-implies-compact rcf3-sv))
(dk-only! rcf3-fwd rcf3-bwd)
(prop)

(qed 'compact-iff-fip)
(topic! 'compact-iff-fip 'topology)

;;; =====================================================================
;;; FOR THE INTEGRATOR.
;;;
;;; * RETIRE the support `compact-iff-fip', structure-library/compactness.scm
;;;   lines 102-134: the `add-axiom!' form and the `warrant!' that
;;;   follows it (the warrant's body is the list of the four missing bricks,
;;;   three of which this batch supplied and one -- BIG-UNION over an IMAGE --
;;;   turned out not to be needed: every passage through the union is done at
;;;   the ELEMENT level, by `bu-me' / `bu-mi', which costs less than the set
;;;   equation would have).  The `qed' here prints "re-installing the same
;;;   statement", so the statement is literally the support's.
;;;   With it, all four equivalences of Prop 3.12 are theorems.
;;; * Nothing else in the tree cites `compact-iff-fip' (checked 2026-09-20:
;;;   only comments name it), so the retirement is a deletion, not a rename.
;;; * theorem-library/rake-complement-laws.scm must load BEFORE this file, and
;;;   theorem-library/intersection-of-laws.scm already does.
;;; =====================================================================
