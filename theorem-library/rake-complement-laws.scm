;;; rake-complement-laws.scm -- two set-theoretic bricks the compactness
;;; duality needs, PROVEN (2026-09-20, batch 11-E; helper prefix `rcl-').
;;;
;;;   complement-in-double      A subset Y  =>  Y \ (Y \ A) = A
;;;   family-of-subsets-is-set  Y a set, every member of c a subset of Y
;;;                               =>  c is a SET
;;;
;;; WHY THEY EXIST.  `compact-iff-fip' (structure-library/compactness.scm:103)
;;; is the duality "an open cover with no finite subcover is a closed family
;;; with the finite-intersection property and empty intersection".  Passing
;;; between the two sides is complementation in PTS(s), and the two facts that
;;; make it work were both missing from the tree (checked 2026-09-20, rake
;;; batch 9-A):
;;;
;;;   * the complement map is an INVOLUTION on subsets of Y, which is what says
;;;     the complements of the complements of a subfamily are the subfamily
;;;     again.  theorem-library/rake-open-sets.scm:521 needed exactly this in
;;;     2026-09-17 and carried a private copy, `rko-dbl-comp!', with the
;;;     comment "The tree has no double-complement lemma"; the argument here is
;;;     that driver's, lifted to a THEOREM so that nobody writes it a third
;;;     time.  (rko-dbl-comp! itself is left where it is: retiring it is an
;;;     edit to a file this batch does not own.  See the footer.)
;;;
;;;   * the SETHOOD of a family of subsets.  A family of closed sets, or of
;;;     open sets, is a family of subsets of PTS(s) and therefore a subclass of
;;;     POWER(PTS s), hence a set -- which is what licenses `image-set' on it
;;;     and, through `card-image-finite', the transport of finiteness between a
;;;     family and its family of complements.  Neither HAS-FIP nor
;;;     IS-OPEN-COVER says `(IN C SET)', and neither has to: the sethood is a
;;;     consequence, and this is the lemma that draws it.
;;;
;;; NEITHER IS GUARD-FREE, and the guards are not decoration.  Without
;;; `SUBSET A Y' the double complement is false (Y \ (Y \ A) = A n Y, which is
;;; A only for A below Y).  Without "every member is a subset of Y" the family
;;; lemma is false for the obvious reason: the class of all sets is not a set.
;;;
;;; CITATIONS, all primitive or proven long before this file:
;;;   class-extensionality, complement-in-membership, power-set,
;;;   power-set-membership, membership-implies-sethood, subset-def
;;;     -- theory.scm (primitive base);
;;;   subset-mem-fwd, subclass-of-set-is-set -- theorem-library/subset-lemmas.
;;; Tactics: dk-peel!, dk-each-leaf!, dk-only!, dk-pick, dk-apply!, `prop'.
;;;
;;; LOAD WINDOW.  lo = theorem-library/subset-lemmas (the latest citation) and
;;; `prop' (a tactic file far above it).  hi = the first file citing either
;;; name, which today is theorem-library/rake-compact-fip, at the bottom.  The
;;; slot right after subset-lemmas satisfies both; window.py's reading is in
;;; the report.
;;;
;;; BINDERS.  `rcy_' (the ambient set), `rca_' (the subset), `rcc_' (the
;;; family), `rcu_' (a member of the family).  The one `x' is the binder of the
;;; have!'d extensionality claim, spelled as `class-extensionality' spells it so
;;; that `fact' detaches against it (theorem-library/intersection-of-laws.scm
;;; does the same and its header says why).

;;; -----------------------------------------------------------------------
;;; Local helpers (prefix `rcl-'; every one local to this file).

;;; Does F contain a membership in a relative complement?  (The driver unfolds
;;; complement memberships to a fixpoint, and a fixed count of `mac' calls
;;; would leave inert steps.)
(define (rcl-comp-mem? f)
  (cond ((not (pair? f)) #f)
        ((and (eq? (car f) 'IN) (pair? (caddr f))
              (eq? (car (caddr f)) 'COMPLEMENT-IN)) #t)
        (#t (and (any-pred rcl-comp-mem? (cdr f)) #t))))

;;; Unfold every complement membership inside the HYPOTHESIS `form', returning
;;; the hypothesis as the context finally holds it.
(define (rcl-unfold-comp-h! form)
  (let loop ((f form))
    (if (rcl-comp-mem? f)
        (loop (dk-landed-1 (lambda () (mac-h 'complement-in-membership f))))
        f)))

;;; The same for the GOAL.
(define (rcl-unfold-comp-goal!)
  (let loop ()
    (if (rcl-comp-mem? (dk-goal))
        (let ((g (dk-goal)))
          (mac 'complement-in-membership)
          (if (equal? (dk-goal) g)
              (error "rcl-unfold-comp-goal!: mac made no progress"
                     (expression->string g)))
          (loop)))))

;;; =====================================================================
;;; (1) the double complement
;;; =====================================================================
;;; With both memberships unfolded the identity is PROPOSITIONAL in the two
;;; atoms `x in Y' and `x in A', so `prop' closes each direction once
;;; `dk-only!' has trimmed the context under prop's atom cap.  The <= direction
;;; additionally needs `x in Y', which is the guard, through subset-mem-fwd.

(sp (make-wff '(FORALL rcy_ (FORALL rca_
   (IMPLIES (SUBSET rca_ rcy_)
     (= (COMPLEMENT-IN rcy_ (COMPLEMENT-IN rcy_ rca_)) rca_))))))
(dk-peel!)

(define rcl-big '(COMPLEMENT-IN rcy_ (COMPLEMENT-IN rcy_ rca_)))

(have! (list 'FORALL 'x (list 'IFF (list 'IN 'x rcl-big) '(IN x rca_)))
  (lambda ()
    (di)
    (dk-each-leaf!
     (lambda () (di))
     (lambda ()
       (let* ((g (dk-goal)) (xv (cadr g)))
         (if (equal? (caddr g) 'rca_)
             ;; => : x is outside Y \ A and inside Y, so it is inside A
             (begin (dk-only! (rcl-unfold-comp-h! (list 'IN xv rcl-big))) (prop))
             ;; <= : x is in A, hence in Y, hence outside Y \ A
             (begin (fact 'subset-mem-fwd 'rca_ 'rcy_ xv)
                    (dk-only! (list 'IN xv 'rca_) (list 'IN xv 'rcy_))
                    (rcl-unfold-comp-goal!)
                    (prop))))))))
(dk-fact! 'class-extensionality rcl-big 'rca_)
(ass)
(qed 'complement-in-double)
(gloss! 'complement-in-double
  "Taking the complement in Y twice returns a subset of Y unchanged:
   Y \\ (Y \\ A) = A whenever A is contained in Y.  The guard is necessary --
   without it the left-hand side is the part of A that lies in Y.")
(topic! 'complement-in-double 'plumbing)

;;; =====================================================================
;;; (2) a family of subsets of a set is a set
;;; =====================================================================
;;; c is a subclass of POWER(Y): each member is a SET (it is a member of
;;; something) and is contained in Y (the hypothesis), which is exactly what
;;; power-set-membership asks.  POWER(Y) is a set, so subclass-of-set-is-set
;;; closes.

(sp (make-wff '(FORALL rcy_ (FORALL rcc_
   (IMPLIES (IN rcy_ SET)
     (IMPLIES (FORALL rcu_ (IMPLIES (IN rcu_ rcc_) (SUBSET rcu_ rcy_)))
              (IN rcc_ SET)))))))
(dk-peel!)

(define rcl-subs
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f 'SUBSET)))
           "the members-are-subsets hypothesis"))

(have! '(SUBSET rcc_ (POWER rcy_))
  (lambda ()
    (let ((v (subset-by-element!)))
      (fact 'membership-implies-sethood v 'rcc_)
      (dk-apply! rcl-subs v)
      (mac 'power-set-membership)
      (dk-conj-close!
       (lambda ()
         (if (eq? (car (dk-goal)) 'FORALL)
             (let ((z (dk-di-var!)))
               (fact 'subset-mem-fwd v 'rcy_ z)
               (ass))
             (ass)))))))
(fact 'power-set 'rcy_)
(fact 'subclass-of-set-is-set 'rcc_ '(POWER rcy_))
(ass)
(qed 'family-of-subsets-is-set)
(gloss! 'family-of-subsets-is-set
  "A family whose members are all subsets of one set Y is itself a set: it is
   a subclass of POWER(Y).  This is what makes a family of closed sets, or of
   open sets, in a metric space a SET -- neither HAS-FIP nor IS-OPEN-COVER
   states it, and neither has to.")
(topic! 'family-of-subsets-is-set 'plumbing)

;;; =====================================================================
;;; FOR THE INTEGRATOR.
;;;
;;; * theorem-library/rake-open-sets.scm:521-540 carries `rko-dbl-comp!', a
;;;   file-local copy of the double-complement argument, introduced when the
;;;   tree had no theorem for it.  It is now `complement-in-double'.  Replacing
;;;   the helper's body by `(dk-fact! 'complement-in-double base sub)' would
;;;   cut about twenty lines from that file, but it is an edit to a file batch
;;;   11-E does not own, and rake-open-sets loads BEFORE this file today, so
;;;   the change costs a load-order move as well.  Reported, not done.
;;; * Nothing is retired by this file: both names are new.
;;; =====================================================================
