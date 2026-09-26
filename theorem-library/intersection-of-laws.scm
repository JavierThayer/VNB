;;; intersection-of-laws.scm -- the laws of INTERSECTION-OF, PROVEN.
;;;
;;;   intersection-of-unfold          the functoid's unfold equation, as a THEOREM
;;;   intersection-of-membership      x in INTERSECTION-OF(c) iff c is inhabited
;;;                                   and x lies in every member of c
;;;   intersection-of-subset-member   u in c  =>  INTERSECTION-OF(c) subset u
;;;   intersection-of-empty-family    c has no member  =>  INTERSECTION-OF(c) = EMPTY-SET
;;;   intersection-of-is-set          INTERSECTION-OF(c) is ALWAYS a set
;;;   intersection-of-antitone        c subset d, c inhabited
;;;                                     =>  INTERSECTION-OF(d) subset INTERSECTION-OF(c)
;;;   complement-in-big-union         De Morgan: x in Y \ UNION(c) iff x in Y and
;;;                                   x is in no member of c
;;;   complement-in-intersection-of   De Morgan: for c inhabited,
;;;                                     Y \ INTERSECTION-OF(c) = UNION_{u in c} (Y \ u)
;;;
;;; The constructor is defined in structure-library/intersection-of.scm; read
;;; its header for why it exists and for the empty-family convention.  Nothing
;;; here is asserted: every statement is `proven modulo 0'.
;;;
;;; WHY `intersection-of-unfold' IS A THEOREM AND NOT JUST THE MACETE.
;;; `def-functoid' installs a rewrite macete only, so `mac' unfolds
;;; INTERSECTION-OF in a GOAL but `mac-h' cannot unfold it in an ASSUMPTION by
;;; the functoid's own name.  The unfold equation is provable in one line --
;;; the macete applies to a goal that IS the equation -- and the resulting
;;; THEOREM is what `mac-h' can name.  theorem-library/poly-membership.scm is
;;; the worked model (seven instances) and its header has the full account.
;;;
;;; THE INHABITEDNESS CLAUSE IS NOT DECORATION.  The intersection is a SEP over
;;; the UNION of the family, so a point of INTERSECTION-OF(c) is in particular a
;;; point of some member: "c is inhabited" is part of the membership law, not a
;;; guard bolted on to it.  Every statement below that could be false for the
;;; empty family carries it.  This is what forced the two inhabitedness guards
;;; on HAS-FIP (structure-library/compactness.scm): with INTERSECTION-OF total
;;; and INTERSECTION-OF(EMPTY-SET) = EMPTY-SET, a finite-intersection property
;;; that ranges over the EMPTY subfamily is unsatisfiable.
;;;
;;; SETHOOD IS UNCONDITIONAL, and that is worth the case split it costs: if c
;;; has a member u then INTERSECTION-OF(c) is included in u, and u is a set
;;; because every member of a class is (membership-implies-sethood); if c has no
;;; member the intersection is EMPTY-SET.  So even the intersection of a proper
;;; CLASS of sets is a set, and no caller ever owes a sethood hypothesis.
;;;
;;; BINDERS.  `iov_ iow_ iou_' are the functoid's own (see its header);
;;; `iox_ ioa_ iod_ ioy_' are this file's statement binders.  None is a
;;; registered constant or a class name, and none is spelled like another up to
;;; case.  The one exception is the `x' of the two `have!'d extensionality
;;; claims, which must be spelled as `class-extensionality' spells it so that
;;; `fact' detaches against it; theorem-library/subset-lemmas.scm does the same.
;;;
;;; LOAD WINDOW.  lo = 193: `subclass-of-set-is-set' and `subset-mem-fwd'
;;; (theorem-library/subset-lemmas, 192) are cited.  `push-not' (143) and
;;; `prop' (141) are the latest tactics used.  hi = end: nothing cites these
;;; laws yet.  structure-library/intersection-of (the definition) must of
;;; course be above, and it is -- it sits in the structure-library block.

;;; -----------------------------------------------------------------------
;;; Local helpers (prefix `iof-'; every one of them is local to this file --
;;; CLAUDE.md, "Where a driver helper lives").

;;; Split an IFF goal and drive each direction, discriminated on the GOAL and
;;; never on the order `dk-opened' happens to return.  `which?' says which
;;; branch a leaf is.
(define (iof-iff! which? fwd bwd)
  (let ((ls (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (which? (dk-goal-of n))) ls)) (fwd)
    (dk-focus! (any-pred (lambda (n) (not (which? (dk-goal-of n)))) ls)) (bwd)))

;;; The SEP that INTERSECTION-OF(cc) unfolds to -- built, never retyped, so the
;;; binder names can only come from one place.
(define (iof-sep-of cc)
  (list 'SEP 'iov_ (list 'BIG-UNION 'iow_ cc 'iow_)
        (list 'FORALL 'iou_ (list 'IMPLIES (list 'IN 'iou_ cc)
                                  (list 'IN 'iov_ 'iou_)))))

;;; The two halves of the membership law at (t, cc), as formulas.
(define (iof-inhabited cc) (list 'FORSOME 'iou_ (list 'IN 'iou_ cc)))
(define (iof-all-of t cc)
  (list 'FORALL 'iou_ (list 'IMPLIES (list 'IN 'iou_ cc) (list 'IN t 'iou_))))

;;; With (IN t (INTERSECTION-OF cc)) in context, land BOTH halves of the
;;; membership law and return them as (inhabited universal).
(define (iof-read! t cc)
  (let* ((ex   (iof-inhabited cc))
         (all  (iof-all-of t cc))
         (conj (list 'AND ex all)))
    (have! conj (lambda ()
                  (dk-fact! 'intersection-of-membership cc t)
                  (prop)))
    (dk-split! conj)
    (list ex all)))

;;; The eigenvariable a `bu-me' minted, read off the landed (IN e cc) -- never
;;; guessed from the binder name.
(define (iof-bu-witness! mem cc)
  (let* ((landed (dk-landed (lambda () (bu-me mem))))
         (memc   (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                            (equal? (caddr f) cc)))
                           landed)))
    (if (not memc)
        (error "iof-bu-witness!: bu-me landed no membership in" cc))
    (cadr memc)))

;;; Run a branching tactic and close every leaf it opened with `ass'.
(define (iof-close-all! thunk)
  (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened thunk)))

;;; Head test that tolerates an ATOM.  A leaf discriminator that writes
;;; (car (caddr goal)) dies on a goal whose class is a bare variable -- `bu-mi'
;;; opens exactly such a leaf, (IN v c_), beside the one being discriminated.
(define (iof-head? e h) (and (pair? e) (eq? (car e) h)))

;;; =====================================================================
;;; (1) the unfold equation
;;; =====================================================================

(sp (make-wff '(FORALL c_
   (== (INTERSECTION-OF c_)
       (SEP iov_ (BIG-UNION iow_ c_ iow_)
            (FORALL iou_ (IMPLIES (IN iou_ c_) (IN iov_ iou_))))))))
(di) (mac 'INTERSECTION-OF) (qrfl)
(qed 'intersection-of-unfold)
(gloss! 'intersection-of-unfold
  "INTERSECTION-OF(c) is the separation { x in UNION(c) : x belongs to every
   member of c }, as a citable equation.  Cite it with mac-h to open an
   intersection membership that sits in a hypothesis.")
(topic! 'intersection-of-unfold 'plumbing)

;;; =====================================================================
;;; (2) the membership law
;;; =====================================================================

(sp (make-wff '(FORALL c_ (FORALL iox_
   (IFF (IN iox_ (INTERSECTION-OF c_))
        (AND (FORSOME iou_ (IN iou_ c_))
             (FORALL iou_ (IMPLIES (IN iou_ c_) (IN iox_ iou_)))))))))
(di)
(iof-iff!
  (lambda (g) (eq? (car g) 'AND))
  ;; => : rewrite the hypothesis into the SEP, read both halves off it; the
  ;; inhabitedness comes from the SEP's DOMAIN, which is the union of c_.
  (lambda ()
    (mac-h 'intersection-of-unfold '(IN iox_ (INTERSECTION-OF c_)))
    (sep-me (list 'IN 'iox_ (iof-sep-of 'c_)))
    (let ((e (iof-bu-witness! '(IN iox_ (BIG-UNION iow_ c_ iow_)) 'c_)))
      (for-each (lambda (n)
                  (dk-focus! n)
                  (if (eq? (car (dk-goal)) 'FORSOME) (ew e))
                  (ass))
                (dk-opened (lambda () (di))))))
  ;; <= : unfold the GOAL; sep-mi's domain obligation is the union membership,
  ;; witnessed by any member of c_ the inhabitedness hands over.
  (lambda ()
    (dk-split! '(AND (FORSOME iou_ (IN iou_ c_))
                     (FORALL iou_ (IMPLIES (IN iou_ c_) (IN iox_ iou_)))))
    (let ((u (dk-skolem! '(FORSOME iou_ (IN iou_ c_)))))
      (dk-apply! '(FORALL iou_ (IMPLIES (IN iou_ c_) (IN iox_ iou_))) u)
      (mac 'INTERSECTION-OF)
      (for-each
        (lambda (n)
          (dk-focus! n)
          (if (eq? (car (dk-goal)) 'FORALL)
              (ass)
              (iof-close-all! (lambda () (bu-mi u)))))
        (dk-opened (lambda () (sep-mi)))))))
(qed 'intersection-of-membership)
(gloss! 'intersection-of-membership
  "A point lies in the intersection of the family c exactly when c has at least
   one member and the point lies in every member of c.  The inhabitedness half
   is not a convention: the intersection is built as a subset of the UNION of
   the family, so a point of it is a point of some member.")
(topic! 'intersection-of-membership 'plumbing)

;;; =====================================================================
;;; (3) the intersection is below every member
;;; =====================================================================

(sp (make-wff '(FORALL c_ (FORALL ioa_
   (IMPLIES (IN ioa_ c_) (SUBSET (INTERSECTION-OF c_) ioa_))))))
(di)
(mac 'subset-def)
(let* ((mem (dk-landed-1 (lambda () (di))))
       (z   (cadr mem)))
  (dk-apply! (cadr (iof-read! z 'c_)) 'ioa_)
  (ass))
(qed 'intersection-of-subset-member)
(gloss! 'intersection-of-subset-member
  "The intersection of a family is contained in each of its members.")
(topic! 'intersection-of-subset-member 'plumbing)

;;; =====================================================================
;;; (4) the empty family
;;; =====================================================================
;;; The convention INTERSECTION-OF(EMPTY-SET) = EMPTY-SET, stated for a family
;;; with no member at all (which covers the empty SET and any empty class), and
;;; PROVEN rather than declared in a comment.

(sp (make-wff '(FORALL c_
   (IMPLIES (NOT (FORSOME iou_ (IN iou_ c_)))
            (= (INTERSECTION-OF c_) EMPTY-SET)))))
(di) (di)
(have! '(FORALL x (IFF (IN x (INTERSECTION-OF c_)) (IN x EMPTY-SET)))
  (lambda ()
    (di)
    ;; `di' on the IFF opens both directions with each one's hypothesis in
    ;; context; both leaves are closed by a contradiction, so `prop' finishes
    ;; each once the relevant law is landed.
    (for-each
      (lambda (leaf)
        (dk-focus! leaf)
        (if (eq? (caddr (dk-goal)) 'EMPTY-SET)
            (begin (dk-fact! 'intersection-of-membership 'c_ 'x) (prop))
            (begin (fact 'empty-set-has-no-members 'x) (prop))))
      (dk-opened (lambda () (di))))))
(fact 'class-extensionality '(INTERSECTION-OF c_) 'EMPTY-SET)
(ass)
(qed 'intersection-of-empty-family)
(gloss! 'intersection-of-empty-family
  "The intersection of a family with no members is the empty set.  This is the
   convention that keeps INTERSECTION-OF total and keeps its value a set: 'the
   intersection of no sets' cannot be the universal class without leaving set
   theory.  The price is that a statement about every FINITE subfamily must
   exclude the empty subfamily explicitly.")
(topic! 'intersection-of-empty-family 'plumbing)

;;; =====================================================================
;;; (5) sethood, unconditionally
;;; =====================================================================

(sp (make-wff '(FORALL c_ (IN (INTERSECTION-OF c_) SET))))
(di)
(use-em (iof-inhabited 'c_)
  ;; c_ has a member u: the intersection is below u, and u is a set because
  ;; every member of a class is.
  (lambda ()
    (let ((u (dk-skolem! (iof-inhabited 'c_))))
      (fact 'intersection-of-subset-member 'c_ u)
      (fact 'membership-implies-sethood u 'c_)
      (fact 'subclass-of-set-is-set '(INTERSECTION-OF c_) u)
      (ass)))
  ;; c_ has no member: the intersection IS the empty set.
  (lambda ()
    (fact 'intersection-of-empty-family 'c_)
    (subst '(= (INTERSECTION-OF c_) EMPTY-SET))
    (fact 'empty-set-is-set)
    (ass)))
(qed 'intersection-of-is-set)
(gloss! 'intersection-of-is-set
  "The intersection of a family is always a set -- even the intersection of a
   proper CLASS of sets, and even of the empty family.  No caller owes a
   sethood hypothesis on the family.")
(topic! 'intersection-of-is-set 'plumbing)

;;; =====================================================================
;;; (6) antitonicity
;;; =====================================================================
;;; Enlarging the family shrinks the intersection -- but only among INHABITED
;;; families: INTERSECTION-OF(EMPTY-SET) is EMPTY-SET, not the universal class,
;;; so without the guard the empty family would be a counterexample
;;; (EMPTY-SET subset d, and INTERSECTION-OF(d) is not below EMPTY-SET).

(sp (make-wff '(FORALL c_ (FORALL iod_
   (IMPLIES (SUBSET c_ iod_)
     (IMPLIES (FORSOME iou_ (IN iou_ c_))
       (SUBSET (INTERSECTION-OF iod_) (INTERSECTION-OF c_))))))))
(di) (di) (di)
(mac 'subset-def)
(let* ((mem (dk-landed-1 (lambda () (di))))
       (z   (cadr mem))
       (all (cadr (iof-read! z 'iod_))))
  ;; z lies in every member of iod_, hence in every member of the smaller c_
  (have! (iof-all-of z 'c_)
    (lambda ()
      (let* ((h (dk-landed-1 (lambda () (di))))
             (v (cadr h)))
        (fact 'subset-mem-fwd 'c_ 'iod_ v)
        (dk-apply! all v)
        (ass))))
  ;; ... and c_ is inhabited, so the membership law closes the goal
  (dk-fact! 'intersection-of-membership 'c_ z)
  (prop))
(qed 'intersection-of-antitone)
(gloss! 'intersection-of-antitone
  "A larger family has a smaller intersection, for inhabited families.  The
   inhabitedness guard is necessary: the intersection of the empty family is
   the empty set, not the universal class.")
(topic! 'intersection-of-antitone 'plumbing)

;;; =====================================================================
;;; (7) De Morgan, complement of a union
;;; =====================================================================
;;; Stated as a MEMBERSHIP law rather than a set equation: the dual set is the
;;; intersection of the family of complements, which is INTERSECTION-OF of an
;;; IMAGE and drags in the sethood of the family; the membership form needs
;;; neither and is what a cover argument actually cites.

(sp (make-wff '(FORALL ioy_ (FORALL c_ (FORALL iox_
   (IFF (IN iox_ (COMPLEMENT-IN ioy_ (BIG-UNION iow_ c_ iow_)))
        (AND (IN iox_ ioy_)
             (FORALL iou_ (IMPLIES (IN iou_ c_) (NOT (IN iox_ iou_)))))))))))
(di)
(mac 'complement-in-membership)
(iof-iff!
  ;; both sides are conjunctions; the branches differ in the SECOND conjunct
  (lambda (g) (eq? (car (caddr g)) 'FORALL))
  ;; => : x is in no member, because a member containing it would put it in the union
  (lambda ()
    (dk-split! '(AND (IN iox_ ioy_) (NOT (IN iox_ (BIG-UNION iow_ c_ iow_)))))
    (for-each
      (lambda (n)
        (dk-focus! n)
        (if (eq? (car (dk-goal)) 'FORALL)
            (let* ((h (dk-landed-1 (lambda () (di))))
                   (v (cadr h)))
              (di)                                  ; NOT-intro: assume (IN iox_ v)
              (have! '(IN iox_ (BIG-UNION iow_ c_ iow_))
                (lambda () (iof-close-all! (lambda () (bu-mi v)))))
              (ai '(NOT (IN iox_ (BIG-UNION iow_ c_ iow_)))))
            (ass)))
      (dk-opened (lambda () (di)))))
  ;; <= : a point of the union sits in some member, which the universal forbids
  (lambda ()
    (dk-split! '(AND (IN iox_ ioy_)
                     (FORALL iou_ (IMPLIES (IN iou_ c_) (NOT (IN iox_ iou_))))))
    (for-each
      (lambda (n)
        (dk-focus! n)
        (if (eq? (car (dk-goal)) 'NOT)
            (begin
              (di)                                  ; assume the union membership
              (let ((e (iof-bu-witness! '(IN iox_ (BIG-UNION iow_ c_ iow_)) 'c_)))
                (dk-apply! '(FORALL iou_ (IMPLIES (IN iou_ c_) (NOT (IN iox_ iou_)))) e)
                (ai (list 'NOT (list 'IN 'iox_ e)))))
            (ass)))
      (dk-opened (lambda () (di))))))
(qed 'complement-in-big-union)
(gloss! 'complement-in-big-union
  "De Morgan for a union: a point lies in Y minus the union of the family c
   exactly when it lies in Y and in no member of c.")
(topic! 'complement-in-big-union 'plumbing)

;;; =====================================================================
;;; (8) De Morgan, complement of an intersection
;;; =====================================================================
;;; This one IS a set equation, and it is the form a compactness duality needs:
;;; "the intersection of the closed family is empty" becomes "the complements
;;; cover".  The inhabitedness guard is the same one as everywhere above: for
;;; the empty family the left side is Y and the right side is empty.

(sp (make-wff '(FORALL ioy_ (FORALL c_
   (IMPLIES (FORSOME iou_ (IN iou_ c_))
     (= (COMPLEMENT-IN ioy_ (INTERSECTION-OF c_))
        (BIG-UNION iow_ c_ (COMPLEMENT-IN ioy_ iow_))))))))
(di) (di)
(have! '(FORALL x (IFF (IN x (COMPLEMENT-IN ioy_ (INTERSECTION-OF c_)))
                       (IN x (BIG-UNION iow_ c_ (COMPLEMENT-IN ioy_ iow_)))))
  (lambda ()
    (di)
    (for-each
      (lambda (leaf)
        (dk-focus! leaf)
        (if (iof-head? (caddr (dk-goal)) 'BIG-UNION)
            ;; => : x is outside the intersection, and the family is inhabited,
            ;; so some member misses x; that member's complement holds x.
            (begin
              (mac-h 'complement-in-membership
                     '(IN x (COMPLEMENT-IN ioy_ (INTERSECTION-OF c_))))
              (dk-split! '(AND (IN x ioy_) (NOT (IN x (INTERSECTION-OF c_)))))
              (have! (list 'NOT (iof-all-of 'x 'c_))
                (lambda () (dk-fact! 'intersection-of-membership 'c_ 'x) (prop)))
              (let ((v (dk-skolem! (push-not-h (list 'NOT (iof-all-of 'x 'c_))))))
                (for-each
                  (lambda (n)
                    (dk-focus! n)
                    (if (iof-head? (caddr (dk-goal)) 'COMPLEMENT-IN)
                        (begin (mac 'complement-in-membership)
                               (iof-close-all! (lambda () (di))))
                        (ass)))
                  (dk-opened (lambda () (bu-mi v))))))
            ;; <= : x misses some member of the family, so it misses the
            ;; intersection.
            (let ((e (iof-bu-witness!
                      '(IN x (BIG-UNION iow_ c_ (COMPLEMENT-IN ioy_ iow_))) 'c_)))
              (mac-h 'complement-in-membership (list 'IN 'x (list 'COMPLEMENT-IN 'ioy_ e)))
              (dk-split! (list 'AND (list 'IN 'x 'ioy_)
                               (list 'NOT (list 'IN 'x e))))
              (mac 'complement-in-membership)
              (for-each
                (lambda (n)
                  (dk-focus! n)
                  (if (eq? (car (dk-goal)) 'NOT)
                      (begin
                        (have! (list 'NOT (iof-all-of 'x 'c_))
                          (lambda ()
                            (di)
                            (dk-apply! (iof-all-of 'x 'c_) e)
                            (ai (list 'NOT (list 'IN 'x e)))))
                        (dk-fact! 'intersection-of-membership 'c_ 'x)
                        (prop))
                      (ass)))
                (dk-opened (lambda () (di)))))))
      (dk-opened (lambda () (di))))))
(fact 'class-extensionality '(COMPLEMENT-IN ioy_ (INTERSECTION-OF c_))
                            '(BIG-UNION iow_ c_ (COMPLEMENT-IN ioy_ iow_)))
(ass)
(qed 'complement-in-intersection-of)
(gloss! 'complement-in-intersection-of
  "De Morgan for an intersection: for an inhabited family c, the complement in
   Y of the intersection of c is the union of the complements in Y of the
   members of c.  This is the identity that turns 'the closed family has empty
   intersection' into 'the complements cover the space'.")
(topic! 'complement-in-intersection-of 'plumbing)
