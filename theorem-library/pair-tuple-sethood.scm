;;; pair-tuple-sethood.scm -- a pair [u,v] is a set, PROVEN modulo 0.
;;;
;;; The gap this fills.  Nothing in the library concludes sethood of a TUPLE.
;;; `TUPLES' is axiomatised entirely by consequences of membership -- there is
;;; no IFF about it anywhere, so no fact about entries ever establishes that a
;;; tuple lies in a class (structure-notes/tuples-rung.md, section 1).  In
;;; particular `list-sethood' (theorem-library/axioms.scm) needs `L in TUPLES(X)'
;;; as a HYPOTHESIS, which for a literal pair is exactly what one cannot get.
;;; So the goal
;;;
;;;     u in SET, v in SET  |-  [u, v] in SET
;;;
;;; -- which arises whenever a driver builds a pair and then needs it typed --
;;; had no route at all, and was being re-derived by hand per proof.
;;;
;;; The route.  Do not go through TUPLES; go through CARTESIAN and come back:
;;;
;;;   (1) `ci' (pi-cartesian-intro!, primitive-inferences.scm:669) reduces
;;;       `[u,v] in CARTESIAN(X,Y)' to `u in X' and `v in Y', and carries NO
;;;       sethood guard on X or Y.  They may be proper classes; SET itself may
;;;       be one of them.
;;;   (2) `membership-implies-sethood' (library.scm:249, base, hence primitive)
;;;       turns membership in ANY class into sethood of the member.
;;;
;;; Step (2) is the point.  One might expect to need `CARTESIAN(X,Y) in SET'
;;; and reach for `cartesian-set-iff' -- but that is both unavailable (for
;;; X = Y = SET it is false) and unnecessary: membership in a proper class
;;; establishes sethood of the member just as well as membership in a set.
;;;
;;; Both theorems are stated over ARBITRARY classes X and Y rather than for
;;; X = Y = SET, which costs nothing in the proof and is what callers actually
;;; have -- a driver holds `x in CARR(s)', not `x in SET'.  The SET-to-SET case
;;; the gap was found on is the instance X := SET, Y := SET.
;;;
;;; BINDER NAMES.  The classes are X, Y and the elements u, v -- NOT A, B and
;;; a, b.  Both the VNB reader and MIT Scheme fold to lowercase, so `A' and `a'
;;; are ONE name: the first draft of this file bound (FORALL A (FORALL B
;;; (FORALL a (FORALL b ...)))), whose inner binders silently shadowed the outer
;;; and turned the hypothesis `u in X' into `a in a'.  It still proved -- the
;;; shadowing is consistent, so `ci' and `ass' matched -- and the theorem was
;;; junk.  `case-fold-audit' caught it at load ("2 formula(s) have a shadowing
;;; binder").  Do not reintroduce single-letter binder pairs that differ only
;;; in case.
;;;
;;; CURRIED antecedents, for `fun-apply-type-proof''s reason: `fact' peels and
;;; detaches both hypotheses in one call, where an AND antecedent would make
;;; every caller assemble the conjunction and `detach!' by hand.
;;;
;;; Needs only base axioms plus interactive/driver-kit, so it loads with the
;;; other elementary plumbing.

;;; --- local helpers (file-local, per the driver-kit containment rule) -------

;;; Focus the open leaf whose goal is exactly FORM.  Errors on a miss: `ci'
;;; opens two leaves and the first `ass' hands focus to an engine-chosen node,
;;; so the second `ass' must be aimed, and a helper that silently missed would
;;; leave the sibling open to surface branches later.
(define (pts-focus! form)
  (let ((hits (filter (lambda (l)
                        (equal? (wff-formula (sequent-node-assertion l)) form))
                      (proof-leaves))))
    (if (null? hits)
        (error "pts-focus!: no open leaf with goal" form)
        (dk-focus! (car hits)))))

;;; Peel the leading FORALL/IMPLIES prefix until the head changes.  `di' is
;;; greedy but not uniformly so -- on this statement the first call takes the
;;; quantifier group and leaves the implication chain -- so a counted run of
;;; `di's would land on the wrong goal.  Guarded on progress.
(define (pts-peel!)
  (let loop ((guard 0))
    (let ((g (dk-goal)))
      (if (and (< guard 12) (pair? g) (memq (car g) '(FORALL IMPLIES)))
          (begin (di) (loop (+ guard 1)))
          g))))

;;; --- pair-in-cartesian ----------------------------------------------------
;;; u in X and v in Y give [u,v] in CARTESIAN(X,Y).  This is `ci' turned into a
;;; citable fact: the rule fires only on a GOAL of that shape, so a driver
;;; holding the two memberships and wanting the pair typed forward had to
;;; restructure its goal.  With this it is one `fact'.

(sp (make-wff '(FORALL X (FORALL Y (FORALL u (FORALL v
     (IMPLIES (IN u X)
              (IMPLIES (IN v Y)
                       (IN (LIST u v) (CARTESIAN X Y))))))))))
(pts-peel!)
(ci)
(pts-focus! '(IN u X)) (ass)
(pts-focus! '(IN v Y)) (ass)
(qed 'pair-in-cartesian)
(topic! 'pair-in-cartesian 'plumbing)

;;; --- pair-tuple-is-set ----------------------------------------------------
;;; The fact the gap was found on: a member of any class is a set, and the pair
;;; is a member of the product.

(sp (make-wff '(FORALL X (FORALL Y (FORALL u (FORALL v
     (IMPLIES (IN u X)
              (IMPLIES (IN v Y)
                       (IN (LIST u v) SET)))))))))
(pts-peel!)
(fact 'pair-in-cartesian 'X 'Y 'u 'v)
(fact 'membership-implies-sethood '(LIST u v) '(CARTESIAN X Y))
(ass)
(qed 'pair-tuple-is-set)
(topic! 'pair-tuple-is-set 'plumbing)
