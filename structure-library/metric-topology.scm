;;; metric-topology.scm -- balls, r-nets, total-boundedness.
;;;
;;; Builds on metric-space.scm.  Adds basic point-set vocabulary for
;;; arguments about covers and approximation:
;;;
;;;   BALL(s, x, r)        open ball: { y in X(s) : D(s)(x,y) < r }
;;;   IS-R-NET(s, F, A, r) F approximates A to within r in s
;;;   TOTALLY-BOUNDED(s)   for every positive r, X(s) has a finite r-net
;;;
;;; "r > 0" is spelled (AND (IN r RR) (<= 0 r) (NOT (= 0 r))), matching
;;; the eps > 0 idiom already in cc-complete (complex.scm).  Strict <
;;; is similarly spelled (AND (<= a b) (NOT (= a b))) since VNB has
;;; <= as primitive but no strict <.  Both idioms are candidates for
;;; a future POS / < cleanup pass; they appear throughout the analytic
;;; vocabulary and the inconsistency would be jarring if introduced here
;;; piecemeal.
;;;
;;; Centers-only formulation: F is a set of points (centers) in X(s),
;;; not a set of balls.  The set-of-balls view is one functoid away
;;; ({ BALL(s,c,r) : c in F }), but pigeonhole-on-centers is what the
;;; standard metric-space arguments actually use.

;;; -----------------------------------------------------------------------
;;; BALL(s, x, r) -- the open r-ball around x in metric space s.

(def-functoid 'BALL '(s x r)
  '(SEP y (X s)
        (AND (<= ((D s) x y) r)
             (NOT (= ((D s) x y) r)))))

;;; ball-membership: y in BALL(s,x,r) iff y in X(s) and D(s)(x,y) < r.
;;; Direct from SEP membership; recorded so proofs can rewrite by name.
(theory-add-axiom! *current-theory* 'ball-membership
  '(FORALL s
     (FORALL x
       (FORALL r
         (FORALL y
           (IFF (IN y (BALL s x r))
                (AND (IN y (X s))
                     (AND (<= ((D s) x y) r)
                          (NOT (= ((D s) x y) r))))))))))
(warrant! 'ball-membership 'proof
  "BALL(s,x,r) is the def-functoid SEP(y in X(s) | d(x,y)<=r and d(x,y)!=r); the iff is just SEP-membership after unfolding BALL.  Definitional.")

;;; ball-subset-carrier: BALL(s,x,r) subset X(s).
(theory-add-axiom! *current-theory* 'ball-subset-carrier
  '(FORALL s
     (FORALL x
       (FORALL r
         (SUBSET (BALL s x r) (X s))))))
(warrant! 'ball-subset-carrier 'proof
  "BALL is a SEP over X(s) (def-functoid), so every member lies in X(s); subset is immediate from ball-membership.")

;;; ball-is-set: BALL(s,x,r) in SET whenever s is a metric space.
;;; Derivable from SEP sethood + X(s) in SET (carrier typing of
;;; IS-METRIC-SPACE).  Kept as a named macete so BALL-using proofs don't
;;; re-derive sethood at every use; not a per-operator closure proliferation.
(theory-add-axiom! *current-theory* 'ball-is-set
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x
         (FORALL r
           (IN (BALL s x r) SET))))))
(warrant! 'ball-is-set 'proof
  "BALL(s,x,r) is a subclass of X(s) (ball-subset-carrier); X(s) is a set (carrier typing of IS-METRIC-SPACE); a subclass of a set is a set (separation).")

;;; ball-center-in: x is in its own r-ball when r > 0.
;;; Uses metric-self-zero: D(s)(x,x) = 0 < r.
(theory-add-axiom! *current-theory* 'ball-center-in
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x
         (IMPLIES (IN x (X s))
           (FORALL r
             (IMPLIES (AND (IN r RR) (<= 0 r) (NOT (= 0 r)))
               (IN x (BALL s x r)))))))))
(warrant! 'ball-center-in 'proof
  "metric-self-zero gives d(s)(x,x)=0, so 0<=r and 0!=r (r>0) put x into the SEP; ball-membership then gives x in BALL(s,x,r).")

;;; ball-2r-triangle: two points in the same r-ball are within 2r of each
;;; other.  The workhorse for arguments that pigeonhole sequence terms
;;; through a finite cover of r-balls -- once two terms land in the same
;;; ball, the 2r bound supplies the Cauchy estimate.
;;;
;;; Derivable from metric-triangle + metric-sym; left as an axiom during
;;; the library-build phase per [[feedback-library-axioms-fine]].
(theory-add-axiom! *current-theory* 'ball-2r-triangle
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x
         (IMPLIES (IN x (X s))
           (FORALL r
             (IMPLIES (AND (IN r RR) (<= 0 r) (NOT (= 0 r)))
               (FORALL y
                 (IMPLIES (IN y (BALL s x r))
                   (FORALL z
                     (IMPLIES (IN z (BALL s x r))
                       (AND (<= ((D s) y z) (+ r r))
                            (NOT (= ((D s) y z) (+ r r)))))))))))))))
(warrant! 'ball-2r-triangle 'proof
  "metric-triangle: d(y,z) <= d(y,x)+d(x,z).  Each of d(y,x)=d(x,y) (metric-sym) and d(x,z) is < r by ball-membership, so d(y,z) < r+r.")

;;; -----------------------------------------------------------------------
;;; IS-R-NET(s, F, A, r) -- F is an r-net for A in metric space s.
;;;
;;; Every point of A is within distance < r of some point of F.  The
;;; centers F need not lie inside A; in classical analysis r-nets for a
;;; subset A often have centers outside A (e.g. centers in the closure).
;;; For our use A = X(s) and F lives inside X(s) by the typing of D(s).

(register-constant! 'IS-R-NET 'predicate)

(theory-add-axiom! *current-theory* 'is-r-net-def
  '(FORALL s
     (FORALL F
       (FORALL A
         (FORALL r
           (IFF (IS-R-NET s F A r)
                (FORALL p
                  (IMPLIES (IN p A)
                    (FORSOME c
                      (AND (IN c F)
                           (AND (<= ((D s) c p) r)
                                (NOT (= ((D s) c p) r)))))))))))))

;;; -----------------------------------------------------------------------
;;; TOTALLY-BOUNDED(s) -- every positive r admits a finite r-net for X(s).
;;;
;;; Includes IS-METRIC-SPACE(s) in the unfolding; total-boundedness is
;;; only meaningful on a metric space.

(register-constant! 'TOTALLY-BOUNDED 'predicate)

(theory-add-axiom! *current-theory* 'totally-bounded-def
  '(FORALL s
     (IFF (TOTALLY-BOUNDED s)
          (AND (IS-METRIC-SPACE s)
               (FORALL r
                 (IMPLIES (AND (IN r RR) (<= 0 r) (NOT (= 0 r)))
                   (FORSOME F
                     (AND (IN (CARD F) NN)
                          (IS-R-NET s F (X s) r)))))))))
