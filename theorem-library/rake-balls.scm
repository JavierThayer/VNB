;;; rake-balls.scm -- the open-ball read-offs of structure-library/metric-topology.scm,
;;; PROVEN.  Five facts that stood there as `support' + `warrant! ... 'proof' -- a tier
;;; that claims a machine-checked proof exists -- and had none:
;;;
;;;     ball-membership       y in BALL(s,x,r)  iff  y in PTS(s) and d(x,y) < r
;;;     ball-mem-from-le      a non-strict bound d(x,y) <= d with d < r lands y
;;;                           strictly inside the r-ball
;;;     ball-is-set           BALL(s,x,r) is a set, in a metric space
;;;     ball-center-in        the centre lies in its own ball of positive radius
;;;     ball-2r-triangle      two points of one r-ball are less than 2r apart
;;;     cauchy-block-estimate the metric leaf of the Cauchy estimate
;;;                           (theorem-library/cauchy-subsequence.scm:297)
;;;
;;; `ball-mem-from-le' was one hypothesis short as first written; it has since been
;;; GUARDED at its site on the centre, and the note at the end of this header records
;;; what the guard was for.
;;;
;;; PLAN.  BALL is a `def-functoid', so `mac' unfolds it in a GOAL and `mac-h' cannot
;;; unfold it in an ASSUMPTION.  `ball-sep-unfold' (ball-cover-lemmas.scm) is the
;;; unfolding EQUATION, proven
;;; the one-line way (`(di) (mac 'BALL) (qrfl)', CLAUDE.md's functoid recipe and
;;; theorem-library/poly-membership.scm's seven worked instances); as a THEOREM it is
;;; what `mac-h' needs, and `sep-me' then reads the membership apart.  Everything else
;;; is ball-membership plus the metric laws:
;;;
;;;   ball-mem-from-le   type d(x,y) by metric-dist-real, rewrite the goal by
;;;                      ball-membership, one Farkas call for d(x,y) < r, unfold that
;;;                      `<' into the goal's two order conjuncts.
;;;   ball-is-set        unfold the goal, kernel SEP sethood, PTS(s) in SET off the
;;;                      IS-METRIC-SPACE unfold.  Does not use ball-membership.
;;;   ball-center-in     rewrite the goal by ball-membership, substitute
;;;                      metric-self-zero (d(x,x) = 0), and the two positivity
;;;                      conjuncts of the hypothesis are literally what is left.
;;;   ball-2r-triangle   ball-membership on each of y, z; metric-sym + metric-triangle;
;;;                      one Farkas call (`ineq') over d(y,z) <= d(y,x) + d(x,z),
;;;                      d(y,x) = d(x,y), d(x,y) < r, d(x,z) < r.
;;;   cauchy-block-estimate  substitute U, cite ball-2r-triangle, then ineq over
;;;                      d(y,z) <= r+r, r <= d, d+d = eps.
;;;
;;; WINDOW.  [255, 261), 0-based over load.scm's quoted file list.
;;;   lo = 255: the highest-positioned citation is structure-library/metric-laws (254),
;;;             which proves metric-self-zero / metric-sym / metric-triangle.  The
;;;             others are lower: op-typing 197 (metric-dist-real), pos-rr-bridges 176
;;;             (rr-pos-rr-in-rr), order-predicates 39 (`<', POS-RR), ineq-oracle 31,
;;;             metric-topology 27 (BALL), driver-kit 140, prop 143.
;;;   hi = 261: theorem-library/cauchy-subseq-proof (261) cites cauchy-block-estimate
;;;             at its line 213.  Nothing proven cites any of the four ball facts, so
;;;             they alone would allow [255, end).
;;;
;;; TRAPS MET, both of them CLAUDE.md's.
;;;   (1) `ineq' poisoning: the hypothesis `U = BALL(s,c,r)' is `='-headed, so a finder
;;;       that names every arithmetic-SHAPED premise hands the oracle the atoms `U' and
;;;       `BALL(s,c,r)', which can never carry an `IN _ RR' certificate, and the call
;;;       fails blaming the GOAL.  `rkb-ineq*' names premises by formula instead.
;;;   (2) `ineq' certifies an atom only from a STANDALONE `(IN t RR)' assumption: with
;;;       `(AND (IN r RR) (AND (<= 0 r) ...))' unsplit in the context, r is uncertified
;;;       and the same misleading message appears.  Hence the `rr-pos-rr-in-rr' lines.
;;;
;;; WHY `ball-mem-from-le' CARRIES A GUARD ON THE CENTRE.  As first written it read
;;;
;;;     IS-METRIC-SPACE(s) => forall x,y,d,r.
;;;        y in PTS(s) and d in RR and r in RR and d(s)(x,y) <= d and d < r
;;;        => y in BALL(s,x,r)
;;;
;;; and never typed the CENTRE x.  Both conclusions -- d(x,y) <= r and d(x,y) /= r --
;;; go through transitivity of <= on RR, and every transitivity in the tree
;;; (rr-leq-transitive, number-systems.scm:415; rr-le-trans; co-le-trans) is guarded on
;;; all three arguments lying in RR.  The certificate for d(s)(x,y) is metric-dist-real
;;; (op-typing.scm:120), which needs BOTH points in PTS(s); nothing derives x in PTS(s)
;;; from the premises, and no axiom infers `a in RR' from `a <= b'.  Probed: the goal
;;; d(x,y) < r came back `ineq: goal not a linear-RR consequence' with the context
;;; {d < r, d(x,y) <= d, r in RR, d in RR, y in PTS(s), IS-METRIC-SPACE(s)}.  The
;;; statement was not FALSE -- with x outside PTS(s) the term d(s)(x,y) is an
;;; application outside the domain, so the premise was undetermined rather than
;;; refuted -- it was underdetermined.  `(IMPLIES (IN x (PTS s)) ...)' now sits
;;; immediately after the `(FORALL x' at the support site, and the proof below is the
;;; six lines that then close it.

;;; --- file-local helpers (prefix rkb-) -----------------------------------
;;; Split an IFF goal and drive each half; the forward leaf is the one whose GOAL is
;;; the conjunction (discriminated on the goal, never on `dk-opened' order).
(define (rkb-iff! fwd bwd)
  (let ((ls (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'and)) ls)) (fwd)
    (dk-focus! (any-pred (lambda (n) (not (eq? (car (dk-goal-of n)) 'and))) ls)) (bwd)))

;;; `ineq' by FORMULA rather than by shape -- see trap (1) in the header.
(define (rkb-idx f)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rkb-idx: not in context" f))
          ((equal? (car l) f) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (rkb-ineq* . fs) (apply ineq (map rkb-idx fs)))

;;; =====================================================================
;;; ball-unfold -- REMOVED 2026-09-20 (batch 11, proven-duplicate-audit).
;;; The functoid's defining equation is already a citable theorem under the
;;; name `ball-sep-unfold' (theorem-library/ball-cover-lemmas.scm:61), which
;;; loads before this file; its gloss moved there.  The citations below name
;;; that one.
;;; =====================================================================

;;; =====================================================================
;;; ball-membership
;;; =====================================================================
(sp (make-wff '(FORALL s
     (FORALL x
       (FORALL r
         (FORALL y
           (IFF (IN y (BALL s x r))
                (AND (IN y (PTS s))
                     (AND (<= ((DIST s) x y) r)
                          (NOT (= ((DIST s) x y) r)))))))))))
(di)
(rkb-iff!
  ;; => : rewrite the hypothesis into the SEP and read both halves off it.
  (lambda ()
    (mac-h 'ball-sep-unfold '(IN y (BALL s x r)))
    (sep-me '(IN y (SEP y (PTS s) (AND (<= ((DIST s) x y) r)
                                       (NOT (= ((DIST s) x y) r))))))
    (prop))
  ;; <= : unfold the GOAL and discharge sep-mi's two obligations.
  (lambda ()
    (dk-split! '(AND (IN y (PTS s))
                     (AND (<= ((DIST s) x y) r)
                          (NOT (= ((DIST s) x y) r)))))
    (mac 'BALL)
    (for-each (lambda (n) (dk-focus! n) (prop)) (dk-opened (lambda () (sep-mi))))))
(qed 'ball-membership)
(gloss! 'ball-membership
  "y lies in the open ball BALL(s,x,r) iff y is a point of s at distance strictly
   less than r from the centre x.  The read-off of the ball, in both directions.")
(topic! 'ball-membership 'plumbing)

;;; =====================================================================
;;; ball-mem-from-le -- a non-strict bound below r lands strictly inside
;;; =====================================================================
(sp (make-wff
 '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x
         (IMPLIES (IN x (PTS s))
         (FORALL y
           (FORALL d
             (FORALL r
               (IMPLIES (AND (IN y (PTS s))
                        (AND (IN d RR)
                        (AND (IN r RR)
                        (AND (<= ((DIST s) x y) d)
                             (< d r)))))
                 (IN y (BALL s x r))))))))))))
(dk-peel!)
(dk-split! '(AND (IN y (PTS s))
            (AND (IN d RR)
            (AND (IN r RR)
            (AND (<= ((DIST s) x y) d)
                 (< d r))))))
(fact 'metric-dist-real 's 'x 'y)          ; the guard on x is exactly what this needs
(mac 'ball-membership)
(have! '(< ((DIST s) x y) r)
       (lambda () (rkb-ineq* '(<= ((DIST s) x y) d) '(< d r))))
(mac-h '< '(< ((DIST s) x y) r))           ; unfold to the goal's two order conjuncts
(prop)
(qed 'ball-mem-from-le)
(gloss! 'ball-mem-from-le
  "A point at distance at most d from the centre, with d < r, lies in the open
   r-ball: the bridge from continuity's non-strict bound to strict ball membership.
   Guarded on the centre lying in PTS(s), which is what types the distance.")
(topic! 'ball-mem-from-le 'topology)

;;; =====================================================================
;;; ball-is-set -- a SEP over the carrier of a metric space
;;; =====================================================================
(sp (make-wff '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x
         (FORALL r
           (IN (BALL s x r) SET)))))))
(dk-peel!)
(mac 'BALL) (sep-set)
;; the one leaf sep-set leaves: PTS(s) in SET, a conjunct of the IS-METRIC-SPACE unfold
(dk-split-all! (dk-landed (lambda () (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s)))))
(ass)
(qed 'ball-is-set)
(gloss! 'ball-is-set
  "An open ball in a metric space is a set: it is a separation over PTS(s), and the
   carrier of a metric space is a set.")
(topic! 'ball-is-set 'plumbing)

;;; =====================================================================
;;; ball-center-in -- the centre is in its own ball of positive radius
;;; =====================================================================
(sp (make-wff '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x
         (IMPLIES (IN x (PTS s))
           (FORALL r
             (IMPLIES (AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
               (IN x (BALL s x r))))))))))
(dk-peel!)
(dk-split! '(AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r)))))
(fact 'metric-self-zero 's 'x)
(mac 'ball-membership)
(subst '(= ((DIST s) x x) 0))          ; goal becomes  x in PTS(s) and 0 <= r and 0 /= r
(prop)
(qed 'ball-center-in)
(gloss! 'ball-center-in
  "The centre of a ball of positive radius lies in it: d(s)(x,x) = 0 < r.")
(topic! 'ball-center-in 'topology)

;;; =====================================================================
;;; ball-2r-triangle -- two points of one r-ball are less than 2r apart
;;; =====================================================================
(sp (make-wff '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x
         (IMPLIES (IN x (PTS s))
           (FORALL r
             (IMPLIES (AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
               (FORALL y
                 (IMPLIES (IN y (BALL s x r))
                   (FORALL z
                     (IMPLIES (IN z (BALL s x r))
                       (AND (<= ((DIST s) y z) (+ r r))
                            (NOT (= ((DIST s) y z) (+ r r))))))))))))))))
(dk-peel!)
(dk-split! '(AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r)))))
(mac-h 'ball-membership '(IN y (BALL s x r)))
(dk-split! '(AND (IN y (PTS s)) (AND (<= ((DIST s) x y) r) (NOT (= ((DIST s) x y) r)))))
(mac-h 'ball-membership '(IN z (BALL s x r)))
(dk-split! '(AND (IN z (PTS s)) (AND (<= ((DIST s) x z) r) (NOT (= ((DIST s) x z) r)))))
;; every atom the oracle will see needs an IN _ RR certificate
(fact 'metric-dist-real 's 'x 'y)
(fact 'metric-dist-real 's 'x 'z)
(fact 'metric-dist-real 's 'y 'x)
(fact 'metric-dist-real 's 'y 'z)
(fact 'metric-sym 's 'y 'x)                ; d(y,x) = d(x,y)
(fact 'metric-triangle 's 'y 'x 'z)        ; d(y,z) <= d(y,x) + d(x,z)
;; the two ball bounds, as strict inequalities the oracle can read
(have! '(< ((DIST s) x y) r) (lambda () (mac '<) (prop)))
(have! '(< ((DIST s) x z) r) (lambda () (mac '<) (prop)))
(have! '(< ((DIST s) y z) (+ r r))
       (lambda () (rkb-ineq* '(<= ((DIST s) y z) (+ ((DIST s) y x) ((DIST s) x z)))
                             '(= ((DIST s) y x) ((DIST s) x y))
                             '(< ((DIST s) x y) r)
                             '(< ((DIST s) x z) r))))
(mac-h '< '(< ((DIST s) y z) (+ r r)))     ; unfold to the goal's AND
(ass)
(qed 'ball-2r-triangle)
(gloss! 'ball-2r-triangle
  "Two points of one open r-ball are strictly less than 2r apart: the triangle
   inequality through the centre, with symmetry on one leg.")
(topic! 'ball-2r-triangle 'topology)

;;; =====================================================================
;;; cauchy-block-estimate -- the metric leaf of the Cauchy estimate
;;; (was a support at theorem-library/cauchy-subsequence.scm:297)
;;; =====================================================================
(sp (make-wff
 '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL c (IMPLIES (IN c (PTS s))
       (FORALL r (IMPLIES (POS-RR r)
         (FORALL U (IMPLIES (= U (BALL s c r))
           (FORALL y (IMPLIES (IN y U)
             (FORALL z (IMPLIES (IN z U)
               (FORALL d (IMPLIES (POS-RR d)
                 (FORALL eps (IMPLIES (IN eps RR)
                   (IMPLIES (<= r d)
                     (IMPLIES (= (+ d d) eps)
                       (<= ((DIST s) y z) eps)))))))))))))))))))))
(dk-peel!)
;; carry y, z from U into the ball
(have! '(IN y (BALL s c r)) (lambda () (subst '(= (BALL s c r) U)) (ass)))
(have! '(IN z (BALL s c r)) (lambda () (subst '(= (BALL s c r) U)) (ass)))
;; ball-2r-triangle is guarded on the verbose positivity form
(have! '(AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
       (lambda () (mac-h 'POS-RR '(POS-RR r)) (ass)))
(dk-split! (dk-fact! 'ball-2r-triangle 's 'c 'r 'y 'z))
;; typings for the oracle
(have! '(IN y (PTS s)) (lambda () (mac-h 'ball-membership '(IN y (BALL s c r))) (prop)))
(have! '(IN z (PTS s)) (lambda () (mac-h 'ball-membership '(IN z (BALL s c r))) (prop)))
(fact 'metric-dist-real 's 'y 'z)
(fact 'rr-pos-rr-in-rr 'd)
(fact 'rr-pos-rr-in-rr 'r)
(rkb-ineq* '(<= ((DIST s) y z) (+ r r)) '(<= r d) '(= (+ d d) eps))
(qed 'cauchy-block-estimate)
(gloss! 'cauchy-block-estimate
  "Two points of one r-ball are within eps, when r <= d and d + d = eps: the metric
   leaf of the Cauchy estimate in the totally-bounded subsequence argument.")
(topic! 'cauchy-block-estimate 'combinatorial)
