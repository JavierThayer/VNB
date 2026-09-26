;;; segments-triangles.scm -- THE VOCABULARY OF CAUCHY-GOURSAT (complex-analysis.pdf
;;; ch. 3, s. 3.2).  DEFINITIONS ONLY; every law is PROVEN in
;;; theorem-library/goursat.scm.  Batch 30, 2026-09-25.
;;;
;;; THE SPECIFICATION is docs/goursat-definitions-2026-09-25.md (the user's decisions
;;; of 2026-09-25), written here exactly as decided:
;;;
;;;     SEG-PATH(z1, z2)      the road s |-> z1 + s*(z2 - z1) on [0, 1]
;;;     SEG-DERIV(z1, z2)     its derivative s |-> z2 - z1 on [0, 1]
;;;     SEG-INT(f, z1, z2)    LINE-INT(f, SEG-PATH(z1,z2), SEG-DERIV(z1,z2), 0, 1),
;;;                           the notes' integral over the segment <z1, z2>
;;;     TRI-INT(f, a, b, c)   SEG-INT(f,a,b) + SEG-INT(f,b,c) + SEG-INT(f,c,a), the
;;;                           integral over the triangular path, as the notes' Prop 3.1
;;;                           (path additivity) reduces it
;;;     CONV3(a, b, c)        the z in CC with z = al*a + be*b + ga*c for some al, be, ga
;;;                           in [0, 1] with al + be + ga = 1 (the convex hull)
;;;     IS-CONVEX(U)          z + t*(w - z) in U for z, w in U and t in [0, 1]
;;;     CC-MID(x, y)          (x + y) * recip(2), the notes' m(x, y)
;;;
;;; The segment is the shape of `segment-is-road' (theorem-library/road-laws.scm):
;;; SEG-PATH(z1, z2) is that road with z0 = z1 and w = z2 - z1.  Its binder is `sgs_',
;;; NOT the `psx_' of segment-is-road and NOT `pat_' (IS-ROAD's and LINE-INT's own
;;; binder): a binder that another body or a driver also binds is renamed by
;;; `subst-free' and every later `equal?' lookup of the rebuilt term misses silently
;;; (CLAUDE.md, "Writing proof drivers").  The bridge to segment-is-road's spelling is
;;; the proven equation `seg-path-bridge' (goursat.scm), alpha-equivalence included.
;;;
;;; STATEMENT CHECKS.
;;; (1) No strict `=' is asserted by a definition: every object is a functoid (a term
;;;     that may fail to denote) or a predicate.  SEG-INT and TRI-INT are defined
;;;     wherever LINE-INT is, i.e. under the hypotheses of `line-int-exists'; the laws
;;;     carry those hypotheses.
;;; (2) CONV3 is a SEP over CC, so it is a set, and its membership iff is a theorem
;;;     (`conv3-member-iff').  The coefficients range over CCINT(0, 1), which is a SEP
;;;     over RR, so they are real; al + be + ga = 1 pins the third.
;;; (3) IS-CONVEX says nothing about U being a subset of CC, as decided; the laws that
;;;     need it take it from an openness hypothesis or state it.
;;; (4) No binder folds onto a class name, an accessor or a registered constant; the
;;;     parameters and binders are sg*_ / cv*_ / cm*_, used nowhere else in the tree.
;;;
;;; Dependencies: path-integral.scm (LINE-INT), extreme-value.scm (CCINT), number
;;; systems (CC, recip).  Load slot: after structure-library/path-integral.

;;; ---------------------------------------------------------------------
;;; the segment <z1, z2> as a road on [0, 1]
;;; ---------------------------------------------------------------------
(def-functoid 'SEG-PATH '(sgp_ sgq_)
  '(VNB-LAMBDA sgs_ (CCINT 0 1) (+ sgp_ (* sgs_ (- sgq_ sgp_)))))

(notation! 'SEG-PATH 'kind 'functoid 'arity 2
           'english "the segment from $1 to $2")

(def-functoid 'SEG-DERIV '(sgp_ sgq_)
  '(VNB-LAMBDA sgs_ (CCINT 0 1) (- sgq_ sgp_)))

(notation! 'SEG-DERIV 'kind 'functoid 'arity 2
           'english "the derivative of the segment from $1 to $2")

;;; ---------------------------------------------------------------------
;;; the integral over a segment and over a triangular path
;;; ---------------------------------------------------------------------
(def-functoid 'SEG-INT '(sgf_ sgp_ sgq_)
  '(LINE-INT sgf_ (SEG-PATH sgp_ sgq_) (SEG-DERIV sgp_ sgq_) 0 1))

(notation! 'SEG-INT 'kind 'functoid 'arity 3
           'english "the integral of $1 along the segment from $2 to $3")

(def-functoid 'TRI-INT '(sgf_ sga_ sgb_ sgc_)
  '(+ (+ (SEG-INT sgf_ sga_ sgb_) (SEG-INT sgf_ sgb_ sgc_)) (SEG-INT sgf_ sgc_ sga_)))

(notation! 'TRI-INT 'kind 'functoid 'arity 4
           'english "the integral of $1 around the triangle $2 $3 $4")

;;; ---------------------------------------------------------------------
;;; the convex hull of three points, convexity, the midpoint
;;; ---------------------------------------------------------------------
(def-functoid 'CONV3 '(cva_ cvb_ cvc_)
  '(SEP cvz_ CC
     (FORSOME cvl_ (AND (IN cvl_ (CCINT 0 1))
     (FORSOME cvm_ (AND (IN cvm_ (CCINT 0 1))
     (FORSOME cvn_ (AND (IN cvn_ (CCINT 0 1))
       (AND (= (+ (+ cvl_ cvm_) cvn_) 1)
            (= cvz_ (+ (+ (* cvl_ cva_) (* cvm_ cvb_)) (* cvn_ cvc_))))))))))))

(notation! 'CONV3 'kind 'functoid 'arity 3
           'english "the convex hull of $1, $2, $3")

(def-predicate 'IS-CONVEX '(cvu_)
  '(FORALL cvx_ (IMPLIES (IN cvx_ cvu_)
     (FORALL cvy_ (IMPLIES (IN cvy_ cvu_)
       (FORALL cvt_ (IMPLIES (IN cvt_ (CCINT 0 1))
         (IN (+ cvx_ (* cvt_ (- cvy_ cvx_))) cvu_))))))))

(notation! 'IS-CONVEX 'kind 'predicate 'arity 1
           'english "$1 is convex")

(def-functoid 'CC-MID '(cmx_ cmy_)
  '(* (+ cmx_ cmy_) (recip 2)))

(notation! 'CC-MID 'kind 'functoid 'arity 2
           'english "the midpoint of $1 and $2")
