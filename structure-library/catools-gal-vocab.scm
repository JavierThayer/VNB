;;; catools-gal-vocab.scm -- divisibility in an integral domain; Euclidean domains as in the galois-theory
;;; notes (Definition 1.2) (CA-TOOLS, galois-theory B1, 2026-10-26).
;;; DEFINITIONS ONLY.  Destination: structure-library/catools-gal-vocab.scm, library algebra.
;;; Load window: after structure-library/euclidean-ring and integral-domain.
;;;
;;; The tree's IS-EUCLIDEAN-RING asks only for division with remainder; the notes' degree function
;;; (Definition 1.2) also has nu(a) <= nu(ab) for a, b /= 0, which Lemma 1.7 and the existence half of
;;; Proposition 1.8 use.  IS-EUCLIDEAN-DOMAIN is the notes' notion; every one is an IS-EUCLIDEAN-RING
;;; (euclidean-domain-is-euclidean-ring).
(def-predicate 'IS-UNIT '(gus_ guu_)
  '(AND (IN guu_ (CARR gus_))
        (FORSOME guv_ (AND (IN guv_ (CARR gus_)) (= ((MUL gus_) guu_ guv_) (ONE gus_))))))
(notation! 'IS-UNIT 'kind 'predicate 'arity 2 'english "$2 is a unit of $1")

(def-predicate 'DIVIDES '(gds_ gda_ gdb_)
  '(AND (IN gda_ (CARR gds_))
        (AND (IN gdb_ (CARR gds_))
             (FORSOME gdk_ (AND (IN gdk_ (CARR gds_)) (= gdb_ ((MUL gds_) gdk_ gda_)))))))
(notation! 'DIVIDES 'kind 'predicate 'arity 3 'english "$2 divides $3 in $1")

;;; The notes' "prime": p = ab forces a or b to be a unit.  The notes leave p /= 0 and p not a unit
;;; implicit; they are written here (otherwise 0 and the units would be prime).
(def-predicate 'IS-PRIME-ELEMENT '(gps_ gpp_)
  '(AND (IN gpp_ (CARR gps_))
        (AND (NOT (= gpp_ (ZERO gps_)))
             (AND (NOT (IS-UNIT gps_ gpp_))
                  (FORALL gpa_ (IMPLIES (IN gpa_ (CARR gps_)) (FORALL gpb_ (IMPLIES (IN gpb_ (CARR gps_))
                    (IMPLIES (= gpp_ ((MUL gps_) gpa_ gpb_)) (OR (IS-UNIT gps_ gpa_) (IS-UNIT gps_ gpb_)))))))))))
(notation! 'IS-PRIME-ELEMENT 'kind 'predicate 'arity 2 'english "$2 is a prime of $1")

;;; Definition 1.2: a degree function nu on the integral domain s.
(def-predicate 'IS-DEGREE-FUNCTION '(gfs_ gfn_)
  (conjuncts->and
    (list
      '(IS-INTEGRAL-DOMAIN gfs_)
      '(IN gfn_ (FUN (CARR gfs_) NN))
      '(FORALL gfa_ (IMPLIES (IN gfa_ (CARR gfs_)) (FORALL gfb_ (IMPLIES (IN gfb_ (CARR gfs_))
         (IMPLIES (NOT (= gfa_ (ZERO gfs_))) (IMPLIES (NOT (= gfb_ (ZERO gfs_)))
           (<= (gfn_ gfa_) (gfn_ ((MUL gfs_) gfa_ gfb_)))))))))
      '(FORALL gfa_ (IMPLIES (IN gfa_ (CARR gfs_)) (FORALL gfb_ (IMPLIES (IN gfb_ (CARR gfs_))
         (IMPLIES (NOT (= gfa_ (ZERO gfs_)))
           (FORSOME gfq_ (AND (IN gfq_ (CARR gfs_))
             (OR (= gfb_ ((MUL gfs_) gfa_ gfq_))
                 (< (gfn_ ((ADD gfs_) gfb_ ((NEG gfs_) ((MUL gfs_) gfa_ gfq_)))) (gfn_ gfa_)))))))))))))
(notation! 'IS-DEGREE-FUNCTION 'kind 'predicate 'arity 2 'english "$2 is a degree function on $1")

(def-predicate 'IS-EUCLIDEAN-DOMAIN '(ges_)
  '(AND (IS-INTEGRAL-DOMAIN ges_) (FORSOME gen_ (IS-DEGREE-FUNCTION ges_ gen_))))
(notation! 'IS-EUCLIDEAN-DOMAIN 'kind 'predicate 'arity 1 'english "$1 is a Euclidean domain")
