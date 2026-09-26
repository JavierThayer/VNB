;;; linear-functional.scm -- bounded linear functionals and the dual norm on a
;;; real NORMED-VECTOR-SPACE.  Vocabulary only (no proofs).
;;;
;;; A functional is a PLAIN function f : VEC(m) -> RR (no separate dual-space
;;; structure -- that is "generalities", deferred).  By the constant-registry
;;; rule, f is a variable head, so f(x) = (f x) is unambiguous function
;;; application; the accessors VEC/VADD/ACT/VNRM are registered heads.
;;;
;;; Scalars are RR (NORMED-VECTOR-SPACE pins SCAL = RR-NORMED-FIELD), so homogeneity and
;;; the bound use ordinary real *, abs, <=.
;;;
;;;   IS-LINEAR-FUNCTIONAL(m,f)          f additive and homogeneous
;;;   IS-BOUNDED-LINEAR-FUNCTIONAL(m,f)  + |f(x)| <= c*||x|| for some c >= 0
;;;   DUAL-NORM(m,f)                     the operator norm ||f|| = least such c
;;;                                      (IOTA least-upper-bound; well-defined
;;;                                      for bounded f -- decision A)
;;;
;;; Dependencies: normed-vector-space.scm (VEC, VADD, ACT, VNRM), abs.

;;; f : VEC(m) -> RR, additive and homogeneous over the real scalars.
(def-predicate 'IS-LINEAR-FUNCTIONAL '(m f)
  '(AND (IN f (FUN (VEC m) RR))
   (AND (FORALL x_ (IMPLIES (IN x_ (VEC m))
          (FORALL y_ (IMPLIES (IN y_ (VEC m))
            (= (f ((VADD m) x_ y_)) (+ (f x_) (f y_)))))))
        (FORALL r_ (IMPLIES (IN r_ RR)
          (FORALL x_ (IMPLIES (IN x_ (VEC m))
            (= (f ((ACT m) r_ x_)) (* r_ (f x_))))))))))

;;; bounded: |f(x)| <= c*||x|| for some nonnegative constant c.
(def-predicate 'IS-BOUNDED-LINEAR-FUNCTIONAL '(m f)
  '(AND (IS-LINEAR-FUNCTIONAL m f)
        (FORSOME c_ (AND (IN c_ RR)
                    (AND (<= 0 c_)
                         (FORALL x_ (IMPLIES (IN x_ (VEC m))
                           (<= (abs (f x_)) (* c_ ((VNRM m) x_))))))))))

;;; DUAL-NORM(m,f) = the operator norm ||f|| : the LEAST c >= 0 with
;;; |f(x)| <= c*||x|| for all x.  IOTA picks the unique such c (it exists and is
;;; unique exactly when f is bounded).  Equivalently sup{|f(x)| : ||x|| <= 1}.
(def-functoid 'DUAL-NORM '(m f)
  '(IOTA c_
     (AND (IN c_ RR)
      (AND (<= 0 c_)
       (AND (FORALL x_ (IMPLIES (IN x_ (VEC m))
              (<= (abs (f x_)) (* c_ ((VNRM m) x_)))))
            (FORALL d_ (IMPLIES (AND (IN d_ RR)
                                (AND (<= 0 d_)
                                     (FORALL x_ (IMPLIES (IN x_ (VEC m))
                                       (<= (abs (f x_)) (* d_ ((VNRM m) x_)))))))
                        (<= c_ d_))))))))

;;; ====================================================================
;;; Functionals on a SUBSPACE s (domain s, not all of VEC m).  The whole-space
;;; predicates above are the s = VEC(m) case; these carry an explicit subspace
;;; domain, as the Hahn-Banach extension machinery needs.  (s is a submodule;
;;; downstream uses supply IS-SUBMODULE(m, s).)
;;; ====================================================================

(def-predicate 'IS-LINEAR-FUNCTIONAL-ON '(m s f)
  '(AND (IN f (FUN s RR))
   (AND (FORALL x_ (IMPLIES (IN x_ s)
          (FORALL y_ (IMPLIES (IN y_ s)
            (= (f ((VADD m) x_ y_)) (+ (f x_) (f y_)))))))
        (FORALL r_ (IMPLIES (IN r_ RR)
          (FORALL x_ (IMPLIES (IN x_ s)
            (= (f ((ACT m) r_ x_)) (* r_ (f x_))))))))))

(def-predicate 'IS-BOUNDED-LINEAR-FUNCTIONAL-ON '(m s f)
  '(AND (IS-LINEAR-FUNCTIONAL-ON m s f)
        (FORSOME c_ (AND (IN c_ RR)
                    (AND (<= 0 c_)
                         (FORALL x_ (IMPLIES (IN x_ s)
                           (<= (abs (f x_)) (* c_ ((VNRM m) x_))))))))))

;;; DUAL-NORM-ON(m, s, f) = operator norm of f relative to the subspace s:
;;; the least c >= 0 with |f(x)| <= c*||x|| for all x in s (IOTA LUB).
(def-functoid 'DUAL-NORM-ON '(m s f)
  '(IOTA c_
     (AND (IN c_ RR)
      (AND (<= 0 c_)
       (AND (FORALL x_ (IMPLIES (IN x_ s)
              (<= (abs (f x_)) (* c_ ((VNRM m) x_)))))
            (FORALL d_ (IMPLIES (AND (IN d_ RR)
                                (AND (<= 0 d_)
                                     (FORALL x_ (IMPLIES (IN x_ s)
                                       (<= (abs (f x_)) (* d_ ((VNRM m) x_)))))))
                        (<= c_ d_))))))))

;;; g extends f from the subspace s: the two agree on s.
(def-predicate 'EXTENDS-ON '(s g f)
  '(FORALL x_ (IMPLIES (IN x_ s) (= (g x_) (f x_)))))

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'IS-LINEAR-FUNCTIONAL 'kind 'predicate 'arity 2
           'english "$2 is a linear functional on $1")
(notation! 'IS-LINEAR-FUNCTIONAL-ON 'kind 'predicate 'arity 3
           'english "$3 is a linear functional on the subspace $2 of $1")
(notation! 'IS-BOUNDED-LINEAR-FUNCTIONAL 'kind 'predicate 'arity 2
           'english "$2 is a bounded linear functional on $1")
(notation! 'IS-BOUNDED-LINEAR-FUNCTIONAL-ON 'kind 'predicate 'arity 3
           'english "$3 is a bounded linear functional on the subspace $2 of $1")
(notation! 'EXTENDS-ON 'kind 'predicate 'arity 3
           'english "$2 agrees with $3 on $1")
