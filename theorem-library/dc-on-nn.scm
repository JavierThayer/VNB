;;; theorem-library/dc-on-nn.scm
;;;
;;; Dependent recursion / dependent choice on NN, as a Proof Support Set
;;; entry.
;;;
;;; Schema:
;;;
;;;   Given a set X, an element a in X, and a set R (intended as a
;;;   subset of NN x X x X) such that
;;;
;;;     forall k in NN. forall x in X. exists y in X. (LIST k x y) in R,
;;;
;;;   there exists f : NN -> X with f(0) = a and, for every k in NN,
;;;
;;;     (LIST k (f k) (f (succ k))) in R.
;;;
;;; Triples are encoded as (LIST k x y) per the n-ary apply-tupling
;;; convention installed in theorem-library/axioms.scm.
;;;
;;; This is the inside-a-proof companion to def-by-nn-recursion: the
;;; latter is a top-level definition macro that installs a named
;;; operator from a closed-form successor expression, while dc-on-nn
;;; produces a sequence inside a proof from a witness relation.
;;;
;;; Derivable in VNB from primitive recursion on NN + Hilbert epsilon:
;;; choose g(k, x) := CHOICE { y in X : (LIST k x y) in R } using
;;; global choice, then recurse f(0) := a, f(succ k) := g(k, f k).
;;; Accepted here without mechanical proof during the library-building
;;; phase.
;;;
;;; Typical use: extracting a sequence of nested infinite subsets of NN
;;; (S_0 supset S_1 supset ...) for the diagonalization argument; more
;;; generally, any "build a sequence by repeated choices" construction.

(support 'dc-on-nn
  '(FORALL X
     (IMPLIES (IN X SET)
       (FORALL a
         (IMPLIES (IN a X)
           (FORALL R
             (IMPLIES (IN R SET)
               (IMPLIES
                 (FORALL k
                   (IMPLIES (IN k NN)
                     (FORALL u
                       (IMPLIES (IN u X)
                         (FORSOME y
                           (AND (IN y X)
                                (IN (LIST k u y) R)))))))
                 (FORSOME f
                   (AND (IN f (FUN NN X))
                        (AND (= (f 0) a)
                             (FORALL k
                               (IMPLIES (IN k NN)
                                 (IN (LIST k (f k) (f (succ k))) R))))))))))))))

;;; ====================================================================
;;; dc-on-nn-pred -- dependent recursion on NN with a SET-VALUED STEP.
;;;
;;; Same principle as dc-on-nn, but the step is presented as a map
;;;   nxt : (k, u)  |->  the SET of allowed successors of u at stage k
;;; (an ordinary VNB-LAMBDA), instead of as a SET R of encoded triples.
;;; Totality is "nxt(k,u) meets X" and the conclusion is the direct
;;; membership  f(succ k) in nxt(k, f k)  -- no (LIST k u y) encoding and
;;; no NTH projection at the call site.
;;;
;;;   Given X in SET, a in X, and nxt with
;;;     forall k in NN. forall u in X. exists y in X. y in nxt(k,u),
;;;   there is f : NN -> X with f(0)=a and, for every k in NN,
;;;     f(succ k) in nxt(k, f k).
;;;
;;; This is the predicate-stepped recursion that block-family-rederive.scm
;;; recommends to kill its O1: the relation-as-a-set plumbing (build R by
;;; comprehension, prove R in SET, prove the (LIST k u y) in R <-> P bridge)
;;; is exactly what the set-valued step removes -- the caller writes
;;; nxt := VNB-LAMBDA((k,u), <successor set>) and reads membership off
;;; directly.  No new strength over dc-on-nn: derivable, like dc-on-nn, from
;;; primitive recursion on NN + global Hilbert choice
;;;   g(k,u) := CHOICE { y in X : y in nxt(k,u) }   (defined by totality),
;;;   f(0) := a,  f(succ k) := g(k, f k);
;;; equivalently it IS dc-on-nn at R := { (LIST k u y) : y in nxt(k,u) }
;;; with the encoding done once here rather than at every call.
(support 'dc-on-nn-pred
  '(FORALL X
     (IMPLIES (IN X SET)
       (FORALL a
         (IMPLIES (IN a X)
           (FORALL nxt
             (IMPLIES
               (FORALL k
                 (IMPLIES (IN k NN)
                   (FORALL u
                     (IMPLIES (IN u X)
                       (FORSOME y
                         (AND (IN y X)
                              (IN y (nxt k u))))))))
               (FORSOME f
                 (AND (IN f (FUN NN X))
                      (AND (= (f 0) a)
                           (FORALL k
                             (IMPLIES (IN k NN)
                               (IN (f (succ k)) (nxt k (f k)))))))))))))))
(warrant! 'dc-on-nn-pred 'reference
  "Set-valued-step form of dc-on-nn (same file).  Derivable from primitive
   recursion on NN + global Hilbert choice: g(k,u):=CHOICE{y in X:y in nxt
   (k,u)} is defined by the totality hypothesis, then recurse f(0):=a,
   f(succ k):=g(k,f k); f:NN->X by induction.  No relation-set encoding --
   nxt(k,u) is the successor SET, supplied as a VNB-LAMBDA, so callers avoid
   the (LIST k u y)-in-R comprehension/sethood/NTH plumbing (O1 of
   archive/calculus-pre-rename/block-family-rederive.scm).  Accepted asserted during library-build.")
