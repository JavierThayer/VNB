;;; theorem-library/subsequence-capture.scm
;;;
;;; The Subsequence Capture lemma + a chosen enumeration NN-ENUM.
;;;
;;; subsequence-capture (PSS):
;;;   For S in INF-SUBSETS(NN), there exists a strictly monotone
;;;   f : NN -> S.
;;;
;;; NN-ENUM(S) (functoid):
;;;   CHOICE of such an f.  Skolem-function for subsequence-capture;
;;;   well-defined iff S is in INF-SUBSETS(NN).
;;;
;;; nn-enum-spec (PSS):
;;;   When S is in INF-SUBSETS(NN), NN-ENUM(S) is in FUN(NN, S) and
;;;   is strictly monotone.
;;;
;;; Standard proofs: subsequence-capture by NN-recursion with
;;; f(0) := MIN-NN(S), f(succ n) := MIN-NN { x in S : f n < x }, using
;;; well-foundedness of NN and unboundedness of infinite S.
;;; nn-enum-spec follows from subsequence-capture + choice-axiom in one
;;; shot.  Both accepted here without mechanical proof while the
;;; library is being built out.

;;; subsequence-capture RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-subseq-leaves.scm

;;; NN-ENUM(S) -- chosen strictly monotone enumeration of S.
;;; The CHOICE is well-defined exactly when the SEP class is non-empty,
;;; which by subsequence-capture is exactly when S in INF-SUBSETS(NN).
(def-functoid 'NN-ENUM '(S)
  '(CHOICE (SEP f (FUN NN S)
             (FORALL m
               (IMPLIES (IN m NN)
                 (FORALL n
                   (IMPLIES (IN n NN)
                     (IMPLIES (< m n) (< (f m) (f n))))))))))

(support 'nn-enum-spec
  '(FORALL S
     (IMPLIES (IN S (INF-SUBSETS NN))
       (AND (IN (NN-ENUM S) (FUN NN S))
            (FORALL m
              (IMPLIES (IN m NN)
                (FORALL n
                  (IMPLIES (IN n NN)
                    (IMPLIES (< m n)
                             (< ((NN-ENUM S) m)
                                ((NN-ENUM S) n)))))))))))


(warrant! 'nn-enum-spec 'well-known
  "NN-ENUM(S) is CHOICE over the SEP of strictly monotone f in FUN(NN,S), so the
   specification is subsequence-capture (same file, which makes the SEP
   non-empty) plus the CHOICE axiom of the base theory in one step.  Never
   mechanised; no script in archive/proven-theorems-archive.scm.")
