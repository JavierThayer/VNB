;;; metric-completeness.scm -- Cauchy sequences, convergence, completeness
;;; on a generic METRIC-SPACE.
;;;
;;; Generic replacements for the magnitude-hard-coded cc-complete idiom:
;;;
;;;   IS-CAUCHY-SEQ(s, f)   f : NN -> X(s) is Cauchy in metric space s
;;;   CONVERGES-TO(s, f, L) f converges to L in s
;;;   CONVERGES(s, f)       f converges to some limit in s
;;;   IS-COMPLETE(s)        s is a metric space in which every Cauchy
;;;                         sequence converges
;;;
;;; A sequence is a function f : NN -> X(s); distances ((D s) (f m) (f n_))
;;; land in RR, so the eps-estimates use the numeric order <= and the
;;; POS-RR ("eps > 0") predicate from order-predicates.scm.
;;;
;;; Bound-variable names follow cc-complete: N is the threshold, m and n_
;;; are the running indices.  `n_' (not `n') because the VNB reader and MIT
;;; Scheme both case-fold, so `N' and `n' would be the same identifier --
;;; see [[feedback-mit-case-fold]], [[feedback-no-case-variant-binders]].
;;;
;;; Dependencies: metric-space.scm (IS-METRIC-SPACE, D, X), number-systems.scm
;;; (NN, RR, <=), order-predicates.scm (POS-RR).  Loaded after order-predicates
;;; and before complex.scm so cc-complete can be stated as IS-COMPLETE(CC-MS).

;;; -----------------------------------------------------------------------
;;; IS-CAUCHY-SEQ(s, f): f : NN -> X(s) is a Cauchy sequence in s.

(def-predicate 'IS-CAUCHY-SEQ '(s f)
  '(AND (IS-METRIC-SPACE s)
   (AND (IN f (FUN NN (X s)))
        (FORALL eps (IMPLIES (POS-RR eps)
          (FORSOME N (AND (IN N NN)
            (FORALL m (IMPLIES (IN m NN)
              (FORALL n_ (IMPLIES (IN n_ NN)
                (IMPLIES (AND (<= N m) (<= N n_))
                  (<= ((D s) (f m) (f n_)) eps)))))))))))))

;;; -----------------------------------------------------------------------
;;; CONVERGES-TO(s, f, L): the sequence f converges to the point L in s.

(def-predicate 'CONVERGES-TO '(s f L)
  '(AND (IS-METRIC-SPACE s)
   (AND (IN f (FUN NN (X s)))
   (AND (IN L (X s))
        (FORALL eps (IMPLIES (POS-RR eps)
          (FORSOME N (AND (IN N NN)
            (FORALL n_ (IMPLIES (IN n_ NN)
              (IMPLIES (<= N n_)
                (<= ((D s) (f n_) L) eps))))))))))))

;;; -----------------------------------------------------------------------
;;; CONVERGES(s, f): f converges to some limit in s.

(def-predicate 'CONVERGES '(s f)
  '(FORSOME L (CONVERGES-TO s f L)))

;;; -----------------------------------------------------------------------
;;; IS-COMPLETE(s): s is a metric space in which every Cauchy sequence
;;; converges.  IS-CAUCHY-SEQ already carries IS-METRIC-SPACE(s) and the
;;; typing of f, so the implication is clean.

(def-predicate 'IS-COMPLETE '(s)
  '(AND (IS-METRIC-SPACE s)
        (FORALL f (IMPLIES (IS-CAUCHY-SEQ s f)
                           (CONVERGES s f)))))

;;; -----------------------------------------------------------------------
;;; complete-cauchy-converges: the forward, backchain-ready form of
;;; completeness -- in a complete space, a Cauchy sequence converges.
;;; (The IS-COMPLETE definition is an IFF; this support entry is the
;;; directly-usable conjunct, so downstream proofs can backchain on it
;;; without unfolding the definition in an assumption -- VNB macetes
;;; rewrite goals, not hypotheses; see [[reference-vnb-proof-mechanics]].)
;;; Trivially derivable: it is the second conjunct of the unfolded
;;; IS-COMPLETE.  Library-build phase: installed as support
;;; [[feedback-library-axioms-fine]].

(support 'complete-cauchy-converges
  '(FORALL s
     (IMPLIES (IS-COMPLETE s)
       (FORALL f (IMPLIES (IS-CAUCHY-SEQ s f)
                          (CONVERGES s f))))))

;;; -----------------------------------------------------------------------
;;; cauchy-rapid-subsequence: every Cauchy sequence has a "rapidly Cauchy"
;;; subsequence -- one whose consecutive distances are bounded by ANY
;;; prescribed positive real sequence a (in particular a(k) = 2^-k).  The
;;; subsequence is a strictly increasing reindexing phi : NN -> NN; the
;;; subsequence itself is k |-> f(phi k).
;;;
;;; This is the bridge from Cauchy to summable: sum_k d(y_k, y_{k+1}) is then
;;; dominated by sum_k a(k), so picking a summable a makes the subsequence's
;;; consecutive-distance series converge.  Coupled with series summation and
;;; diagonalization it gives the completeness of a completion (and the general
;;; "Cauchy with a convergent subsequence => convergent" lemma).  Recorded in
;;; the PSS for that future use; standard, no proof attempted
;;; [[feedback-pss-over-proof-slog]] [[project-metric-completion]].
;;;
;;; Proof sketch (NN-recursion + choice): a(k) > 0, so Cauchyness gives N_k with
;;; d(f m, f n) <= a(k) for all m,n >= N_k.  Define phi(0) := N_0,
;;; phi(succ k) := max(succ(phi k), N_{succ k}); strictly increasing, and
;;; phi(k), phi(succ k) >= N_k, so d(f(phi k), f(phi(succ k))) <= a(k).
(support 'cauchy-rapid-subsequence
  '(FORALL s (FORALL f (FORALL a
     (IMPLIES (AND (IS-CAUCHY-SEQ s f)
              (AND (IN a (FUN NN RR))
                   (FORALL k (IMPLIES (IN k NN) (POS-RR (a k))))))
       (FORSOME phi
         (AND (IN phi (FUN NN NN))
         (AND (FORALL m (IMPLIES (IN m NN)
                (FORALL n_ (IMPLIES (IN n_ NN)
                  (IMPLIES (< m n_) (< (phi m) (phi n_)))))))
              (FORALL k (IMPLIES (IN k NN)
                (<= ((D s) (f (phi k)) (f (phi (succ k)))) (a k))))))))))))
(warrant! 'cauchy-rapid-subsequence 'well-known
  "Standard subsequence extraction.  For each k, a(k) > 0 and f Cauchy give an
   N_k with d(f m, f n) <= a(k) whenever m,n >= N_k (IS-CAUCHY-SEQ at eps=a(k)).
   Build phi by NN-recursion: phi(0)=N_0, phi(succ k)=max(succ(phi k),N_{succ k})
   -- strictly increasing, with phi(k) and phi(succ k) both >= N_k, so the
   consecutive distance is <= a(k).  Choice picks the N_k.  a(k)=2^-k is the
   usual instance, making sum_k d-consecutive dominated by the geometric series.")
