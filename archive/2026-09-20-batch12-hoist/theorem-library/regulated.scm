;;; regulated.scm -- docs/calculus.pdf CHAPTER 4 SECTION 1: the vocabulary of
;;; Definitions 4.1 (regulated), 4.3 (step function, piecewise continuous), the
;;; one-sided limits (56)/(57) they are stated in terms of, the finite partition
;;; (58), and uniform convergence ON [a,b] -- which Proposition 4.5 is about.
;;;
;;; THREE DECISIONS, each a deviation from the notes and each deliberate.
;;;
;;; * The one-sided limits are RELATIONS, `IS-RIGHT-LIMIT(f,x,l)', not
;;;   partial-valued `f(x+)'.  Precedent: IS-DIFF-AT(f,th,v) carries the
;;;   derivative as an ARGUMENT rather than there being a partial DERIV that may
;;;   fail to denote.  The notes' endpoint convention -- f(b+) = f(b), f(a-) =
;;;   f(a) -- exists only to make those symbols denote, so it is NOT stated:
;;;   IS-REGULATED guards the right limit on `x < b' and the left on `a < x',
;;;   which is Remark 4.2's content without the device.
;;;
;;; * The finite sequence (58) is an NN-indexed family `p in FUN(INTERVAL(0,n),
;;;   RR)' -- INTERVAL is the tree's finite index set, the one MAT already uses.
;;;
;;; * IS-UNIF-LIMIT-ON is a head of its own because CONVERGES-UNIFORMLY
;;;   (metric-topology) is over a WHOLE metric space and there is no metric
;;;   subspace structure on CCINT(a,b); that is why antiderivable-uniform-limit
;;;   writes this shape out inline.
;;;
;;; Continuity is tested as IS-CONTINUOUS-AT(RR-MS, RR-MS, f, t) at the points
;;; of the piece, the convention the whole calculus arc uses.  On an OPEN piece
;;; that is not merely a convention: continuity of the restriction at an
;;; interior point and continuity on the line there coincide.

(def-predicate 'IS-RIGHT-LIMIT '(f x l)
  (conjuncts->and
    (list '(IN f (FUN RR RR))
          '(IN x RR)
          '(IN l RR)
          '(FORALL eps_
             (IMPLIES (POS-RR eps_)
               (FORSOME delta_
                 (AND (POS-RR delta_)
                      (FORALL t_
                        (IMPLIES (AND (IN t_ RR) (AND (< x t_) (<= t_ (+ x delta_))))
                                 (<= (ABS (- (f t_) l)) eps_))))))))))

(def-predicate 'IS-LEFT-LIMIT '(f x l)
  (conjuncts->and
    (list '(IN f (FUN RR RR))
          '(IN x RR)
          '(IN l RR)
          '(FORALL eps_
             (IMPLIES (POS-RR eps_)
               (FORSOME delta_
                 (AND (POS-RR delta_)
                      (FORALL t_
                        (IMPLIES (AND (IN t_ RR) (AND (<= (- x delta_) t_) (< t_ x)))
                                 (<= (ABS (- (f t_) l)) eps_)))))))))) 

;;; DEFINITION 4.1.
(def-predicate 'IS-REGULATED '(f a b)
  (conjuncts->and
    (list '(IN f (FUN RR RR))
          '(IN a RR)
          '(IN b RR)
          '(< a b)
          '(FORALL x_
             (IMPLIES (IN x_ (CCINT a b))
               (AND (IMPLIES (< x_ b) (FORSOME l_ (IS-RIGHT-LIMIT f x_ l_)))
                    (IMPLIES (< a x_) (FORSOME l_ (IS-LEFT-LIMIT f x_ l_)))))))))

;;; The finite increasing sequence (58), as an NN-indexed family over the
;;; tree's finite index set INTERVAL(0,n).
(def-predicate 'IS-PARTITION '(p n a b)
  (conjuncts->and
    (list '(IN n NN)
          '(<= 1 n)
          '(IN a RR)
          '(IN b RR)
          '(< a b)
          ;; TOTAL on NN, constrained only on 0..n.  Typing p by
          ;; `FUN(INTERVAL(0,n), RR)' looks tighter and makes the induction that
          ;; locates a point in the partition nearly unprovable: the step needs
          ;; the SAME family read as a partition with one piece fewer, and under
          ;; the tight typing that is a DIFFERENT function -- you must build the
          ;; restriction as a VNB-LAMBDA, discharge lam-t's two leaves, and
          ;; re-establish all four conjuncts for it.  Total on NN, the step is
          ;; literally the same `p' with `n' replaced by its predecessor.  The
          ;; conditions below say nothing outside 0..n, so the extra domain
          ;; carries no information; a finite sequence always extends.
          '(IN p (FUN NN RR))
          '(= (p 0) a)
          '(= (p n) b)
          '(FORALL i_ (FORALL j_
             (IMPLIES (AND (IN i_ (INTERVAL 0 n)) (AND (IN j_ (INTERVAL 0 n)) (< i_ j_)))
                      (< (p i_) (p j_))))))))

;;; DEFINITION 4.3, first half.
(def-predicate 'IS-STEP-FN '(f a b)
  (conjuncts->and
    (list '(IN f (FUN RR RR))
          '(IN a RR)
          '(IN b RR)
          '(< a b)
          '(FORSOME n_ (FORSOME p_
             (AND (IS-PARTITION p_ n_ a b)
                  (FORALL i_
                    (IMPLIES (AND (IN i_ (INTERVAL 0 n_)) (< i_ n_))
                      (FORSOME c_
                        (AND (IN c_ RR)
                             (FORALL t_
                               (IMPLIES (AND (IN t_ RR)
                                        (AND (< (p_ i_) t_) (< t_ (p_ (SUCC i_)))))
                                        (= (f t_) c_)))))))))))))

;;; DEFINITION 4.3, second half.
(def-predicate 'IS-PIECEWISE-CONTINUOUS '(f a b)
  (conjuncts->and
    (list '(IN f (FUN RR RR))
          '(IN a RR)
          '(IN b RR)
          '(< a b)
          '(FORSOME n_ (FORSOME p_
             (AND (IS-PARTITION p_ n_ a b)
                  (FORALL i_
                    (IMPLIES (AND (IN i_ (INTERVAL 0 n_)) (< i_ n_))
                      (FORALL t_
                        (IMPLIES (AND (IN t_ RR)
                                 (AND (< (p_ i_) t_) (< t_ (p_ (SUCC i_)))))
                                 (IS-CONTINUOUS-AT RR-MS RR-MS f t_)))))))))))

;;; Uniform convergence ON [a,b].  CONVERGES-UNIFORMLY (metric-topology) is
;;; over a whole metric space and there is no metric subspace on CCINT(a,b),
;;; which is why antiderivable-uniform-limit writes this shape out inline.
(def-predicate 'IS-UNIF-LIMIT-ON '(fam g a b)
  (conjuncts->and
    (list '(IN fam (FUN NN (FUN RR RR)))
          '(IN g (FUN RR RR))
          '(IN a RR)
          '(IN b RR)
          '(< a b)
          '(FORALL eps_
             (IMPLIES (POS-RR eps_)
               (FORSOME n_
                 (AND (IN n_ NN)
                      (FORALL k_
                        (IMPLIES (AND (IN k_ NN) (<= n_ k_))
                          (FORALL x_
                            (IMPLIES (IN x_ (CCINT a b))
                              (<= (ABS (- (g x_) ((fam k_) x_))) eps_)))))))))))) 

;;; English readings.  These matter beyond the documentation: the Focus
;;; workspace makes every head in a displayed sequent hover-sensitive, and a
;;; head with no `notation!' shows as "(no English reading declared)" -- so an
;;; undeclared reading is a hole the reader sees, not just a gap in a table.
(notation! 'IS-RIGHT-LIMIT 'kind 'predicate 'arity 3
           'english "$3 is the limit of $1 as the argument approaches $2 from the right")
(notation! 'IS-LEFT-LIMIT 'kind 'predicate 'arity 3
           'english "$3 is the limit of $1 as the argument approaches $2 from the left")
(notation! 'IS-REGULATED 'kind 'predicate 'arity 3
           'english "$1 is regulated on the interval [$2, $3] -- both one-sided limits exist at every point")
(notation! 'IS-PARTITION 'kind 'predicate 'arity 4
           'english "$1 is a partition of [$3, $4] into $2 pieces")
(notation! 'IS-STEP-FN 'kind 'predicate 'arity 3
           'english "$1 is a step function on [$2, $3]")
(notation! 'IS-PIECEWISE-CONTINUOUS 'kind 'predicate 'arity 3
           'english "$1 is piecewise continuous on [$2, $3]")
(notation! 'IS-UNIF-LIMIT-ON 'kind 'predicate 'arity 4
           'english "$2 is the uniform limit of the sequence $1 on [$3, $4]")
