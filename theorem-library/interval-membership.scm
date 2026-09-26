;;; interval-membership.scm -- INTERVAL's membership IFF and the [1,1] instance,
;;; both PROVEN, both by citation of the read-offs already in the tree.
;;;
;;; INTERVAL(a,b) is the def-functoid  { i in NN : a <= i and i <= b }
;;; (structure-library/matrix.scm).  Its two directions are already mechanised:
;;;
;;;   forward (elimination)   interval-elt-in-nn / interval-lo / interval-hi
;;;                           -- theorem-library/interval-basics.scm, by the
;;;                           citable unfolding equation plus sep-me;
;;;   backward (introduction) interval-mem-intro
;;;                           -- theorem-library/interval-mem-intro.scm, by
;;;                           `mac' of the functoid plus sep-mi.
;;;
;;; So neither theorem here needs to touch SEP at all.  The IFF is the two
;;; halves of `di' handed the four citations; `one-in-interval-1' is
;;; interval-mem-intro at a = b = i = 1, with nn-one-in and nn-le-refl
;;; supplying its three antecedents.  Re-deriving the separation read-offs here
;;; would have been a second copy of interval-basics.scm's driver.
;;;
;;; RETIRES
;;;   interval-membership  -- structure-library/matrix.scm:80 (warrant :83)
;;;   one-in-interval-1    -- structure-library/order-lemmas.scm:333 (warrant :334)
;;;
;;; WINDOW.  lo = theorem-library/nn-order-basics (nn-le-refl); the other
;;; citations -- nn-one-in (nn-order-ord), interval-mem-intro, interval-basics
;;; -- all load before it.  hi = theorem-library/matact-row-linear-proof, the
;;; earliest citer of one-in-interval-1 (interval-membership's earliest citer,
;;; theorem-library/partition-locates-point, is much later).
;;;
;;; Helper prefix: im-.

;;; Focus the unique OPEN leaf whose goal has head H.  The two branches of an
;;; iff-intro are told apart by their goal head -- AND on the elimination side,
;;; IN on the introduction side -- and nothing else distinguishes them, the
;;; contexts being each other's goals.  Errors on a miss: a focus helper that
;;; returns #f and leaves focus put hides every later step.
(define (im-focus-goal-head! h)
  (let ((hit (any-pred
              (lambda (l)
                (and (not (sequent-node-grounded? l))
                     (let ((g (wff-formula (sequent-node-assertion l))))
                       (and (pair? g) (eq? (car g) h)))))
              (proof-leaves))))
    (if (not hit) (error "im-focus-goal-head!: no open leaf with goal head" h))
    (dk-focus! hit)))

;;; ---- the membership characterisation ---------------------------------
(sp (make-wff '(FORALL a (FORALL b (FORALL i
   (IFF (IN i (INTERVAL a b)) (AND (IN i NN) (AND (<= a i) (<= i b)))))))))
(di)                       ; peel the three universals; the body is an IFF,
                           ; which `di' does not take in the same call
(di)                       ; iff-intro: two leaves, one per direction

;; ->  i in INTERVAL(a,b) gives the NN typing and the two bounds.
(im-focus-goal-head! 'AND)
(fact 'interval-elt-in-nn 'a 'b 'i)
(fact 'interval-lo 'a 'b 'i)
(fact 'interval-hi 'a 'b 'i)
(from-context!)            ; splits the nested AND and `ass'es each conjunct

;; <-  the NN typing and the two bounds put i back in INTERVAL(a,b).
(im-focus-goal-head! 'IN)
(dk-split! '(AND (IN i NN) (AND (<= a i) (<= i b))))
(fact 'interval-mem-intro 'a 'b 'i)
(ass)
(qed 'interval-membership)
(topic! 'interval-membership 'plumbing)

;;; ---- the column index of a column vector ------------------------------
;;; 1 in [1,1].  Three antecedents, all ground: 1 in NN (nn-one-in) and
;;; 1 <= 1 twice (nn-le-refl at 1, whose own guard is the same nn-one-in).
(sp (make-wff '(IN 1 (INTERVAL 1 1))))
(fact 'nn-one-in)
(fact 'nn-le-refl 1)
(fact 'interval-mem-intro 1 1 1)
(ass)
(qed 'one-in-interval-1)
(topic! 'one-in-interval-1 'plumbing)
