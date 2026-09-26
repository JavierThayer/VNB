;;; heine-borel-interval.scm -- HEINE-BOREL for a closed interval AS A SPACE:
;;;
;;;     forall a, b in RR.   IS-COMPACT( SUBSPACE-MS(RR-MS, CCINT(a, b)) )
;;;
;;; the first use of the metric subspace (structure-library/metric-subspace.scm,
;;; theorem-library/metric-subspace-laws.scm).  Until the subspace existed this
;;; statement could not be WRITTEN: IS-COMPACT takes a metric space, and
;;; "the closed interval" was only a subclass of RR (the wall recorded in
;;; theorem-library/heine-borel-baby.scm and ascoli-arzela-statement.scm:148).
;;;
;;; THE ROUTE, and why it is three citations.
;;;   1. `rr-interval-seq-has-convergent-subseq' (rake-bolzano-weierstrass-2.scm)
;;;      hands a sequence in CCINT(a,b) a subsequence converging IN RR-MS to a
;;;      real pt.  It does NOT say pt lies in the interval.
;;;   2. `rr-limit-in-ccint' (proved first, below) puts it there: the limit of a
;;;      sequence inside [lo, hi] is inside [lo, hi].  Two applications of
;;;      `rr-limit-le' against the CONSTANT sequences (`rr-const-converges-to').
;;;      This is "a closed interval is closed" in the only form needed here.
;;;   3. `subspace-converges-to' (metric-subspace-laws.scm) moves the convergence
;;;      from RR-MS into the subspace -- legitimate exactly because the limit is
;;;      now known to be a point of the subspace.
;;;   Then SEQ-COMPACT is established and `seq-compact-implies-compact'
;;;   (rake-lebesgue-number.scm) finishes.
;;;
;;; THE EMPTY INTERVAL IS INCLUDED AND NEEDS NO GUARD.  When b < a, CCINT(a,b)
;;; is empty, SUBSPACE-MS(RR-MS, CCINT(a,b)) is the empty metric space, and the
;;; empty space is compact.  Nothing below assumes a <= b: the sequential
;;; argument is driven symbolically from a given f in FUN(NN, CCINT(a,b)), of
;;; which there are none when the interval is empty, so the universal it proves
;;; is vacuously true and every step still type-checks.  A guard `a <= b' would
;;; have been a false economy -- the Ascoli and calculus.pdf 2.23-2.29 consumers
;;; take the interval from a hypothesis and cannot always exhibit its order.
;;;
;;; WINDOW (scratchpad/window.py).  lo = 3201, forced by theorem-library/rake-series2
;;; (rr-const-converges-to); rake-bolzano-weierstrass-2 (2942), limit-arithmetic
;;; (2260, rr-limit-le), ccint-basics (2015) and rake-lebesgue-number (1382,
;;; seq-compact-implies-compact) are above it.  It must ALSO load after
;;; theorem-library/metric-subspace-laws, which window.py cannot see yet (those
;;; theorems are not in the band).  The slot is immediately after
;;; "theorem-library/rake-series2".  hi = none: nothing cites it yet.
;;;
;;; Helper prefix: hbi-.

(define (hbi-head g) (and (pair? g) (car g)))

;;; =====================================================================
;;; (1) THE LIMIT OF A SEQUENCE IN [lo, hi] LIES IN [lo, hi].
;;;
;;; `rr-limit-le' compares two convergent sequences termwise; run it against the
;;; constant sequence on each side.  The termwise premise is claimed in the
;;; UNREDUCED spelling `((VNB-LAMBDA nv_ NN lo_) n_) <= q_(n_)' -- the form
;;; `fact' will look for after instantiating at the lambda -- and reduced inside
;;; the lane by `lam-b', the argument being typed by the guard just peeled.
;;; =====================================================================
(define hbi-lo-const '(VNB-LAMBDA nv_ NN lo_))
(define hbi-hi-const '(VNB-LAMBDA nv_ NN hi_))

;;; (IN <constant sequence> (FUN NN RR)) for the real c.
(define (hbi-const-fun! cfun c)
  (have! (list 'IN cfun '(FUN NN RR))
    (lambda ()
      (for-each (lambda (k)
                  (dk-focus! k)
                  (if (eq? (hbi-head (dk-goal)) 'FORALL)
                      (begin (di) (ass))
                      (begin (fact 'nn-is-set) (ass))))
                (dk-opened (lambda () (lam-t)))))))

(sp (make-wff '(FORALL lo_ (IMPLIES (IN lo_ RR)
     (FORALL hi_ (IMPLIES (IN hi_ RR)
       (FORALL q_ (IMPLIES (IN q_ (FUN NN (CCINT lo_ hi_)))
         (FORALL pt_ (IMPLIES (IN pt_ RR)
           (IMPLIES (CONVERGES-TO RR-MS q_ pt_)
                    (IN pt_ (CCINT lo_ hi_)))))))))))))
(dk-peel!)
(fact 'ccint-subset-rr 'lo_ 'hi_)
(fact 'fun-codomain-superset 'q_ 'NN '(CCINT lo_ hi_) 'RR)
(hbi-const-fun! hbi-lo-const 'lo_)
(hbi-const-fun! hbi-hi-const 'hi_)
(fact 'rr-const-converges-to 'lo_)
(fact 'rr-const-converges-to 'hi_)

;; lo_ <= pt_
(have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
         (list '<= (list hbi-lo-const 'n_) '(q_ n_))))
  (lambda ()
    (di)
    (lam-b)
    (fact 'fun-apply-type-c 'q_ 'NN '(CCINT lo_ hi_) 'n_)
    (fact 'ccint-parts 'lo_ 'hi_ '(q_ n_))
    (dk-split-all!)
    (ass)))
(fact 'rr-limit-le hbi-lo-const 'q_ 'lo_ 'pt_)

;; pt_ <= hi_
(have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
         (list '<= '(q_ n_) (list hbi-hi-const 'n_))))
  (lambda ()
    (di)
    (lam-b)
    (fact 'fun-apply-type-c 'q_ 'NN '(CCINT lo_ hi_) 'n_)
    (fact 'ccint-parts 'lo_ 'hi_ '(q_ n_))
    (dk-split-all!)
    (ass)))
(fact 'rr-limit-le 'q_ hbi-hi-const 'pt_ 'hi_)

(mac 'ccint-membership)
(dk-conj-close! (lambda () (ass)))
(qed 'rr-limit-in-ccint)
(topic! 'rr-limit-in-ccint 'analysis)
(alias! 'rr-limit-in-ccint "the limit of a sequence in a closed interval stays in it")

;;; =====================================================================
;;; (2) HEINE-BOREL.  The closed interval, as a metric space, is compact.
;;; =====================================================================
(define hbi-ms '(SUBSPACE-MS RR-MS (CCINT av_ bv_)))
(define hbi-int '(CCINT av_ bv_))

(sp (make-wff (list 'FORALL 'av_ (list 'IMPLIES '(IN av_ RR)
     (list 'FORALL 'bv_ (list 'IMPLIES '(IN bv_ RR)
       (list 'IS-COMPACT hbi-ms)))))))
(dk-peel!)
(fact 'rr-is-metric-space)
(have! (list 'SUBSET hbi-int '(PTS RR-MS))
  (lambda () (slot 'PTS) (fact 'ccint-subset-rr 'av_ 'bv_) (ass)))
(fact 'subspace-is-metric-space 'RR-MS hbi-int)

(have! (list 'SEQ-COMPACT hbi-ms)
  (lambda ()
    (mac 'SEQ-COMPACT)
    (mac 'subspace-pts)                    ; PTS(SUBSPACE-MS(RR-MS, [a,b])) -> [a,b]
    (dk-conj-close!
     (lambda ()
       (if (eq? (hbi-head (dk-goal)) 'IS-METRIC-SPACE)
           (ass)
           (begin
             (di)                           ; f, with (IN f (FUN NN [a,b]))
             (let* ((ex1 (dk-fact! 'rr-interval-seq-has-convergent-subseq
                                   'av_ 'bv_ 'f))
                    (phi (dk-skolem! ex1))
                    (ex2 (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORSOME)))
                                  "the limit existential"))
                    (pt  (dk-skolem! ex2))
                    (sq  (list 'SUBSEQ 'f phi)))
               ;; the subsequence is a sequence IN the interval
               (have! (list 'AND (list 'IN 'f (list 'FUN 'NN (list 'PTS hbi-ms)))
                                 (list 'STRICTLY-MONO-NN phi))
                 (lambda () (mac 'subspace-pts) (dk-conj-close! (lambda () (ass)))))
               (fact 'subseq-is-fun hbi-ms 'f phi)
               (mac-h 'subspace-pts (list 'IN sq (list 'FUN 'NN (list 'PTS hbi-ms))))
               ;; ... and its limit lies in the interval
               (fact 'rr-limit-in-ccint 'av_ 'bv_ sq pt)
               (ew phi)
               (dk-conj-close!
                (lambda ()
                  (if (eq? (hbi-head (dk-goal)) 'STRICTLY-MONO-NN)
                      (ass)
                      (begin
                        (ew pt)
                        (dk-conj-close!
                         (lambda ()
                           (if (eq? (hbi-head (dk-goal)) 'IN)
                               (ass)
                               (begin
                                 (fact 'subspace-converges-to 'RR-MS hbi-int sq pt)
                                 (prop))))))))))))))))
(fact 'seq-compact-implies-compact hbi-ms)
(ass)
(qed 'heine-borel-ccint)
(topic! 'heine-borel-ccint 'topology)
(alias! 'heine-borel-ccint
        "a closed bounded interval is compact as a metric space"
        "Heine-Borel: the subspace of RR on [a,b] is compact")
