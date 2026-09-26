;;; interval-calculus-laws.scm -- the laws of the vocabulary of
;;; structure-library/interval-calculus.scm: OOINT, IS-CONTINUOUS-ON,
;;; HAS-DERIV-AT and EXTEND-CONST.  Everything here is PROVEN; the definition
;;; file asserts nothing.
;;;
;;; STAGE 1: the open interval; the read-offs, the locality and the uniqueness
;;; of HAS-DERIV-AT; the equivalence with IS-DIFF-AT for a function on all of
;;; RR; the differentiation rules transported.
;;; STAGE 2: the extension lemma of docs/real-calculus-statements.tex, s.5.
;;;
;;; Helper prefix: ic-.
;;;
;;; Dependencies: structure-library/interval-calculus.scm; extreme-value.scm
;;; (CCINT) and theorem-library/ccint-basics.scm; metric-subspace.scm and
;;; theorem-library/metric-subspace-laws.scm; structure-library/diff-on.scm and
;;; theorem-library/diff-on-laws.scm (the bridge `diff-at-iff-diff-on', the
;;; `ms-agree-*' transports, the `rr-nf-*' slot read-offs), diff-on-laws-2.scm
;;; (diff-on-unique, diff-on-sum, diff-on-product), holomorphic-basics-2.scm
;;; (diff-on-transfer-ptwise-eq), theorem-library/diff-at-local.scm
;;; (diff-at-local) and continuity-local.scm (continuous-at-local).

;;; ---- file-local driver helpers ---------------------------------------

(define (ic-head g) (and (pair? g) (car g)))

;;; The membership of an open interval, landed as its three conjuncts.
(define (ic-ooint-in! y a b)
  (dk-split-all! (dk-landed* (lambda ()
    (mac-h 'ooint-membership (list 'IN y (list 'OOINT a b)))))))

;;; Close an AND goal conjunct by conjunct: `ass' when the conjunct is in the
;;; context, otherwise `ineq' with PREMS named by formula (CLAUDE.md: bare
;;; (ineq) passes ZERO premises).

;;; forall dfu_ in P. forall dfv_ in P. BODY -- the INTERLEAVED spelling, which
;;; is what `forall-guarded' with a list of variables does NOT build (it puts
;;; both FORALLs first and then both guards).  `fact' detaches an antecedent
;;; only when the context holds it VERBATIM, so a two-variable guarded
;;; universal that is going to be detached has to be spelled this way.
(define (ic-fa2 p1 p2 body)
  (list 'FORALL 'dfu_ (list 'IMPLIES (list 'IN 'dfu_ p1)
        (list 'FORALL 'dfv_ (list 'IMPLIES (list 'IN 'dfv_ p2) body)))))

(define (ic-absplit! f)
  (let* ((nw (dk-landed* (lambda () (mac-h 'rr-abs-bound f))))
         (a  (car (filter (dk-head? 'AND) nw))))
    (filter (lambda (g) (and (pair? g) (memq (car g) '(< <=))))
            (dk-landed* (lambda () (dk-split! a))))))

(define (ic-conj-ineq! prems)
  (dk-conj-close!
   (lambda ()
     (if (dk-ctx-form (dk-goal))
         (ass)
         (apply dk-ineq! prems)))))

;;; =====================================================================
;;; (1) THE OPEN INTERVAL.
;;;
;;; STATEMENT CHECK.  OOINT(a, b) is a SEP over RR, so it is EMPTY whenever
;;; b <= a -- deliberately, and nothing below carries an `a < b' guard for that
;;; reason.  `ooint-subset-ccint' and `ooint-open' DO carry (IN a RR) and
;;; (IN b RR): off the reals the order relations `<' and `<=' are not tied to
;;; each other by anything, so `a < x implies a <= x' is not available there,
;;; and the arithmetic of the radius is not either.  Every consumer has real
;;; endpoints (HAS-DERIV-AT's are a - eps and a + eps).
;;; =====================================================================

;;; ooint-membership: x in OOINT(a,b) iff x in RR and a < x and x < b.
;;; Separation and nothing else, as `ccint-membership' is for CCINT.
(sp (make-wff '(FORALL a (FORALL b (FORALL icy_
   (IFF (IN icy_ (OOINT a b))
        (AND (IN icy_ RR) (AND (< a icy_) (< icy_ b)))))))))
(dk-peel!)
(mac 'OOINT)
(for-each
 (lambda (k)
   (dk-focus! k)
   (if (eq? (ic-head (dk-goal)) 'AND)
       (begin (sep-me (dk-pick (lambda (f)
                                 (and (pair? f) (eq? (car f) 'IN)
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'SEP)))
                               "the separation membership"))
              (dk-split-all!)
              (from-context!))
       (begin (dk-split-all!)
              (for-each (lambda (j) (dk-focus! j) (from-context!))
                        (dk-opened (lambda () (sep-mi)))))))
 (dk-opened (lambda () (di))))
(qed 'ooint-membership)
(topic! 'ooint-membership 'topology)
(alias! 'ooint-membership "membership in an open interval")

;;; ooint-elt-in-rr: a point of an open interval is a real.
(sp (make-wff '(FORALL a (FORALL b (FORALL icy_
   (IMPLIES (IN icy_ (OOINT a b)) (IN icy_ RR)))))))
(dk-peel!)
(ic-ooint-in! 'icy_ 'a 'b)
(ass)
(qed 'ooint-elt-in-rr)
(topic! 'ooint-elt-in-rr 'topology)

;;; ooint-subset-rr: an open interval is a class of reals.
(sp (make-wff '(FORALL a (FORALL b (SUBSET (OOINT a b) RR)))))
(dk-peel!)
(let ((z (subset-by-element!)))
  (fact 'ooint-elt-in-rr 'a 'b z)
  (ass))
(qed 'ooint-subset-rr)
(topic! 'ooint-subset-rr 'topology)

;;; ooint-subset-ccint: (a,b) is contained in [a,b].
(sp (make-wff (forall-guarded '(a b) '((IN a RR) (IN b RR))
   '(SUBSET (OOINT a b) (CCINT a b)))))
(dk-peel!)
(let ((z (subset-by-element!)))
  (ic-ooint-in! z 'a 'b)
  (mac 'ccint-membership)
  (ic-conj-ineq! (list '(IN a RR) '(IN b RR) (list 'IN z 'RR)
                       (list '< 'a z) (list '< z 'b))))
(qed 'ooint-subset-ccint)
(topic! 'ooint-subset-ccint 'topology)
(alias! 'ooint-subset-ccint "the open interval lies in the closed one")

;;; ooint-center: the centre of a symmetric open interval lies in it.
(sp (make-wff (forall-guarded '(icy_ ice_) '((IN icy_ RR) (POS-RR ice_))
   '(IN icy_ (OOINT (- icy_ ice_) (+ icy_ ice_))))))
(dk-peel!)
(fact 'rr-pos-rr-in-rr 'ice_)
(fact 'rr-lt-of-pos-rr 'ice_)
(mac 'ooint-membership)
(ic-conj-ineq! (list '(IN icy_ RR) '(IN ice_ RR) '(< 0 ice_)))
(qed 'ooint-center)
(topic! 'ooint-center 'topology)

;;; ooint-open: an open interval is open in RR-MS.  At y the radius is half of
;;; a common lower bound of y - a and b - y (`rr-min-pos' then `dk-halve!'):
;;; halving is what makes the bound STRICT, and a ball of radius exactly
;;; min(y - a, b - y) would need the ball's `not(dist = r)' conjunct instead.
(sp (make-wff (forall-guarded '(a b) '((IN a RR) (IN b RR))
   '(IS-OPEN RR-MS (OOINT a b)))))
(dk-peel!)
(fact 'rr-is-metric-space)
(mac 'IS-OPEN)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (ic-head g) 'IS-METRIC-SPACE) (ass))
       ((eq? (ic-head g) 'SUBSET) (slot 'PTS) (fact 'ooint-subset-rr 'a 'b) (ass))
       (#t
        (let ((y (dk-di-var!)))
          (ic-ooint-in! y 'a 'b)
          (fact 'rr-sub-in-rr y 'a)
          (fact 'rr-sub-in-rr 'b y)
          (dk-have! (list '< 0 (list '- y 'a))
            (lambda () (dk-ineq! '(IN a RR) (list 'IN y 'RR) (list '< 'a y))))
          (dk-have! (list '< 0 (list '- 'b y))
            (lambda () (dk-ineq! '(IN b RR) (list 'IN y 'RR) (list '< y 'b))))
          (let* ((ex (dk-fact! 'rr-min-pos (list '- y 'a) (list '- 'b y)))
                 (w  (dk-skolem! ex)))
            (dk-split-all!)
            (fact 'rr-pos-rr-of-lt w)
            (let ((d (dk-halve! w)))
              (ew d)
              (dk-conj-close!
               (lambda ()
                 (if (eq? (ic-head (dk-goal)) 'POS-RR)
                     (ass)
                     (let ((z (subset-by-element!)))
                       (dk-split-all!
                        (dk-landed* (lambda ()
                          (mac-h 'ball-membership
                                 (list 'IN z (list 'BALL 'RR-MS y d))))))
                       (slot-h 'PTS (list 'IN z '(PTS RR-MS)))
                       (dk-have! (list '<= (list 'abs (list '- y z)) d)
                         (lambda ()
                           (fact 'rr-ms-dist y z)
                           (subst (list '== (list 'abs (list '- y z))
                                        (list '(DIST RR-MS) y z)))
                           (ass)))
                       (fact 'rr-sub-in-rr y z)
                       (let ((bnds (ic-absplit! (list '<= (list 'abs (list '- y z)) d))))
                         (mac 'ooint-membership)
                         (ic-conj-ineq!
                          (append
                           (list '(IN a RR) '(IN b RR) (list 'IN y 'RR) (list 'IN z 'RR)
                                 (list 'IN d 'RR) (list 'IN w 'RR)
                                 (list '= (list '+ d d) w)
                                 (list '< 0 d)
                                 (list '<= w (list '- y 'a))
                                 (list '<= w (list '- 'b y)))
                           bnds)))))))))))))))
(qed 'ooint-open)
(topic! 'ooint-open 'topology)
(alias! 'ooint-open "an open interval is an open set of the real line")

;;; ooint-open-nf: the same, in the metric space IS-DIFF-ON speaks of.
;;; `ms-agree-open' with the two spaces of `diff-on-laws.scm' section 6.
(sp (make-wff (forall-guarded '(a b) '((IN a RR) (IN b RR))
   '(IS-OPEN (NF-METRIC-SPACE RR-NORMED-FIELD) (OOINT a b)))))
(dk-peel!)
(fact 'nf-rr-is-metric-space)
(fact 'nf-rr-agree-pts)
(fact 'nf-rr-agree-dist)
(fact 'ooint-open 'a 'b)
(fact 'ms-agree-open 'RR-MS '(NF-METRIC-SPACE RR-NORMED-FIELD) (list 'OOINT 'a 'b))
(ass)
(qed 'ooint-open-nf)
(topic! 'ooint-open-nf 'topology)

;;; =====================================================================
;;; (2) A SUBSPACE OF A SUBSPACE, AND THE SHRINKING OF A DERIVATIVE.
;;;
;;; IS-DIFF-ON's continuity conjunct lives on SUBSPACE-MS(NF-METRIC-SPACE K, U),
;;; so shrinking the domain from U to an open V inside it has to move a
;;; continuity statement from the subspace on V OF THE SUBSPACE ON U to the
;;; subspace on V of the ambient space.  Those two are not the same TERM -- the
;;; distance of the first is a lambda whose body is itself a lambda application
;;; -- but they have the same points and the same distance values, which is
;;; exactly what `ms-agree-continuous-at' (diff-on-laws.scm) asks for.
;;; =====================================================================

;;; subspace-restrict-continuous-at: continuity at a point of V, as a map off
;;; the subspace on U, restricts to continuity as a map off the subspace on V.
(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
   (FORALL icu_ (IMPLIES (SUBSET icu_ (PTS s))
   (FORALL icv_ (IMPLIES (SUBSET icv_ icu_)
   (FORALL ict_ (IMPLIES (IS-METRIC-SPACE ict_)
   (FORALL f (FORALL icz_ (IMPLIES (IN icz_ icv_)
     (IMPLIES (IS-CONTINUOUS-AT (SUBSPACE-MS s icu_) ict_ f icz_)
              (IS-CONTINUOUS-AT (SUBSPACE-MS s icv_) ict_ (RESTRICT f icv_) icz_)
     ))))))))))))))
(dk-peel!)
(define ic-msa '(SUBSPACE-MS (SUBSPACE-MS s icu_) icv_))
(define ic-msb '(SUBSPACE-MS s icv_))
(fact 'subset-trans 'icv_ 'icu_ '(PTS s))
(fact 'subspace-is-metric-space 's 'icu_)
(fact 'subspace-is-metric-space 's 'icv_)
(fact 'subspace-pts 's 'icu_)
(fact 'subspace-pts 's 'icv_)
(fact 'subspace-pts '(SUBSPACE-MS s icu_) 'icv_)
(dk-have! '(SUBSET icv_ (PTS (SUBSPACE-MS s icu_)))
  (lambda () (subst '(== (PTS (SUBSPACE-MS s icu_)) icu_)) (ass)))
(fact 'restrict-continuous-at '(SUBSPACE-MS s icu_) 'icv_ 'ict_ 'f 'icz_)
;; the four agreement hypotheses of `ms-agree-continuous-at', landed first --
;; `fact' detaches an antecedent only from the context.
(dk-have! (list '== (list 'PTS ic-msb) (list 'PTS ic-msa))
  (lambda ()
    (subst (list '== (list 'PTS ic-msb) 'icv_))
    (subst (list '== (list 'PTS ic-msa) 'icv_))
    (qrfl)))
(dk-have! '(== (PTS ict_) (PTS ict_)) (lambda () (qrfl)))
(dk-have! (ic-fa2 (list 'PTS ic-msa) (list 'PTS ic-msa)
            (list '== (list (list 'DIST ic-msb) 'dfu_ 'dfv_)
                      (list (list 'DIST ic-msa) 'dfu_ 'dfv_)))
  (lambda ()
    (dk-peel!)
    (dk-have! '(IN dfu_ icv_)
      (lambda () (subst (list '== 'icv_ (list 'PTS ic-msa))) (ass)))
    (dk-have! '(IN dfv_ icv_)
      (lambda () (subst (list '== 'icv_ (list 'PTS ic-msa))) (ass)))
    (fact 'subset-mem-fwd 'icv_ 'icu_ 'dfu_)
    (fact 'subset-mem-fwd 'icv_ 'icu_ 'dfv_)
    (fact 'subspace-dist 's 'icv_ 'dfu_ 'dfv_)
    (fact 'subspace-dist '(SUBSPACE-MS s icu_) 'icv_ 'dfu_ 'dfv_)
    (fact 'subspace-dist 's 'icu_ 'dfu_ 'dfv_)
    (subst (list '== (list (list 'DIST ic-msb) 'dfu_ 'dfv_) '((DIST s) dfu_ dfv_)))
    (subst (list '== (list (list 'DIST ic-msa) 'dfu_ 'dfv_)
                     '((DIST (SUBSPACE-MS s icu_)) dfu_ dfv_)))
    (subst '(== ((DIST (SUBSPACE-MS s icu_)) dfu_ dfv_) ((DIST s) dfu_ dfv_)))
    (qrfl)))
(dk-have! (ic-fa2 '(PTS ict_) '(PTS ict_)
            '(== ((DIST ict_) dfu_ dfv_) ((DIST ict_) dfu_ dfv_)))
  (lambda () (dk-peel!) (qrfl)))
(fact 'ms-agree-continuous-at ic-msa ic-msb 'ict_ 'ict_ '(RESTRICT f icv_) 'icz_)
(ass)
(qed 'subspace-restrict-continuous-at)
(topic! 'subspace-restrict-continuous-at 'analysis)
(alias! 'subspace-restrict-continuous-at
        "continuity on a subspace restricts to a smaller subspace")

;;; diff-on-shrink: the derivative on an open set is LOCAL downwards -- it
;;; survives restriction to any open V inside U that still contains the point.
;;; The same Caratheodory factor, restricted, witnesses it.
(sp (make-wff '(FORALL K (FORALL U (FORALL f (FORALL a (FORALL icl_
   (IMPLIES (IS-DIFF-ON K U f a icl_)
   (FORALL icv_
   (IMPLIES (IS-OPEN (NF-METRIC-SPACE K) icv_)
   (IMPLIES (SUBSET icv_ U)
   (IMPLIES (IN a icv_)
     (IS-DIFF-ON K icv_ (RESTRICT f icv_) a icl_)))))))))))))
(dk-peel!)
(fact 'diff-on-normed-field 'K 'U 'f 'a 'icl_)
(fact 'diff-on-open 'K 'U 'f 'a 'icl_)
(fact 'diff-on-in-fun 'K 'U 'f 'a 'icl_)
(fact 'diff-on-pt-in 'K 'U 'f 'a 'icl_)
(fact 'diff-on-deriv-in-carr 'K 'U 'f 'a 'icl_)
(fact 'nf-metric-space-is-metric-space 'K)
(fact 'nf-metric-carrier 'K)
(fact 'nf-open-subset-carr 'K 'U)
(dk-have! '(SUBSET U (PTS (NF-METRIC-SPACE K)))
  (lambda () (subst '(== (PTS (NF-METRIC-SPACE K)) (CARR K))) (ass)))
(fact 'restrict-in-fun 'f 'U '(CARR K) 'icv_)
(dk-split-all! (dk-landed* (lambda () (mac-h 'IS-DIFF-ON '(IS-DIFF-ON K U f a icl_)))))
(let ((ic-phi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the Caratheodory existential"))))
  (dk-split-all!)
  (let ((ic-cara (dk-pick (lambda (fm)
                            (and (pair? fm) (eq? (car fm) 'FORALL)
                                 (dk-contains? fm ic-phi) (dk-contains? fm 'f)))
                          "the Caratheodory universal")))
    (fact 'restrict-in-fun ic-phi 'U '(CARR K) 'icv_)
    (fact 'restrict-apply ic-phi 'icv_ 'a)
    (fact 'restrict-apply 'f 'icv_ 'a)
    (fact 'subspace-restrict-continuous-at '(NF-METRIC-SPACE K) 'U 'icv_
          '(NF-METRIC-SPACE K) ic-phi 'a)
    (mac 'IS-DIFF-ON)
    (dk-conj-close!
     (lambda ()
       (if (not (eq? (ic-head (dk-goal)) 'FORSOME))
           (ass)
           (begin
             (ew (list 'RESTRICT ic-phi 'icv_))
             (dk-conj-close!
              (lambda ()
                (let ((g (dk-goal)))
                  (cond
                    ((eq? (ic-head g) '=)
                     (subst (list '== (list (list 'RESTRICT ic-phi 'icv_) 'a)
                                  (list ic-phi 'a)))
                     (ass))
                    ((eq? (ic-head g) 'FORALL)
                     (let ((z (dk-di-var!)))
                       (fact 'subset-mem-fwd 'icv_ 'U z)
                       (fact 'restrict-apply 'f 'icv_ z)
                       (fact 'restrict-apply ic-phi 'icv_ z)
                       (subst (list '== (list (list 'RESTRICT 'f 'icv_) z) (list 'f z)))
                       (subst (list '== (list (list 'RESTRICT 'f 'icv_) 'a) '(f a)))
                       (subst (list '== (list (list 'RESTRICT ic-phi 'icv_) z)
                                    (list ic-phi z)))
                       (dk-apply! ic-cara z)
                       (ass)))
                    (#t (ass))))))))))))
(qed 'diff-on-shrink)
(topic! 'diff-on-shrink 'analysis)
(alias! 'diff-on-shrink "a derivative on an open set restricts to a smaller open set")

;;; restrict-in-fun-of-restrict: if the restriction of f to U is a function on
;;; U, so is its restriction to any subclass V.  `restrict-in-fun' does NOT
;;; give this: its hypothesis is about f itself, and in HAS-DERIV-AT nothing
;;; is ever known about f outside the neighbourhood.
(sp (make-wff '(FORALL f (FORALL U (FORALL icc_ (FORALL icv_
   (IMPLIES (IN (RESTRICT f U) (FUN U icc_))
   (IMPLIES (SUBSET icv_ U)
            (IN (RESTRICT f icv_) (FUN icv_ icc_))))))))))
(dk-peel!)
(fact 'fun-domain-in-set 'U 'icc_ '(RESTRICT f U))
(fact 'subclass-of-set-is-set 'icv_ 'U)
(mac 'RESTRICT)
(for-each
 (lambda (k)
   (dk-focus! k)
   (if (equal? (dk-goal) '(IN icv_ SET))
       (ass)
       (let ((z (dk-di-var!)))
         (fact 'subset-mem-fwd 'icv_ 'U z)
         (fact 'restrict-apply 'f 'U z)
         (fact 'fun-apply-type-c '(RESTRICT f U) 'U 'icc_ z)
         (subst (list '== (list 'f z) (list '(RESTRICT f U) z)))
         (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'restrict-in-fun-of-restrict)
(topic! 'restrict-in-fun-of-restrict 'plumbing)

;;; diff-on-shrink-restrict: the form the local derivative actually uses --
;;; shrink the domain AND re-read the function as a restriction of f itself,
;;; not as a restriction of a restriction.  `diff-on-shrink' lands the latter;
;;; the two agree at every point of V, so `diff-on-transfer-ptwise-eq'
;;; (holomorphic-basics-2.scm) closes the gap.
(sp (make-wff '(FORALL K (FORALL U (FORALL f (FORALL a (FORALL icl_
   (IMPLIES (IS-DIFF-ON K U (RESTRICT f U) a icl_)
   (FORALL icv_
   (IMPLIES (IS-OPEN (NF-METRIC-SPACE K) icv_)
   (IMPLIES (SUBSET icv_ U)
   (IMPLIES (IN a icv_)
     (IS-DIFF-ON K icv_ (RESTRICT f icv_) a icl_)))))))))))))
(dk-peel!)
(fact 'diff-on-in-fun 'K 'U '(RESTRICT f U) 'a 'icl_)
(fact 'restrict-in-fun-of-restrict 'f 'U '(CARR K) 'icv_)
(fact 'diff-on-shrink 'K 'U '(RESTRICT f U) 'a 'icl_ 'icv_)
(dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES '(IN hbx_ icv_)
            '(== ((RESTRICT f icv_) hbx_)
                 ((RESTRICT (RESTRICT f U) icv_) hbx_))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'subset-mem-fwd 'icv_ 'U z)
      (fact 'restrict-apply 'f 'icv_ z)
      (fact 'restrict-apply '(RESTRICT f U) 'icv_ z)
      (fact 'restrict-apply 'f 'U z)
      (subst (list '== (list '(RESTRICT f icv_) z) (list 'f z)))
      (subst (list '== (list '(RESTRICT (RESTRICT f U) icv_) z)
                   (list '(RESTRICT f U) z)))
      (subst (list '== (list '(RESTRICT f U) z) (list 'f z)))
      (qrfl))))
(fact 'diff-on-transfer-ptwise-eq 'K 'icv_ '(RESTRICT f icv_)
      '(RESTRICT (RESTRICT f U) icv_) 'a 'icl_)
(ass)
(qed 'diff-on-shrink-restrict)
(topic! 'diff-on-shrink-restrict 'analysis)
(alias! 'diff-on-shrink-restrict
        "a derivative of a restriction shrinks to a smaller open set")

;;; =====================================================================
;;; (3) HAS-DERIV-AT: INTRODUCTION, READ-OFFS, SHRINKING, UNIQUENESS.
;;; =====================================================================

;;; diff-on-ooint-shrink: the derivative of a restriction on a symmetric open
;;; interval passes to any smaller symmetric open interval about the centre.
(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL ice_ (IMPLIES (POS-RR ice_)
   (FORALL icw_ (IMPLIES (POS-RR icw_)
   (IMPLIES (<= icw_ ice_)
   (FORALL f (FORALL icl_
   (IMPLIES (IS-DIFF-ON RR-NORMED-FIELD (OOINT (- a ice_) (+ a ice_))
                        (RESTRICT f (OOINT (- a ice_) (+ a ice_))) a icl_)
            (IS-DIFF-ON RR-NORMED-FIELD (OOINT (- a icw_) (+ a icw_))
                        (RESTRICT f (OOINT (- a icw_) (+ a icw_))) a icl_)
   ))))))))))))
(dk-peel!)
(fact 'rr-pos-rr-in-rr 'ice_)
(fact 'rr-lt-of-pos-rr 'ice_)
(fact 'rr-pos-rr-in-rr 'icw_)
(fact 'rr-lt-of-pos-rr 'icw_)
(fact 'rr-sub-in-rr 'a 'icw_)
(fact 'rr-add-in-rr 'a 'icw_)
(fact 'ooint-open-nf '(- a icw_) '(+ a icw_))
(fact 'ooint-center 'a 'icw_)
(dk-have! '(SUBSET (OOINT (- a icw_) (+ a icw_)) (OOINT (- a ice_) (+ a ice_)))
  (lambda ()
    (let ((z (subset-by-element!)))
      (ic-ooint-in! z '(- a icw_) '(+ a icw_))
      (mac 'ooint-membership)
      (ic-conj-ineq!
       (list '(IN a RR) '(IN ice_ RR) '(IN icw_ RR) (list 'IN z 'RR)
             '(<= icw_ ice_) '(< 0 icw_) '(< 0 ice_)
             (list '< '(- a icw_) z) (list '< z '(+ a icw_)))))))
(fact 'diff-on-shrink-restrict 'RR-NORMED-FIELD '(OOINT (- a ice_) (+ a ice_))
      'f 'a 'icl_ '(OOINT (- a icw_) (+ a icw_)))
(ass)
(qed 'diff-on-ooint-shrink)
(topic! 'diff-on-ooint-shrink 'analysis)

;;; has-deriv-at-intro: the definition, used forwards.
(sp (make-wff '(FORALL f (FORALL a (FORALL icl_ (FORALL ice_
   (IMPLIES (POS-RR ice_)
   (IMPLIES (IS-DIFF-ON RR-NORMED-FIELD (OOINT (- a ice_) (+ a ice_))
                        (RESTRICT f (OOINT (- a ice_) (+ a ice_))) a icl_)
            (HAS-DERIV-AT f a icl_)))))))))
(dk-peel!)
(mac 'HAS-DERIV-AT)
(ew 'ice_)
(dk-conj-close! (lambda () (ass)))
(qed 'has-deriv-at-intro)
(topic! 'has-deriv-at-intro 'analysis)

;;; has-deriv-at-shrink: the derivative can be witnessed on an ARBITRARILY
;;; SMALL symmetric interval -- the form every later proof uses, because the
;;; radius the definition hands over is opaque.
(sp (make-wff '(FORALL f (FORALL a (FORALL icl_
   (IMPLIES (HAS-DERIV-AT f a icl_)
   (FORALL icr_ (IMPLIES (POS-RR icr_)
     (FORSOME icw_ (AND (POS-RR icw_)
                   (AND (<= icw_ icr_)
                        (IS-DIFF-ON RR-NORMED-FIELD (OOINT (- a icw_) (+ a icw_))
                                    (RESTRICT f (OOINT (- a icw_) (+ a icw_)))
                                    a icl_))))))))))))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda () (mac-h 'HAS-DERIV-AT '(HAS-DERIV-AT f a icl_)))))
(let ((ice (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the radius existential"))))
  (dk-split-all!)
  (fact 'diff-on-pt-in 'RR-NORMED-FIELD
        (list 'OOINT (list '- 'a ice) (list '+ 'a ice))
        (list 'RESTRICT 'f (list 'OOINT (list '- 'a ice) (list '+ 'a ice))) 'a 'icl_)
  (fact 'ooint-elt-in-rr (list '- 'a ice) (list '+ 'a ice) 'a)
  (fact 'rr-pos-rr-in-rr ice)
  (fact 'rr-lt-of-pos-rr ice)
  (fact 'rr-pos-rr-in-rr 'icr_)
  (fact 'rr-lt-of-pos-rr 'icr_)
  (let ((w (dk-skolem! (dk-fact! 'rr-min-pos ice 'icr_))))
    (dk-split-all!)
    (fact 'rr-pos-rr-of-lt w)
    (fact 'diff-on-ooint-shrink 'a ice w 'f 'icl_)
    (ew w)
    (dk-conj-close! (lambda () (ass)))))
(qed 'has-deriv-at-shrink)
(topic! 'has-deriv-at-shrink 'analysis)
(alias! 'has-deriv-at-shrink
        "a derivative at a point is witnessed on arbitrarily small intervals")

;;; has-deriv-at-pt-in-rr / has-deriv-at-in-rr: the two typings the definition
;;; carries but does not state.
(sp (make-wff '(FORALL f (FORALL a (FORALL icl_
   (IMPLIES (HAS-DERIV-AT f a icl_) (IN a RR)))))))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda () (mac-h 'HAS-DERIV-AT '(HAS-DERIV-AT f a icl_)))))
(let ((ice (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the radius existential"))))
  (dk-split-all!)
  (fact 'diff-on-pt-in 'RR-NORMED-FIELD
        (list 'OOINT (list '- 'a ice) (list '+ 'a ice))
        (list 'RESTRICT 'f (list 'OOINT (list '- 'a ice) (list '+ 'a ice))) 'a 'icl_)
  (fact 'ooint-elt-in-rr (list '- 'a ice) (list '+ 'a ice) 'a)
  (ass))
(qed 'has-deriv-at-pt-in-rr)
(topic! 'has-deriv-at-pt-in-rr 'analysis)

(sp (make-wff '(FORALL f (FORALL a (FORALL icl_
   (IMPLIES (HAS-DERIV-AT f a icl_) (IN icl_ RR)))))))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda () (mac-h 'HAS-DERIV-AT '(HAS-DERIV-AT f a icl_)))))
(let ((ice (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the radius existential"))))
  (dk-split-all!)
  (fact 'diff-on-deriv-in-carr 'RR-NORMED-FIELD
        (list 'OOINT (list '- 'a ice) (list '+ 'a ice))
        (list 'RESTRICT 'f (list 'OOINT (list '- 'a ice) (list '+ 'a ice))) 'a 'icl_)
  (fact 'rr-nf-carr)
  (subst '(== RR (CARR RR-NORMED-FIELD)))
  (ass))
(qed 'has-deriv-at-in-rr)
(topic! 'has-deriv-at-in-rr 'analysis)

;;; has-deriv-at-unique: the value is unique.  Both witnesses are shrunk to a
;;; COMMON interval and `diff-on-unique' (diff-on-laws-2.scm) finishes; its
;;; non-triviality antecedent for RR is `rr-nf-small-elements'.
(sp (make-wff '(FORALL f (FORALL a (FORALL icl_ (FORALL icm_
   (IMPLIES (HAS-DERIV-AT f a icl_)
   (IMPLIES (HAS-DERIV-AT f a icm_) (= icl_ icm_)))))))))
(dk-peel!)
(fact 'rr-is-normed-field)
(fact 'rr-nf-small-elements)
(fact 'has-deriv-at-pt-in-rr 'f 'a 'icl_)
(dk-split-all! (dk-landed* (lambda () (mac-h 'HAS-DERIV-AT '(HAS-DERIV-AT f a icl_)))))
(let ((e1 (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the radius existential"))))
  (dk-split-all!)
  (let ((w (dk-skolem! (dk-fact! 'has-deriv-at-shrink 'f 'a 'icm_ e1))))
    (dk-split-all!)
    (fact 'diff-on-ooint-shrink 'a e1 w 'f 'icl_)
    (fact 'diff-on-unique 'RR-NORMED-FIELD
          (list 'OOINT (list '- 'a w) (list '+ 'a w))
          (list 'RESTRICT 'f (list 'OOINT (list '- 'a w) (list '+ 'a w)))
          'a 'icl_ 'icm_)
    (ass)))
(qed 'has-deriv-at-unique)
(topic! 'has-deriv-at-unique 'analysis)
(alias! 'has-deriv-at-unique "the derivative at a point is unique")

;;; =====================================================================
;;; (4) THE LOCAL DERIVATIVE OF A TOTAL FUNCTION IS THE DERIVATIVE.
;;;
;;; This is the one direction that is NOT a restriction: from a Caratheodory
;;; factor phi defined only on an open interval around a, a factor defined on
;;; ALL of RR has to be produced.  It is produced by FREEZING phi outside a
;;; closed sub-interval:
;;;
;;;     psi(y)  =  IF |y - a| <= rho THEN phi(y) ELSE L,      2 rho = eps,
;;;
;;; which is in FUN(RR, RR) (the true branch sits inside the interval where phi
;;; is defined, the false branch is the constant L), is continuous at a because
;;; it agrees with phi on a whole neighbourhood of a, has psi(a) = phi(a) = L,
;;; and factors f(x) - f(a) for every x within rho of a.  `diff-at-local'
;;; (theorem-library/diff-at-local.scm) asks for exactly that much and returns
;;; IS-DIFF-AT.  NO DIVISION IS INVOLVED: the naive extension of phi by the
;;; difference quotient would need `recip' and a case analysis on y = a.
;;; =====================================================================

(define ic-nfm '(NF-METRIC-SPACE RR-NORMED-FIELD))

;;; the base facts about the two spellings of the real line, landed once.
(define (ic-rr-setup!)
  (fact 'rr-is-normed-field)
  (fact 'rr-is-metric-space)
  (fact 'nf-rr-is-metric-space)
  (fact 'nf-rr-agree-pts)
  (fact 'nf-rr-agree-dist)
  (fact 'ms-agree-pts-sym 'RR-MS ic-nfm)
  (fact 'ms-agree-dist-sym 'RR-MS ic-nfm)
  (fact 'rr-nf-carr)
  (fact 'r7q-rr-pts))

;;; `if-true' on IFTERM whose condition the context already settles: CLOSER
;;; proves the condition, the main branch gets the equation substituted into
;;; the goal, and the main leaf is left in focus.
(define (ic-if-true! ifterm closer)
  (let* ((ls   (dk-opened (lambda () (if-true ifterm))))
         (cnd  (filter (lambda (s) (equal? (dk-goal-of s) (cadr ifterm))) ls))
         (main (filter (lambda (s) (not (member s cnd))) ls)))
    (for-each (lambda (s) (dk-focus! s) (closer)) cnd)
    (if (null? main)
        (error "ic-if-true!: no main branch")
        (begin (dk-focus! (car main))
               (subst (list '= ifterm (caddr ifterm)))
               (car main)))))

;;; the whole case analysis on an IF condition: BODY is run on each main
;;; branch with #t / #f saying which case it is.
(define (ic-if-cases! ifterm body)
  (let ((cnd (cadr ifterm)))
    (for-each
     (lambda (cs)
       (let ((true? (and (member cnd (dk-asms-of cs)) #t)))
         (dk-focus! cs)
         (for-each
          (lambda (s)
            (dk-focus! s)
            (if (or (equal? (dk-goal) cnd) (equal? (dk-goal) (list 'NOT cnd)))
                (ass)
                (begin
                  (subst (list '= ifterm (if true? (caddr ifterm) (cadddr ifterm))))
                  (body true?))))
          (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))))
     (dk-opened (lambda () (use-em cnd))))))

(sp (make-wff '(FORALL f (IMPLIES (IN f (FUN RR RR))
   (FORALL a (IMPLIES (IN a RR)
   (FORALL ice_ (IMPLIES (POS-RR ice_)
   (FORALL icl_
   (IMPLIES (IS-DIFF-ON RR-NORMED-FIELD (OOINT (- a ice_) (+ a ice_))
                        (RESTRICT f (OOINT (- a ice_) (+ a ice_))) a icl_)
            (IS-DIFF-AT f a icl_)))))))))))
(dk-peel!)
(ic-rr-setup!)
(fact 'rr-pos-rr-in-rr 'ice_)
(fact 'rr-lt-of-pos-rr 'ice_)
(fact 'rr-sub-in-rr 'a 'ice_)
(fact 'rr-add-in-rr 'a 'ice_)
(define ic-u '(OOINT (- a ice_) (+ a ice_)))
(define ic-sub-rr (list 'SUBSPACE-MS 'RR-MS ic-u))
(define ic-sub-nf (list 'SUBSPACE-MS ic-nfm ic-u))
(fact 'ooint-subset-rr '(- a ice_) '(+ a ice_))
(dk-have! (list 'SUBSET ic-u '(PTS RR-MS))
  (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
(fact 'subspace-is-metric-space 'RR-MS ic-u)
(fact 'subspace-pts 'RR-MS ic-u)
(fact 'subspace-pts ic-nfm ic-u)
(fact 'diff-on-deriv-in-carr 'RR-NORMED-FIELD ic-u (list 'RESTRICT 'f ic-u) 'a 'icl_)
(dk-have! '(IN icl_ RR) (lambda () (subst '(== RR (CARR RR-NORMED-FIELD))) (ass)))
(define ic-rho (dk-halve! 'ice_))
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'IS-DIFF-ON (list 'IS-DIFF-ON 'RR-NORMED-FIELD ic-u (list 'RESTRICT 'f ic-u)
                           'a 'icl_)))))
(define ic-phi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the Caratheodory existential")))
(dk-split-all!)
(define ic-cara
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm ic-phi) (dk-contains? fm 'f)))
           "the Caratheodory universal"))
(dk-have! (list 'IN ic-phi (list 'FUN ic-u 'RR))
  (lambda () (subst '(== RR (CARR RR-NORMED-FIELD))) (ass)))

;;; the continuity of phi at a, moved from the normed field's spelling of the
;;; real line to RR-MS.
(dk-have! (list '== (list 'PTS ic-sub-rr) (list 'PTS ic-sub-nf))
  (lambda ()
    (subst (list '== (list 'PTS ic-sub-rr) ic-u))
    (subst (list '== (list 'PTS ic-sub-nf) ic-u))
    (qrfl)))
(dk-have! (ic-fa2 (list 'PTS ic-sub-nf) (list 'PTS ic-sub-nf)
            (list '== (list (list 'DIST ic-sub-rr) 'dfu_ 'dfv_)
                      (list (list 'DIST ic-sub-nf) 'dfu_ 'dfv_)))
  (lambda ()
    (dk-peel!)
    (dk-have! (list 'IN 'dfu_ ic-u)
      (lambda () (subst (list '== ic-u (list 'PTS ic-sub-nf))) (ass)))
    (dk-have! (list 'IN 'dfv_ ic-u)
      (lambda () (subst (list '== ic-u (list 'PTS ic-sub-nf))) (ass)))
    (fact 'ooint-elt-in-rr '(- a ice_) '(+ a ice_) 'dfu_)
    (fact 'ooint-elt-in-rr '(- a ice_) '(+ a ice_) 'dfv_)
    (dk-have! '(IN dfu_ (PTS RR-MS)) (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
    (dk-have! '(IN dfv_ (PTS RR-MS)) (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
    (fact 'subspace-dist 'RR-MS ic-u 'dfu_ 'dfv_)
    (fact 'subspace-dist ic-nfm ic-u 'dfu_ 'dfv_)
    (fact 'nf-rr-agree-dist 'dfu_ 'dfv_)
    (subst (list '== (list (list 'DIST ic-sub-rr) 'dfu_ 'dfv_) '((DIST RR-MS) dfu_ dfv_)))
    (subst (list '== (list (list 'DIST ic-sub-nf) 'dfu_ 'dfv_)
                     (list (list 'DIST ic-nfm) 'dfu_ 'dfv_)))
    (subst (list '== (list (list 'DIST ic-nfm) 'dfu_ 'dfv_) '((DIST RR-MS) dfu_ dfv_)))
    (qrfl)))
(fact 'ms-agree-continuous-at ic-sub-nf ic-sub-rr ic-nfm 'RR-MS ic-phi 'a)

;;; the frozen factor.
(define ic-psi
  (list 'VNB-LAMBDA 'icpz_ 'RR
        (list 'IF (list '<= (list 'abs (list '- 'icpz_ 'a)) ic-rho)
              (list ic-phi 'icpz_) 'icl_)))
(define (ic-cond-at-a!)
  (fact 'rr-sub-in-rr 'a 'a)
  (dk-have! '(<= 0 (- a a)) (lambda () (dk-ineq! '(IN a RR))))
  (fact 'rr-abs-of-nonneg '(- a a))
  (subst (list '= '(abs (- a a)) '(- a a)))
  (dk-ineq! '(IN a RR) (list 'IN ic-rho 'RR) (list '< 0 ic-rho)))

(define (ic-if-at z)
  (list 'IF (list '<= (list 'abs (list '- z 'a)) ic-rho) (list ic-phi z) 'icl_))

;;; "z is within rho of a, hence inside the interval of radius eps".
(define (ic-in-u! z)
  (dk-have! (list 'IN z ic-u)
    (lambda ()
      (let ((bnds (ic-absplit! (list '<= (list 'abs (list '- z 'a)) ic-rho))))
        (mac 'ooint-membership)
        (ic-conj-ineq!
         (append (list '(IN a RR) '(IN ice_ RR) (list 'IN ic-rho 'RR) (list 'IN z 'RR)
                       (list '= (list '+ ic-rho ic-rho) 'ice_) (list '< 0 ic-rho))
                 bnds))))))

;;; (1) psi is a function on the whole line.
(dk-have! (list 'IN ic-psi '(FUN RR RR))
  (lambda ()
    (for-each
     (lambda (k)
       (dk-focus! k)
       (if (equal? (dk-goal) '(IN RR SET))
           (begin (fact 'rr-is-set) (ass))
           (let ((z (dk-di-var!)))
             (fact 'rr-sub-in-rr z 'a)
             (fact 'rr-abs-closed (list '- z 'a))
             (ic-if-cases!
              (ic-if-at z)
              (lambda (true?)
                (if true?
                    (begin (ic-in-u! z)
                           (fact 'fun-apply-type-c ic-phi ic-u 'RR z)
                           (ass))
                    (ass)))))))
     (dk-opened (lambda () (lam-t))))))

;;; (2) psi(a) = L.
(dk-have! (list '= (list ic-psi 'a) 'icl_)
  (lambda ()
    (dk-lam-b!)
    (ic-if-true! (ic-if-at 'a) ic-cond-at-a!)
    (ass)))

;;; (3) psi is continuous at a, because it IS phi on a neighbourhood of a.
(fact 'ooint-center 'a 'ice_)
(dk-have! (list 'IN ic-psi '(FUN (PTS RR-MS) (PTS RR-MS)))
  (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
(dk-have! '(IN a (PTS RR-MS))
  (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
(dk-have! (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS ic-psi 'a)
  (lambda ()
    (mac 'IS-CONTINUOUS-AT)
    (dk-conj-close!
     (lambda ()
       (if (not (eq? (ic-head (dk-goal)) 'FORALL))
           (ass)
           (let* ((new (dk-landed* (lambda () (dk-peel!))))
                  (eps (cadr (car (filter (dk-head? 'POS-RR) new)))))
             (dk-split-all!
              (dk-landed* (lambda ()
                (mac-h 'IS-CONTINUOUS-AT
                       (list 'IS-CONTINUOUS-AT ic-sub-rr 'RR-MS ic-phi 'a)))))
             (let* ((univ (dk-pick (lambda (fm)
                                     (and (pair? fm) (eq? (car fm) 'FORALL)
                                          (dk-contains? fm 'POS-RR)
                                          (dk-contains? fm 'FORSOME)))
                                   "the eps universal"))
                    (dl0 (dk-skolem! (dk-apply! univ eps))))
               (dk-split-all!)
               (fact 'rr-pos-rr-in-rr dl0)
               (fact 'rr-lt-of-pos-rr dl0)
               (let ((dl (dk-skolem! (dk-fact! 'rr-min-pos dl0 ic-rho))))
                 (dk-split-all!)
                 (fact 'rr-pos-rr-of-lt dl)
                 (ew dl)
                 (dk-conj-close!
                  (lambda ()
                    (if (eq? (ic-head (dk-goal)) 'POS-RR)
                        (ass)
                        (let ((bb (car (dk-peel!))))
                          (let ((b (cadr (car (filter (lambda (fm)
                                                        (and (pair? fm) (eq? (car fm) 'IN)
                                                             (equal? (caddr fm) '(PTS RR-MS))))
                                                      (dk-asms))))))
                            (dk-have! (list 'IN b 'RR)
                              (lambda () (subst '(== RR (PTS RR-MS))) (ass)))
                            (fact 'rr-ms-dist 'a b)
                            (fact 'rr-abs-sub-sym 'a b)
                            (fact 'rr-sub-in-rr 'a b)
                            (fact 'rr-sub-in-rr b 'a)
                            (fact 'rr-abs-closed (list '- 'a b))
                            (fact 'rr-abs-closed (list '- b 'a))
                            (dk-have! (list '<= (list 'abs (list '- 'a b)) dl)
                              (lambda ()
                                (subst (list '== (list 'abs (list '- 'a b))
                                             (list '(DIST RR-MS) 'a b)))
                                (ass)))
                            (dk-have! (list '<= (list 'abs (list '- b 'a)) ic-rho)
                              (lambda ()
                                (subst (list '= (list 'abs (list '- b 'a))
                                             (list 'abs (list '- 'a b))))
                                (dk-ineq! (list '<= (list 'abs (list '- 'a b)) dl)
                                          (list '<= dl ic-rho)
                                          (list 'IN dl 'RR) (list 'IN ic-rho 'RR)
                                          (list 'IN 'a 'RR) (list 'IN b 'RR))))
                            (ic-in-u! b)
                            (dk-have! (list 'IN b (list 'PTS ic-sub-rr))
                              (lambda () (subst (list '== (list 'PTS ic-sub-rr) ic-u)) (ass)))
                            (fact 'subspace-dist 'RR-MS ic-u 'a b)
                            (dk-have! (list '<= (list (list 'DIST ic-sub-rr) 'a b) dl0)
                              (lambda ()
                                (subst (list '== (list (list 'DIST ic-sub-rr) 'a b)
                                             (list '(DIST RR-MS) 'a b)))
                                (subst (list '== (list '(DIST RR-MS) 'a b)
                                             (list 'abs (list '- 'a b))))
                                (dk-ineq! (list '<= (list 'abs (list '- 'a b)) dl)
                                          (list '<= dl dl0)
                                          (list 'IN dl 'RR) (list 'IN dl0 'RR)
                                          (list 'IN (list 'abs (list '- 'a b)) 'RR))))
                            (let ((duniv (dk-pick (lambda (fm)
                                                    (and (pair? fm) (eq? (car fm) 'FORALL)
                                                         (dk-contains? fm dl0)
                                                         (dk-contains? fm ic-phi)))
                                                  "the delta universal")))
                              (dk-apply! duniv b))
                            (dk-lam-b!)
                            (ic-if-true! (ic-if-at 'a) ic-cond-at-a!)
                            (ic-if-true! (ic-if-at b) (lambda () (ass)))
                            (ass))))))))))))))

;;; (4) the factorization, within rho of a.
(dk-have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
            (list 'IMPLIES (list '<= (list 'abs (list '- 'x_ 'a)) ic-rho)
                  (list '= '(- (f x_) (f a))
                        (list '* (list ic-psi 'x_) '(- x_ a))))))
  (lambda ()
    (dk-peel!)
    (fact 'rr-sub-in-rr 'x_ 'a)
    (fact 'rr-abs-closed '(- x_ a))
    (ic-in-u! 'x_)
    (fact 'fun-apply-type-c 'f 'RR 'RR 'x_)
    (fact 'fun-apply-type-c 'f 'RR 'RR 'a)
    (fact 'fun-apply-type-c ic-phi ic-u 'RR 'x_)
    (dk-lam-b!)
    (ic-if-true! (ic-if-at 'x_) (lambda () (ass)))
    (fact 'restrict-apply 'f ic-u 'x_)
    (fact 'restrict-apply 'f ic-u 'a)
    (fact 'rr-nf-sub '(f x_) '(f a))
    (fact 'rr-nf-sub 'x_ 'a)
    (fact 'rr-nf-mul-apply (list ic-phi 'x_) '(- x_ a))
    (subst (list '== '(- (f x_) (f a))
                 '((ADD RR-NORMED-FIELD) (f x_) ((NEG RR-NORMED-FIELD) (f a)))))
    (subst (list '== (list '* (list ic-phi 'x_) '(- x_ a))
                 (list '(MUL RR-NORMED-FIELD) (list ic-phi 'x_) '(- x_ a))))
    (subst (list '== '(- x_ a)
                 '((ADD RR-NORMED-FIELD) x_ ((NEG RR-NORMED-FIELD) a))))
    (subst (list '== '(f x_) (list (list 'RESTRICT 'f ic-u) 'x_)))
    (subst (list '== '(f a) (list (list 'RESTRICT 'f ic-u) 'a)))
    (dk-apply! ic-cara 'x_)
    (ass)))

(fact 'diff-at-local 'f ic-psi 'a 'icl_ ic-rho)
(ass)
(qed 'diff-on-nbhd-implies-diff-at)
(topic! 'diff-on-nbhd-implies-diff-at 'analysis)
(alias! 'diff-on-nbhd-implies-diff-at
        "a derivative on a neighbourhood is the derivative of the whole function")

;;; =====================================================================
;;; (5) HAS-DERIV-AT AND IS-DIFF-AT AGREE ON A FUNCTION DEFINED EVERYWHERE.
;;;
;;; This is the statement the specification asks for ("for f in fun(rr, rr) it
;;; coincides with the existing is-diff-at").  Forwards it is section 4;
;;; backwards it is the bridge `diff-at-iff-diff-on' (diff-on-laws.scm)
;;; followed by `diff-on-shrink' down to the unit interval about a.
;;; =====================================================================
(sp (make-wff '(FORALL f (IMPLIES (IN f (FUN RR RR))
   (FORALL a (FORALL icl_
     (IFF (HAS-DERIV-AT f a icl_) (IS-DIFF-AT f a icl_))))))))
(dk-peel!)
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(fact 'rr-pos-rr-of-lt 1)
(dk-iff!
 (dk-head? 'IS-DIFF-AT)
 ;; ---- forward: the local derivative of a total function ----------------
 (lambda ()
   (fact 'has-deriv-at-pt-in-rr 'f 'a 'icl_)
   (dk-split-all! (dk-landed* (lambda ()
     (mac-h 'HAS-DERIV-AT '(HAS-DERIV-AT f a icl_)))))
   (let ((e (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the radius existential"))))
     (dk-split-all!)
     (fact 'diff-on-nbhd-implies-diff-at 'f 'a e 'icl_)
     (ass)))
 ;; ---- backward: the global derivative restricts ------------------------
 (lambda ()
   (fact 'diff-at-iff-diff-on 'f 'a 'icl_)
   (mac-h 'diff-at-iff-diff-on '(IS-DIFF-AT f a icl_))
   (fact 'diff-on-pt-in 'RR-NORMED-FIELD 'RR 'f 'a 'icl_)
   (fact 'rr-sub-in-rr 'a 1)
   (fact 'rr-add-in-rr 'a 1)
   (fact 'ooint-open-nf '(- a 1) '(+ a 1))
   (fact 'ooint-subset-rr '(- a 1) '(+ a 1))
   (fact 'ooint-center 'a 1)
   (fact 'diff-on-shrink 'RR-NORMED-FIELD 'RR 'f 'a 'icl_ '(OOINT (- a 1) (+ a 1)))
   (fact 'has-deriv-at-intro 'f 'a 'icl_ 1)
   (ass)))
(qed 'has-deriv-at-iff-diff-at)
(topic! 'has-deriv-at-iff-diff-at 'analysis)
(alias! 'has-deriv-at-iff-diff-at
        "for a function on the whole line the local derivative is the derivative")

;;; =====================================================================
;;; (6) STAGE 2 -- THE EXTENSION LEMMA.
;;;
;;; docs/real-calculus-statements.tex, section 5: for a < b and
;;; f in FUN(CCINT(a,b), RR), the extension of f by the constants f(a) and f(b)
;;; is a function on the whole line, agrees with f on [a, b], is continuous at
;;; every real when f is continuous on [a, b], and has the same derivative as f
;;; at every interior point.  EXTEND-CONST is the CLAMPED COMPOSITE (see
;;; structure-library/interval-calculus.scm), so each of the four is a citation
;;; of the corresponding CLAMP law and no case analysis appears anywhere.
;;; =====================================================================

;;; extend-const-value: the extension is f AT THE CLAMPED ARGUMENT.
(sp (make-wff '(FORALL f (FORALL a (FORALL b (FORALL icz_
   (IMPLIES (IN icz_ RR)
            (== ((EXTEND-CONST f a b) icz_) (f (CLAMP a b icz_))))))))))
(dk-peel!)
(mac 'EXTEND-CONST)
(dk-lam-b!)
(qrfl)
(qed 'extend-const-value)
(topic! 'extend-const-value 'analysis)

;;; extend-const-in-fun: it is a function on the whole line.
(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL b (IMPLIES (IN b RR)
   (IMPLIES (<= a b)
   (FORALL f (IMPLIES (IN f (FUN (CCINT a b) RR))
     (IN (EXTEND-CONST f a b) (FUN RR RR)))))))))))
(dk-peel!)
(mac 'EXTEND-CONST)
(for-each
 (lambda (k)
   (dk-focus! k)
   (if (equal? (dk-goal) '(IN RR SET))
       (begin (fact 'rr-is-set) (ass))
       (let ((z (dk-di-var!)))
         (fact 'clamp-in-ccint 'a 'b z)
         (fact 'fun-apply-type-c 'f '(CCINT a b) 'RR (list 'CLAMP 'a 'b z))
         (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'extend-const-in-fun)
(topic! 'extend-const-in-fun 'analysis)
(alias! 'extend-const-in-fun "the constant extension is a function on the line")

;;; extend-const-fixes: it agrees with f on [a, b].
(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL b (IMPLIES (IN b RR)
   (FORALL icz_ (IMPLIES (IN icz_ RR)
   (IMPLIES (<= a icz_) (IMPLIES (<= icz_ b)
   (FORALL f (== ((EXTEND-CONST f a b) icz_) (f icz_)))))))))))))
(dk-peel!)
(mac 'EXTEND-CONST)
(dk-lam-b!)
(fact 'clamp-fixes 'a 'b 'icz_)
(subst '(= (CLAMP a b icz_) icz_))
(qrfl)
(qed 'extend-const-fixes)
(topic! 'extend-const-fixes 'analysis)
(alias! 'extend-const-fixes "the constant extension agrees with f on the interval")

;;; extend-const-ccint-fixes: the same, keyed on membership of the interval --
;;; the shape every citer below has in hand.
(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL b (IMPLIES (IN b RR)
   (FORALL icz_ (IMPLIES (IN icz_ (CCINT a b))
   (FORALL f (== ((EXTEND-CONST f a b) icz_) (f icz_)))))))))))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'ccint-membership '(IN icz_ (CCINT a b))))))
(fact 'extend-const-fixes 'a 'b 'icz_ 'f)
(ass)
(qed 'extend-const-ccint-fixes)
(topic! 'extend-const-ccint-fixes 'analysis)

;;; extend-const-continuous-at: continuous at EVERY real.  No cases: the clamp
;;; is 1-Lipschitz, so f's own delta at CLAMP(a, b, t) serves unchanged.
(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL b (IMPLIES (IN b RR)
   (IMPLIES (<= a b)
   (FORALL f (IMPLIES (IS-CONTINUOUS-ON f (CCINT a b))
   (FORALL ict_ (IMPLIES (IN ict_ RR)
     (IS-CONTINUOUS-AT RR-MS RR-MS (EXTEND-CONST f a b) ict_))))))))))))
(dk-peel!)
(define ic-ci '(CCINT a b))
(define ic-sub-cc (list 'SUBSPACE-MS 'RR-MS ic-ci))
(define ic-ext '(EXTEND-CONST f a b))
(define ic-ct '(CLAMP a b ict_))
(fact 'rr-is-metric-space)
(fact 'r7q-rr-pts)
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'IS-CONTINUOUS-ON (list 'IS-CONTINUOUS-ON 'f ic-ci)))))
(fact 'extend-const-in-fun 'a 'b 'f)
(fact 'subspace-pts 'RR-MS ic-ci)
(fact 'clamp-in-rr 'a 'b 'ict_)
(fact 'clamp-in-ccint 'a 'b 'ict_)
(dk-have! (list 'IN ic-ext '(FUN (PTS RR-MS) (PTS RR-MS)))
  (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
(dk-have! '(IN ict_ (PTS RR-MS))
  (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
(let* ((cu (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                      (dk-contains? fm 'IS-CONTINUOUS-AT)))
                    "the pointwise continuity of f"))
       (cat (dk-apply! cu ic-ct)))
  (dk-split-all! (dk-landed* (lambda () (mac-h 'IS-CONTINUOUS-AT cat))))
  (let ((epsu (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                         (dk-contains? fm 'POS-RR)
                                         (dk-contains? fm 'DIST)))
                       "the eps universal of f")))
    (mac 'IS-CONTINUOUS-AT)
    (dk-conj-close!
     (lambda ()
       (let ((g (dk-goal)))
         (if (not (eq? (ic-head g) 'FORALL))
             (ass)
             (let* ((new (dk-landed* (lambda () (dk-peel!))))
                    (eps (cadr (car (filter (dk-head? 'POS-RR) new))))
                    (del (dk-skolem! (dk-apply! epsu eps))))
               (dk-split-all!)
               (fact 'rr-pos-rr-in-rr del)
               (fact 'rr-lt-of-pos-rr del)
               (let ((du (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                                    (dk-contains? fm del)
                                                    (dk-contains? fm 'DIST)))
                                  "the delta universal of f")))
                 (ew del)
                 (dk-conj-close!
                  (lambda ()
                    (if (eq? (ic-head (dk-goal)) 'POS-RR)
                        (ass)
                        (begin
                          (dk-peel!)
                          (let* ((bb (cadr (car (filter (lambda (fm)
                                        (and (pair? fm) (eq? (car fm) 'IN)
                                             (equal? (caddr fm) '(PTS RR-MS))
                                             (not (equal? (cadr fm) 'ict_))))
                                        (dk-asms)))))
                                 (cb (list 'CLAMP 'a 'b bb)))
                            (dk-have! (list 'IN bb 'RR)
                              (lambda () (subst '(== RR (PTS RR-MS))) (ass)))
                            (fact 'clamp-in-rr 'a 'b bb)
                            (fact 'clamp-in-ccint 'a 'b bb)
                            (fact 'rr-sub-in-rr 'ict_ bb)
                            (fact 'rr-abs-closed (list '- 'ict_ bb))
                            (fact 'rr-sub-in-rr ic-ct cb)
                            (fact 'rr-abs-closed (list '- ic-ct cb))
                            (fact 'rr-ms-dist 'ict_ bb)
                            (fact 'clamp-lipschitz 'a 'b 'ict_ bb)
                            (dk-have! (list '<= (list 'abs (list '- 'ict_ bb)) del)
                              (lambda ()
                                (subst (list '== (list 'abs (list '- 'ict_ bb))
                                             (list '(DIST RR-MS) 'ict_ bb)))
                                (ass)))
                            (dk-have! (list 'IN cb (list 'PTS ic-sub-cc))
                              (lambda () (subst (list '== (list 'PTS ic-sub-cc) ic-ci))
                                         (ass)))
                            (fact 'subspace-dist 'RR-MS ic-ci ic-ct cb)
                            (fact 'rr-ms-dist ic-ct cb)
                            (dk-have! (list '<= (list (list 'DIST ic-sub-cc) ic-ct cb) del)
                              (lambda ()
                                (subst (list '== (list (list 'DIST ic-sub-cc) ic-ct cb)
                                             (list '(DIST RR-MS) ic-ct cb)))
                                (subst (list '== (list '(DIST RR-MS) ic-ct cb)
                                             (list 'abs (list '- ic-ct cb))))
                                (dk-ineq!
                                 (list '<= (list 'abs (list '- ic-ct cb))
                                       (list 'abs (list '- 'ict_ bb)))
                                 (list '<= (list 'abs (list '- 'ict_ bb)) del)
                                 (list 'IN (list 'abs (list '- ic-ct cb)) 'RR)
                                 (list 'IN (list 'abs (list '- 'ict_ bb)) 'RR)
                                 (list 'IN del 'RR))))
                            (dk-apply! du cb)
                            (fact 'extend-const-value 'f 'a 'b 'ict_)
                            (fact 'extend-const-value 'f 'a 'b bb)
                            (subst (list '== (list ic-ext 'ict_) (list 'f ic-ct)))
                            (subst (list '== (list ic-ext bb) (list 'f cb)))
                            (ass))))))))))))))
(qed 'extend-const-continuous-at)
(topic! 'extend-const-continuous-at 'analysis)
(alias! 'extend-const-continuous-at
        "the constant extension of a continuous function is continuous everywhere")


;;; extend-const-deriv-fwd / -bwd / -iff: at an INTERIOR point the extension
;;; has exactly the derivatives f has.  No continuity is needed for this half
;;; of the extension lemma: differentiability at x only ever looks at a
;;; neighbourhood of x, and inside (a, b) the extension IS f there.  The two
;;; DIRECTIONS are separate theorems and the IFF is derived from them: `fact'
;;; of an IFF cannot be used forwards, and an IFF cited by `mac-h' on a
;;; hypothesis spawns the side conditions of its five guards.
(define (ic-ec-int rad) (list 'OOINT (list '- 'icx_ rad) (list '+ 'icx_ rad)))

(define (ic-ec-sub! rad)
  (fact 'rr-pos-rr-in-rr rad)
  (fact 'rr-lt-of-pos-rr rad)
  (fact 'rr-sub-in-rr 'icx_ rad)
  (fact 'rr-add-in-rr 'icx_ rad)
  (fact 'ooint-open-nf (list '- 'icx_ rad) (list '+ 'icx_ rad))
  (fact 'ooint-center 'icx_ rad)
  (fact 'ooint-subset-rr (list '- 'icx_ rad) (list '+ 'icx_ rad))
  (dk-have! (list 'SUBSET (ic-ec-int rad) '(CCINT a b))
    (lambda ()
      (let ((z (subset-by-element!)))
        (ic-ooint-in! z (list '- 'icx_ rad) (list '+ 'icx_ rad))
        (mac 'ccint-membership)
        (ic-conj-ineq!
         (list '(IN a RR) '(IN b RR) '(IN icx_ RR) (list 'IN z 'RR)
               (list 'IN rad 'RR) (list '< 0 rad)
               (list '<= rad '(- icx_ a)) (list '<= rad '(- b icx_))
               (list '< (list '- 'icx_ rad) z) (list '< z (list '+ 'icx_ rad))))))))

(define (ic-ec-ptwise! rad lft rgt)
  (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ (ic-ec-int rad))
              (list '== (list (list 'RESTRICT lft (ic-ec-int rad)) 'hbx_)
                        (list (list 'RESTRICT rgt (ic-ec-int rad)) 'hbx_))))
    (lambda ()
      (let ((z (dk-di-var!)))
        (fact 'subset-mem-fwd (ic-ec-int rad) '(CCINT a b) z)
        (fact 'restrict-apply lft (ic-ec-int rad) z)
        (fact 'restrict-apply rgt (ic-ec-int rad) z)
        (fact 'extend-const-ccint-fixes 'a 'b z 'f)
        (subst (list '== (list (list 'RESTRICT lft (ic-ec-int rad)) z) (list lft z)))
        (subst (list '== (list (list 'RESTRICT rgt (ic-ec-int rad)) z) (list rgt z)))
        (subst (list '== (list ic-ext z) (list 'f z)))
        (qrfl)))))

;;; the shared opening of both directions; returns the radius of an interval
;;; about icx_ that stays inside (a, b).
(define (ic-ec-common!)
  (fact 'rr-is-normed-field)
  (fact 'rr-nf-carr)
  (fact 'extend-const-in-fun 'a 'b 'f)
  (ic-ooint-in! 'icx_ 'a 'b)
  (fact 'rr-sub-in-rr 'icx_ 'a)
  (fact 'rr-sub-in-rr 'b 'icx_)
  (dk-have! '(< 0 (- icx_ a))
    (lambda () (dk-ineq! '(IN a RR) '(IN icx_ RR) '(< a icx_))))
  (dk-have! '(< 0 (- b icx_))
    (lambda () (dk-ineq! '(IN b RR) '(IN icx_ RR) '(< icx_ b))))
  (let ((rad (dk-skolem! (dk-fact! 'rr-min-pos '(- icx_ a) '(- b icx_)))))
    (dk-split-all!)
    (fact 'rr-pos-rr-of-lt rad)
    rad))

(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL b (IMPLIES (IN b RR)
   (IMPLIES (<= a b)
   (FORALL f (IMPLIES (IN f (FUN (CCINT a b) RR))
   (FORALL icx_ (IMPLIES (IN icx_ (OOINT a b))
   (FORALL icl_ (IMPLIES (HAS-DERIV-AT f icx_ icl_)
     (IS-DIFF-AT (EXTEND-CONST f a b) icx_ icl_))))))))))))))
(dk-peel!)
(let ((ic-rad (ic-ec-common!)))
  (let ((w (dk-skolem! (dk-fact! 'has-deriv-at-shrink 'f 'icx_ 'icl_ ic-rad))))
    (dk-split-all!)
    (fact 'rr-pos-rr-in-rr w)
    (fact 'rr-lt-of-pos-rr w)
    (dk-have! (list '<= w '(- icx_ a))
      (lambda () (dk-ineq! (list '<= w ic-rad) (list '<= ic-rad '(- icx_ a))
                           (list 'IN w 'RR) (list 'IN ic-rad 'RR)
                           '(IN icx_ RR) '(IN a RR))))
    (dk-have! (list '<= w '(- b icx_))
      (lambda () (dk-ineq! (list '<= w ic-rad) (list '<= ic-rad '(- b icx_))
                           (list 'IN w 'RR) (list 'IN ic-rad 'RR)
                           '(IN icx_ RR) '(IN b RR))))
    (ic-ec-sub! w)
    (fact 'restrict-in-fun ic-ext 'RR 'RR (ic-ec-int w))
    (dk-have! (list 'IN (list 'RESTRICT ic-ext (ic-ec-int w))
                    (list 'FUN (ic-ec-int w) '(CARR RR-NORMED-FIELD)))
      (lambda () (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass)))
    (ic-ec-ptwise! w ic-ext 'f)
    (fact 'diff-on-transfer-ptwise-eq 'RR-NORMED-FIELD (ic-ec-int w)
          (list 'RESTRICT ic-ext (ic-ec-int w))
          (list 'RESTRICT 'f (ic-ec-int w)) 'icx_ 'icl_)
    (fact 'diff-on-nbhd-implies-diff-at ic-ext 'icx_ w 'icl_)
    (ass)))
(qed 'extend-const-deriv-fwd)
(topic! 'extend-const-deriv-fwd 'analysis)

(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL b (IMPLIES (IN b RR)
   (IMPLIES (<= a b)
   (FORALL f (IMPLIES (IN f (FUN (CCINT a b) RR))
   (FORALL icx_ (IMPLIES (IN icx_ (OOINT a b))
   (FORALL icl_ (IMPLIES (IS-DIFF-AT (EXTEND-CONST f a b) icx_ icl_)
     (HAS-DERIV-AT f icx_ icl_))))))))))))))
(dk-peel!)
(let ((ic-rad (ic-ec-common!)))
  (ic-ec-sub! ic-rad)
  (fact 'diff-at-iff-diff-on ic-ext 'icx_ 'icl_)
  (mac-h 'diff-at-iff-diff-on (list 'IS-DIFF-AT ic-ext 'icx_ 'icl_))
  (fact 'diff-on-shrink 'RR-NORMED-FIELD 'RR ic-ext 'icx_ 'icl_ (ic-ec-int ic-rad))
  (fact 'restrict-in-fun 'f '(CCINT a b) 'RR (ic-ec-int ic-rad))
  (dk-have! (list 'IN (list 'RESTRICT 'f (ic-ec-int ic-rad))
                  (list 'FUN (ic-ec-int ic-rad) '(CARR RR-NORMED-FIELD)))
    (lambda () (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass)))
  (ic-ec-ptwise! ic-rad 'f ic-ext)
  (fact 'diff-on-transfer-ptwise-eq 'RR-NORMED-FIELD (ic-ec-int ic-rad)
        (list 'RESTRICT 'f (ic-ec-int ic-rad))
        (list 'RESTRICT ic-ext (ic-ec-int ic-rad)) 'icx_ 'icl_)
  (fact 'has-deriv-at-intro 'f 'icx_ 'icl_ ic-rad)
  (ass))
(qed 'extend-const-deriv-bwd)
(topic! 'extend-const-deriv-bwd 'analysis)

(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL b (IMPLIES (IN b RR)
   (IMPLIES (<= a b)
   (FORALL f (IMPLIES (IN f (FUN (CCINT a b) RR))
   (FORALL icx_ (IMPLIES (IN icx_ (OOINT a b))
   (FORALL icl_
     (IFF (HAS-DERIV-AT f icx_ icl_)
          (IS-DIFF-AT (EXTEND-CONST f a b) icx_ icl_))))))))))))))
(dk-peel!)
(dk-iff!
 (dk-head? 'IS-DIFF-AT)
 (lambda () (fact 'extend-const-deriv-fwd 'a 'b 'f 'icx_ 'icl_) (ass))
 (lambda () (fact 'extend-const-deriv-bwd 'a 'b 'f 'icx_ 'icl_) (ass)))
(qed 'extend-const-deriv-iff)
(topic! 'extend-const-deriv-iff 'analysis)
(alias! 'extend-const-deriv-iff
        "the constant extension has the same derivatives inside the interval")

;;; =====================================================================
;;; (7) LOCALITY.  Two functions that agree on an open interval about x have
;;; the same derivatives at x.  This is what makes HAS-DERIV-AT a LOCAL
;;; notion: it depends on neither the radius the definition happens to pick
;;; nor on the domain of f away from x.
;;;
;;; The FUN typing of the restriction is a hypothesis and is not redundant,
;;; for the reason diff-transfer.scm:42 gives: pointwise agreement with a
;;; function says nothing about f being a set of pairs at all.
;;; =====================================================================
(sp (make-wff "forall([icr_], pos-rr(icr_) implies
  forall([f, g, icx_, icl_],
    restrict(f, ooint(icx_ - icr_, icx_ + icr_))
        in fun(ooint(icx_ - icr_, icx_ + icr_), rr) implies
    forall([hbx_ in ooint(icx_ - icr_, icx_ + icr_)], f(hbx_) == g(hbx_)) implies
    has-deriv-at(g, icx_, icl_) implies
    has-deriv-at(f, icx_, icl_)))"))
(dk-peel!)
(fact 'rr-is-normed-field)
(fact 'rr-nf-carr)
(fact 'has-deriv-at-pt-in-rr 'g 'icx_ 'icl_)
(fact 'rr-pos-rr-in-rr 'icr_)
(fact 'rr-lt-of-pos-rr 'icr_)
(define ic-loc-big '(OOINT (- icx_ icr_) (+ icx_ icr_)))
(define ic-loc-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'g)
                             (dk-contains? fm 'f)))
           "the pointwise agreement"))
(let ((w (dk-skolem! (dk-fact! 'has-deriv-at-shrink 'g 'icx_ 'icl_ 'icr_))))
  (dk-split-all!)
  (fact 'rr-pos-rr-in-rr w)
  (fact 'rr-lt-of-pos-rr w)
  (fact 'rr-sub-in-rr 'icx_ w)
  (fact 'rr-add-in-rr 'icx_ w)
  (let ((v (list 'OOINT (list '- 'icx_ w) (list '+ 'icx_ w))))
    (dk-have! (list 'SUBSET v ic-loc-big)
      (lambda ()
        (let ((z (subset-by-element!)))
          (ic-ooint-in! z (list '- 'icx_ w) (list '+ 'icx_ w))
          (mac 'ooint-membership)
          (ic-conj-ineq!
           (list '(IN icx_ RR) '(IN icr_ RR) (list 'IN w 'RR) (list 'IN z 'RR)
                 (list '<= w 'icr_) (list '< 0 w) '(< 0 icr_)
                 (list '< (list '- 'icx_ w) z) (list '< z (list '+ 'icx_ w)))))))
    (fact 'restrict-in-fun-of-restrict 'f ic-loc-big 'RR v)
    (dk-have! (list 'IN (list 'RESTRICT 'f v) (list 'FUN v '(CARR RR-NORMED-FIELD)))
      (lambda () (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass)))
    (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ v)
                (list '== (list (list 'RESTRICT 'f v) 'hbx_)
                          (list (list 'RESTRICT 'g v) 'hbx_))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'subset-mem-fwd v ic-loc-big z)
          (fact 'restrict-apply 'f v z)
          (fact 'restrict-apply 'g v z)
          (dk-apply! ic-loc-agree z)
          (subst (list '== (list (list 'RESTRICT 'f v) z) (list 'f z)))
          (subst (list '== (list (list 'RESTRICT 'g v) z) (list 'g z)))
          (subst (list '== (list 'f z) (list 'g z)))
          (qrfl))))
    (fact 'diff-on-transfer-ptwise-eq 'RR-NORMED-FIELD v
          (list 'RESTRICT 'f v) (list 'RESTRICT 'g v) 'icx_ 'icl_)
    (fact 'has-deriv-at-intro 'f 'icx_ 'icl_ w)
    (ass)))
(qed 'has-deriv-at-local)
(topic! 'has-deriv-at-local 'analysis)
(alias! 'has-deriv-at-local
        "functions agreeing near a point have the same derivatives there")

;;; =====================================================================
;;; (8) THE ARITHMETIC RULES.
;;;
;;; A sum of two functions on an interval is not a term the tree can form --
;;; there is no addition on FUN(A, RR) -- so each rule is stated for ANY h that
;;; agrees with the combination on a neighbourhood of x, which is the shape
;;; every caller has in hand and is exactly what locality makes harmless.
;;; The work is done by `diff-on-sum' / `diff-on-product' (diff-on-laws-2.scm)
;;; at K = RR-NORMED-FIELD, after both derivatives have been shrunk to one
;;; common interval; what is left is turning K's own ADD and MUL into the
;;; numeric `+' and `*' (`rr-nf-add-apply', `rr-nf-mul-apply').
;;; =====================================================================

;;; shrink two derivatives at the same point to ONE common radius, at most
;;; RAD; returns that radius.
(define (ic-common-radius! fn gn rad)
  (let ((w1 (dk-skolem! (dk-fact! 'has-deriv-at-shrink fn 'icx_ 'icl_ rad))))
    (dk-split-all!)
    (fact 'rr-pos-rr-in-rr w1)
    (fact 'rr-lt-of-pos-rr w1)
    (let ((w2 (dk-skolem! (dk-fact! 'has-deriv-at-shrink gn 'icx_ 'icm_ w1))))
      (dk-split-all!)
      (fact 'rr-pos-rr-in-rr w2)
      (fact 'rr-lt-of-pos-rr w2)
      (fact 'diff-on-ooint-shrink 'icx_ w1 w2 fn 'icl_)
      (dk-have! (list '<= w2 rad)
        (lambda () (dk-ineq! (list '<= w2 w1) (list '<= w1 rad)
                             (list 'IN w2 'RR) (list 'IN w1 'RR) (list 'IN rad 'RR))))
      w2)))

(sp (make-wff "forall([icr_], pos-rr(icr_) implies
  forall([f, g, h, icx_, icl_, icm_],
    restrict(h, ooint(icx_ - icr_, icx_ + icr_))
        in fun(ooint(icx_ - icr_, icx_ + icr_), rr) implies
    forall([hbx_ in ooint(icx_ - icr_, icx_ + icr_)],
           h(hbx_) == f(hbx_) + g(hbx_)) implies
    has-deriv-at(f, icx_, icl_) implies
    has-deriv-at(g, icx_, icm_) implies
    has-deriv-at(h, icx_, icl_ + icm_)))"))
(dk-peel!)
(fact 'rr-is-normed-field)
(fact 'rr-nf-carr)
(fact 'has-deriv-at-pt-in-rr 'f 'icx_ 'icl_)
(fact 'has-deriv-at-in-rr 'f 'icx_ 'icl_)
(fact 'has-deriv-at-in-rr 'g 'icx_ 'icm_)
(fact 'rr-pos-rr-in-rr 'icr_)
(fact 'rr-lt-of-pos-rr 'icr_)
(define ic-sum-big '(OOINT (- icx_ icr_) (+ icx_ icr_)))
(define ic-sum-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'h)
                             (dk-contains? fm 'f) (dk-contains? fm 'g)))
           "the pointwise agreement"))
(let ((w (ic-common-radius! 'f 'g 'icr_)))
  (fact 'rr-sub-in-rr 'icx_ w)
  (fact 'rr-add-in-rr 'icx_ w)
  (let* ((v (list 'OOINT (list '- 'icx_ w) (list '+ 'icx_ w)))
         (rf (list 'RESTRICT 'f v))
         (rg (list 'RESTRICT 'g v))
         (lam (list 'VNB-LAMBDA 'd2x_ v
                    (list '(ADD RR-NORMED-FIELD) (list rf 'd2x_) (list rg 'd2x_)))))
    (dk-have! (list 'SUBSET v ic-sum-big)
      (lambda ()
        (let ((z (subset-by-element!)))
          (ic-ooint-in! z (list '- 'icx_ w) (list '+ 'icx_ w))
          (mac 'ooint-membership)
          (ic-conj-ineq!
           (list '(IN icx_ RR) '(IN icr_ RR) (list 'IN w 'RR) (list 'IN z 'RR)
                 (list '<= w 'icr_) (list '< 0 w) '(< 0 icr_)
                 (list '< (list '- 'icx_ w) z) (list '< z (list '+ 'icx_ w)))))))
    (fact 'restrict-in-fun-of-restrict 'h ic-sum-big 'RR v)
    (dk-have! (list 'IN (list 'RESTRICT 'h v) (list 'FUN v '(CARR RR-NORMED-FIELD)))
      (lambda () (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass)))
    (fact 'diff-on-in-fun 'RR-NORMED-FIELD v rf 'icx_ 'icl_)
    (fact 'diff-on-in-fun 'RR-NORMED-FIELD v rg 'icx_ 'icm_)
    (dk-have! (list 'IN rf (list 'FUN v 'RR))
      (lambda () (subst '(== RR (CARR RR-NORMED-FIELD))) (ass)))
    (dk-have! (list 'IN rg (list 'FUN v 'RR))
      (lambda () (subst '(== RR (CARR RR-NORMED-FIELD))) (ass)))
    (fact 'diff-on-sum 'RR-NORMED-FIELD v rf rg 'icx_ 'icl_ 'icm_)
    (fact 'rr-nf-add-apply 'icl_ 'icm_)
    (dk-have! (list 'IS-DIFF-ON 'RR-NORMED-FIELD v lam 'icx_ '(+ icl_ icm_))
      (lambda ()
        (subst '(== (+ icl_ icm_) ((ADD RR-NORMED-FIELD) icl_ icm_)))
        (ass)))
    (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ v)
                (list '== (list (list 'RESTRICT 'h v) 'hbx_) (list lam 'hbx_))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'subset-mem-fwd v ic-sum-big z)
          (fact 'ooint-elt-in-rr (list '- 'icx_ w) (list '+ 'icx_ w) z)
          (fact 'restrict-apply 'h v z)
          (fact 'restrict-apply 'f v z)
          (fact 'restrict-apply 'g v z)
          (dk-apply! ic-sum-agree z)
          (dk-lam-b!)
          (subst (list '== (list (list 'RESTRICT 'h v) z) (list 'h z)))
          (subst (list '== (list rf z) (list 'f z)))
          (subst (list '== (list rg z) (list 'g z)))
          (fact 'fun-apply-type-c (list 'RESTRICT 'f v) v 'RR z)
          (fact 'fun-apply-type-c (list 'RESTRICT 'g v) v 'RR z)
          (dk-have! (list 'IN (list 'f z) 'RR)
            (lambda () (subst (list '== (list 'f z) (list rf z))) (ass)))
          (dk-have! (list 'IN (list 'g z) 'RR)
            (lambda () (subst (list '== (list 'g z) (list rg z))) (ass)))
          (fact 'rr-nf-add-apply (list 'f z) (list 'g z))
          (subst (list '== (list '(ADD RR-NORMED-FIELD) (list 'f z) (list 'g z))
                       (list '+ (list 'f z) (list 'g z))))
          (subst (list '== (list 'h z) (list '+ (list 'f z) (list 'g z))))
          (qrfl))))
    (fact 'diff-on-transfer-ptwise-eq 'RR-NORMED-FIELD v
          (list 'RESTRICT 'h v) lam 'icx_ '(+ icl_ icm_))
    (fact 'has-deriv-at-intro 'h 'icx_ '(+ icl_ icm_) w)
    (ass)))
(qed 'has-deriv-at-sum)
(topic! 'has-deriv-at-sum 'analysis)
(alias! 'has-deriv-at-sum "the derivative of a sum is the sum of the derivatives")

;;; has-deriv-at-product: the same driver as the sum, with `diff-on-product'
;;; and three more K-to-numeric rewrites.  The notes' f'(x) g(x) + g'(x) f(x)
;;; appears as icl_ * g(icx_) + icm_ * f(icx_): the values at the point are the
;;; values of f and g themselves, by `restrict-apply'.
(sp (make-wff "forall([icr_], pos-rr(icr_) implies
  forall([f, g, h, icx_, icl_, icm_],
    restrict(h, ooint(icx_ - icr_, icx_ + icr_))
        in fun(ooint(icx_ - icr_, icx_ + icr_), rr) implies
    forall([hbx_ in ooint(icx_ - icr_, icx_ + icr_)],
           h(hbx_) == f(hbx_) * g(hbx_)) implies
    has-deriv-at(f, icx_, icl_) implies
    has-deriv-at(g, icx_, icm_) implies
    has-deriv-at(h, icx_, icl_ * g(icx_) + icm_ * f(icx_))))"))
(dk-peel!)
(fact 'rr-is-normed-field)
(fact 'rr-nf-carr)
(fact 'has-deriv-at-pt-in-rr 'f 'icx_ 'icl_)
(fact 'has-deriv-at-in-rr 'f 'icx_ 'icl_)
(fact 'has-deriv-at-in-rr 'g 'icx_ 'icm_)
(fact 'rr-pos-rr-in-rr 'icr_)
(fact 'rr-lt-of-pos-rr 'icr_)
(define ic-prod-big '(OOINT (- icx_ icr_) (+ icx_ icr_)))
(define ic-prod-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'h)
                             (dk-contains? fm 'f) (dk-contains? fm 'g)))
           "the pointwise agreement"))
(let ((w (ic-common-radius! 'f 'g 'icr_)))
  (fact 'rr-sub-in-rr 'icx_ w)
  (fact 'rr-add-in-rr 'icx_ w)
  (let* ((v (list 'OOINT (list '- 'icx_ w) (list '+ 'icx_ w)))
         (rf (list 'RESTRICT 'f v))
         (rg (list 'RESTRICT 'g v))
         (lam (list 'VNB-LAMBDA 'd2x_ v
                    (list '(MUL RR-NORMED-FIELD) (list rf 'd2x_) (list rg 'd2x_))))
         (pl (list '* 'icl_ '(g icx_)))
         (pm (list '* 'icm_ '(f icx_)))
         (ql (list '(MUL RR-NORMED-FIELD) 'icl_ (list rg 'icx_)))
         (qm (list '(MUL RR-NORMED-FIELD) 'icm_ (list rf 'icx_))))
    (dk-have! (list 'SUBSET v ic-prod-big)
      (lambda ()
        (let ((z (subset-by-element!)))
          (ic-ooint-in! z (list '- 'icx_ w) (list '+ 'icx_ w))
          (mac 'ooint-membership)
          (ic-conj-ineq!
           (list '(IN icx_ RR) '(IN icr_ RR) (list 'IN w 'RR) (list 'IN z 'RR)
                 (list '<= w 'icr_) (list '< 0 w) '(< 0 icr_)
                 (list '< (list '- 'icx_ w) z) (list '< z (list '+ 'icx_ w)))))))
    (fact 'ooint-center 'icx_ w)
    (fact 'restrict-in-fun-of-restrict 'h ic-prod-big 'RR v)
    (dk-have! (list 'IN (list 'RESTRICT 'h v) (list 'FUN v '(CARR RR-NORMED-FIELD)))
      (lambda () (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass)))
    (fact 'diff-on-in-fun 'RR-NORMED-FIELD v rf 'icx_ 'icl_)
    (fact 'diff-on-in-fun 'RR-NORMED-FIELD v rg 'icx_ 'icm_)
    (dk-have! (list 'IN rf (list 'FUN v 'RR))
      (lambda () (subst '(== RR (CARR RR-NORMED-FIELD))) (ass)))
    (dk-have! (list 'IN rg (list 'FUN v 'RR))
      (lambda () (subst '(== RR (CARR RR-NORMED-FIELD))) (ass)))
    (fact 'fun-apply-type-c rf v 'RR 'icx_)
    (fact 'fun-apply-type-c rg v 'RR 'icx_)
    (fact 'restrict-apply 'f v 'icx_)
    (fact 'restrict-apply 'g v 'icx_)
    (dk-have! '(IN (f icx_) RR)
      (lambda () (subst (list '== '(f icx_) (list rf 'icx_))) (ass)))
    (dk-have! '(IN (g icx_) RR)
      (lambda () (subst (list '== '(g icx_) (list rg 'icx_))) (ass)))
    (fact 'rr-mul-in-rr 'icl_ '(g icx_))
    (fact 'rr-mul-in-rr 'icm_ '(f icx_))
    (fact 'diff-on-product 'RR-NORMED-FIELD v rf rg 'icx_ 'icl_ 'icm_)
    (fact 'rr-nf-mul-apply 'icl_ (list rg 'icx_))
    (fact 'rr-nf-mul-apply 'icm_ (list rf 'icx_))
    (fact 'rr-mul-in-rr 'icl_ (list rg 'icx_))
    (fact 'rr-mul-in-rr 'icm_ (list rf 'icx_))
    (dk-have! (list 'IN ql 'RR)
      (lambda () (subst (list '== ql (list '* 'icl_ (list rg 'icx_)))) (ass)))
    (dk-have! (list 'IN qm 'RR)
      (lambda () (subst (list '== qm (list '* 'icm_ (list rf 'icx_)))) (ass)))
    (fact 'rr-nf-add-apply ql qm)
    (dk-have! (list 'IS-DIFF-ON 'RR-NORMED-FIELD v lam 'icx_ (list '+ pl pm))
      (lambda ()
        (subst (list '== '(g icx_) (list rg 'icx_)))
        (subst (list '== '(f icx_) (list rf 'icx_)))
        (subst (list '== (list '* 'icl_ (list rg 'icx_)) ql))
        (subst (list '== (list '* 'icm_ (list rf 'icx_)) qm))
        (subst (list '== (list '+ ql qm) (list '(ADD RR-NORMED-FIELD) ql qm)))
        (ass)))
    (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ v)
                (list '== (list (list 'RESTRICT 'h v) 'hbx_) (list lam 'hbx_))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'subset-mem-fwd v ic-prod-big z)
          (fact 'ooint-elt-in-rr (list '- 'icx_ w) (list '+ 'icx_ w) z)
          (fact 'restrict-apply 'h v z)
          (fact 'restrict-apply 'f v z)
          (fact 'restrict-apply 'g v z)
          (dk-apply! ic-prod-agree z)
          (dk-lam-b!)
          (subst (list '== (list (list 'RESTRICT 'h v) z) (list 'h z)))
          (subst (list '== (list rf z) (list 'f z)))
          (subst (list '== (list rg z) (list 'g z)))
          (fact 'fun-apply-type-c rf v 'RR z)
          (fact 'fun-apply-type-c rg v 'RR z)
          (dk-have! (list 'IN (list 'f z) 'RR)
            (lambda () (subst (list '== (list 'f z) (list rf z))) (ass)))
          (dk-have! (list 'IN (list 'g z) 'RR)
            (lambda () (subst (list '== (list 'g z) (list rg z))) (ass)))
          (fact 'rr-nf-mul-apply (list 'f z) (list 'g z))
          (subst (list '== (list '(MUL RR-NORMED-FIELD) (list 'f z) (list 'g z))
                       (list '* (list 'f z) (list 'g z))))
          (subst (list '== (list 'h z) (list '* (list 'f z) (list 'g z))))
          (qrfl))))
    (fact 'diff-on-transfer-ptwise-eq 'RR-NORMED-FIELD v
          (list 'RESTRICT 'h v) lam 'icx_ (list '+ pl pm))
    (fact 'has-deriv-at-intro 'h 'icx_ (list '+ pl pm) w)
    (ass)))
(qed 'has-deriv-at-product)
(topic! 'has-deriv-at-product 'analysis)
(alias! 'has-deriv-at-product "the product rule for the derivative at a point")
