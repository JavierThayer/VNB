;;; road-laws.scm -- the laws of IS-PW-CONTINUOUS-ON, IS-PATH and IS-ROAD
;;; (structure-library/path-integral.scm), section 3.4 of
;;; docs/paths-and-line-integrals-2026-09-21.md and Dieudonne 9.6.
;;;
;;; STAGE 1: the read-offs of the three predicates, and the one-piece
;;;   introduction rule for IS-PW-CONTINUOUS-ON.
;;; STAGE 2: `is-path-of-coords' -- a map into CC is a path when both its
;;;   coordinate maps are continuous on the interval (the transfer form of
;;;   `cc-continuous-at-iff-coords').
;;; STAGE 3: THE WITNESS.  The line segment t |-> z0 + t*w on [0,1], with
;;;   dgamma the constant w, is a ROAD.  This is what makes IS-PATH and IS-ROAD
;;;   non-vacuous.
;;;
;;; THE EXCEPTIONAL SET IS A SET (batch 16, 2026-09-22).  Both introduction
;;; rules below -- `pw-continuous-one-piece' and, through
;;; `pw-affine-antiderivative', the segment -- take the exceptional set EMPTY.
;;; The two-point partition that the first draft of this file used is gone with
;;; the partitions; `empty-set-is-set', `card-empty' and `empty-subset-any' are
;;; what replace it, and they are three citations instead of a lemma.
;;;
;;; Helper prefix: rd-.
;;;
;;; Dependencies: structure-library/path-integral.scm;
;;; theorem-library/pw-antiderivative-laws.scm (pw-affine-antiderivative,
;;; pw-restrict-continuous-on, pw-antiderivative-continuous); cc-int-laws.scm;
;;; cc-coords-laws.scm (cc-continuous-at-iff-coords); cc-real-imag.scm
;;; (real-part-in-rr, imag-part-in-rr); cc-complete-proof.scm (cc-re-add,
;;; cc-re-real-mul and their imaginary twins are proven in cc-coords-laws.scm);
;;; metric-subspace-laws.scm; ccint-basics.scm; monotone-inverse.scm
;;; (ccint-subset-rr); number-systems (rr-subset-cc, cc-add-closed,
;;; cc-mul-closed, rr-zero-lt-one).

;;; ---- file-local driver helpers ---------------------------------------

(define (rd-head g) (and (pair? g) (car g)))

(define rd-cc '(CCINT a b))
(define rd-sub (list 'SUBSPACE-MS 'RR-MS rd-cc))

;;; the three citations that make EMPTY-SET a legitimate exceptional set.
(define (rd-empty-set! dom)
  (fact 'empty-set-is-set)
  (fact 'nn-zero-in)
  (fact 'card-empty)
  (dk-have! '(IN (CARD EMPTY-SET) NN)
    (lambda () (subst '(= (CARD EMPTY-SET) 0)) (ass)))
  (fact 'empty-subset-any dom))

(define (rd-open! name form)
  (dk-split-all! (dk-landed* (lambda () (mac-h name form)))))

;;; unfold IS-CONTINUOUS-ON on the interval and return its POINTWISE universal.
;;; `mac-h' lands ONE formula, the nested AND: it has to be SPLIT before the
;;; universal can be picked out of it.
(define (rd-cont-univ-of! f)
  (car (filter (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                 (dk-contains? fm 'IS-CONTINUOUS-AT)))
               (dk-split-all!
                (dk-landed* (lambda ()
                  (mac-h 'IS-CONTINUOUS-ON (list 'IS-CONTINUOUS-ON f rd-cc))))))))

;;; =====================================================================
;;; (1) THE READ-OFFS.
;;; =====================================================================

(sp (make-wff '(FORALL pphi_ (FORALL a (FORALL b
   (IMPLIES (IS-PW-CONTINUOUS-ON pphi_ a b)
            (AND (IN a RR) (AND (IN b RR) (< a b)))))))))
(dk-peel!)
(rd-open! 'IS-PW-CONTINUOUS-ON '(IS-PW-CONTINUOUS-ON pphi_ a b))
(dk-conj-close! (lambda () (ass)))
(qed 'pw-continuous-endpoints)
(topic! 'pw-continuous-endpoints 'analysis)

(sp (make-wff '(FORALL pphi_ (FORALL a (FORALL b
   (IMPLIES (IS-PW-CONTINUOUS-ON pphi_ a b)
            (IN pphi_ (FUN (CCINT a b) RR))))))))
(dk-peel!)
(rd-open! 'IS-PW-CONTINUOUS-ON '(IS-PW-CONTINUOUS-ON pphi_ a b))
(ass)
(qed 'pw-continuous-in-fun)
(topic! 'pw-continuous-in-fun 'analysis)

(sp (make-wff '(FORALL pgam (FORALL a (FORALL b
   (IMPLIES (IS-PATH pgam a b)
            (AND (IN a RR) (AND (IN b RR) (< a b)))))))))
(dk-peel!)
(rd-open! 'IS-PATH '(IS-PATH pgam a b))
(dk-conj-close! (lambda () (ass)))
(qed 'is-path-endpoints)
(topic! 'is-path-endpoints 'analysis)

(sp (make-wff '(FORALL pgam (FORALL a (FORALL b
   (IMPLIES (IS-PATH pgam a b) (IN pgam (FUN (CCINT a b) CC))))))))
(dk-peel!)
(rd-open! 'IS-PATH '(IS-PATH pgam a b))
(ass)
(qed 'is-path-in-fun)
(topic! 'is-path-in-fun 'analysis)

(sp (make-wff '(FORALL pgam (FORALL a (FORALL b
   (IMPLIES (IS-PATH pgam a b)
     (FORALL pax_ (IMPLIES (IN pax_ (CCINT a b))
       (IS-CONTINUOUS-AT (SUBSPACE-MS RR-MS (CCINT a b)) CC-MS pgam pax_)))))))))
(dk-peel!)
(rd-open! 'IS-PATH '(IS-PATH pgam a b))
;; dk-peel! has already peeled the CONCLUSION's universal, so the goal is the
;; instance and the unfolded hypothesis is the universal: apply it.
(let ((z (list-ref (dk-goal) 4)))
  (dk-apply! (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                        (dk-contains? fm 'IS-CONTINUOUS-AT)))
                      "the continuity universal")
             z)
  (ass))
(qed 'is-path-continuous)
(topic! 'is-path-continuous 'analysis)
(alias! 'is-path-continuous "a path is continuous at every point of its interval")

(sp (make-wff '(FORALL pgam (FORALL dgam (FORALL a (FORALL b
   (IMPLIES (IS-ROAD pgam dgam a b) (IS-PATH pgam a b))))))))
(dk-peel!)
(rd-open! 'IS-ROAD '(IS-ROAD pgam dgam a b))
(ass)
(qed 'is-road-is-path)
(topic! 'is-road-is-path 'analysis)
(alias! 'is-road-is-path "a road is a path")

(sp (make-wff '(FORALL pgam (FORALL dgam (FORALL a (FORALL b
   (IMPLIES (IS-ROAD pgam dgam a b) (IN dgam (FUN (CCINT a b) CC)))))))))
(dk-peel!)
(rd-open! 'IS-ROAD '(IS-ROAD pgam dgam a b))
(ass)
(qed 'is-road-dgam-in-fun)
(topic! 'is-road-dgam-in-fun 'analysis)

;;; the two conjuncts the value theorem of a line integral consumes: each
;;; coordinate of gamma is a piecewise antiderivative of the corresponding
;;; coordinate of dgamma.
(sp (make-wff '(FORALL pgam (FORALL dgam (FORALL a (FORALL b
   (IMPLIES (IS-ROAD pgam dgam a b)
     (IS-PW-ANTIDERIVATIVE
       (VNB-LAMBDA pat_ (CCINT a b) (real-part (pgam pat_)))
       (VNB-LAMBDA pat_ (CCINT a b) (real-part (dgam pat_))) a b))))))))
(dk-peel!)
(rd-open! 'IS-ROAD '(IS-ROAD pgam dgam a b))
(ass)
(qed 'is-road-re-antiderivative)
(topic! 'is-road-re-antiderivative 'analysis)

(sp (make-wff '(FORALL pgam (FORALL dgam (FORALL a (FORALL b
   (IMPLIES (IS-ROAD pgam dgam a b)
     (IS-PW-ANTIDERIVATIVE
       (VNB-LAMBDA pat_ (CCINT a b) (imag-part (pgam pat_)))
       (VNB-LAMBDA pat_ (CCINT a b) (imag-part (dgam pat_))) a b))))))))
(dk-peel!)
(rd-open! 'IS-ROAD '(IS-ROAD pgam dgam a b))
(ass)
(qed 'is-road-im-antiderivative)
(topic! 'is-road-im-antiderivative 'analysis)

;;; =====================================================================
;;; (2) A CONTINUOUS FUNCTION ON [a,b] IS PIECEWISE CONTINUOUS.  The
;;; introduction rule; the exceptional set is EMPTY.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr], a < b implies
  forall([pphi_],
    pphi_ in fun(ccint(a,b), rr) implies
    is-continuous-on(pphi_, ccint(a,b)) implies
    is-pw-continuous-on(pphi_, a, b)))"))
(dk-peel!)
(rd-empty-set! rd-cc)
(define rd-cont-univ (rd-cont-univ-of! 'pphi_))
(fact 'ooint-subset-ccint 'a 'b)
(mac 'IS-PW-CONTINUOUS-ON)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (rd-head (dk-goal)) 'FORSOME))
       (ass)
       (begin
         (ew 'EMPTY-SET)
         (dk-conj-close!
          (lambda ()
            (if (not (eq? (rd-head (dk-goal)) 'FORALL))
                (ass)
                (begin
                  (dk-peel!)
                  (let ((tv (list-ref (dk-goal) 4)))
                    (fact 'subset-mem-fwd '(OOINT a b) rd-cc tv)
                    (dk-apply! rd-cont-univ tv)
                    (ass))))))))))
(qed 'pw-continuous-one-piece)
(topic! 'pw-continuous-one-piece 'analysis)
(alias! 'pw-continuous-one-piece
        "a function continuous on a closed interval is piecewise continuous on it")

;;; =====================================================================
;;; (3) A MAP INTO CC WITH CONTINUOUS COORDINATES IS A PATH.
;;;
;;; The transfer form of `cc-continuous-at-iff-coords' (cc-coords-laws.scm) on
;;; the metric SUBSPACE of the interval: the coordinate maps are GIVEN, agreeing
;;; pointwise with re o gamma and im o gamma, so no consumer owes a
;;; beta-reduction under a binder.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr], a < b implies
  forall([pgam, pgr_, pgi_],
    pgam in fun(ccint(a,b), cc) implies
    pgr_ in fun(ccint(a,b), rr) implies
    pgi_ in fun(ccint(a,b), rr) implies
    forall([pay_ in ccint(a,b)], real-part(pgam(pay_)) = pgr_(pay_)) implies
    forall([pay_ in ccint(a,b)], imag-part(pgam(pay_)) = pgi_(pay_)) implies
    is-continuous-on(pgr_, ccint(a,b)) implies
    is-continuous-on(pgi_, ccint(a,b)) implies
    is-path(pgam, a, b)))"))
(dk-peel!)
(fact 'rr-is-metric-space)
(define rd-re-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'real-part)))
           "the real-part agreement"))
(define rd-im-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'imag-part)))
           "the imaginary-part agreement"))
(define rd-re-cont (rd-cont-univ-of! 'pgr_))
(define rd-im-cont (rd-cont-univ-of! 'pgi_))
(dk-have! '(SUBSET (CCINT a b) (PTS RR-MS))
  (lambda () (slot 'PTS) (fact 'ccint-subset-rr 'a 'b) (ass)))
(fact 'subspace-is-metric-space 'RR-MS rd-cc)
(fact 'subspace-pts 'RR-MS rd-cc)
(define (rd-to-pts! f cod)
  (dk-have! (list 'IN f (list 'FUN (list 'PTS rd-sub) cod))
    (lambda () (subst (list '== (list 'PTS rd-sub) rd-cc)) (ass))))
(rd-to-pts! 'pgam 'CC)
(rd-to-pts! 'pgr_ 'RR)
(rd-to-pts! 'pgi_ 'RR)
(define (rd-pts-univ! proj agree)
  (dk-have! (list 'FORALL 'u_ (list 'IMPLIES (list 'IN 'u_ (list 'PTS rd-sub))
              (list '= (list proj '(pgam u_))
                    (list (if (eq? proj 'real-part) 'pgr_ 'pgi_) 'u_))))
    (lambda ()
      (let ((y (dk-di-var!)))
        (dk-have! (list 'IN y rd-cc)
          (lambda () (subst (list '== rd-cc (list 'PTS rd-sub))) (ass)))
        (dk-apply! agree y)
        (ass)))))
(rd-pts-univ! 'real-part rd-re-agree)
(rd-pts-univ! 'imag-part rd-im-agree)
(mac 'IS-PATH)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (rd-head (dk-goal)) 'FORALL))
       (ass)
       (let ((z (dk-di-var!)))
         ;; the GOAL here holds PTS(subspace) and the context holds CCINT, so
         ;; the rewrite must go PTS -> CCINT.  The other direction rewrites the
         ;; CCINT that sits INSIDE the subspace term as well and nests it.
         (dk-have! (list 'IN z (list 'PTS rd-sub))
           (lambda () (subst (list '== (list 'PTS rd-sub) rd-cc)) (ass)))
         (dk-apply! rd-re-cont z)
         (dk-apply! rd-im-cont z)
         (fact 'cc-continuous-at-iff-coords rd-sub 'pgam 'pgr_ 'pgi_ z)
         (have! (list 'AND (list 'IS-CONTINUOUS-AT rd-sub 'RR-MS 'pgr_ z)
                      (list 'IS-CONTINUOUS-AT rd-sub 'RR-MS 'pgi_ z)))
         ;; the goal IS the left side of the iff, so a `have!' of it would be a
         ;; silent self-loop: narrow the context to the iff and the conjunction
         ;; -- `prop' has an atom cap and a deep context drops the relevant
         ;; pair -- and decide it there.
         (dk-only! (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'IFF)))
                            "the coordinate iff")
                   (list 'AND (list 'IS-CONTINUOUS-AT rd-sub 'RR-MS 'pgr_ z)
                         (list 'IS-CONTINUOUS-AT rd-sub 'RR-MS 'pgi_ z)))
         (prop)))))
(qed 'is-path-of-coords)
(topic! 'is-path-of-coords 'analysis)
(alias! 'is-path-of-coords
        "a map into the plane with continuous coordinates is a path")

;;; =====================================================================
;;; (4) THE WITNESS: THE LINE SEGMENT IS A ROAD.
;;;
;;;     gamma(t) = z0 + t*w,   dgamma(t) = w,   on [0, 1]
;;;
;;; Dieudonne 9.6's first example, and the first road every computation in the
;;; notes' chapter 3 uses.  It makes IS-PATH, IS-ROAD, IS-PW-CONTINUOUS-ON and
;;; IS-PW-ANTIDERIVATIVE all NON-VACUOUS at once, and each coordinate of it is
;;; the AFFINE case of `pw-affine-antiderivative'.
;;;
;;; THE BINDER OF THE SEGMENT IS `psx_', NOT `pat_'.  IS-ROAD's own body builds
;;; the coordinate maps as (VNB-LAMBDA pat_ (CCINT a b) (real-part (gamma
;;; pat_))); with `pat_' as the segment's binder too, `subst-free' would rename
;;; one of the two and every later `equal?' lookup of the rebuilt term would
;;; silently miss (CLAUDE.md, "Writing proof drivers").
;;; =====================================================================
(define rd-01 '(CCINT 0 1))
(define rd-gam (list 'VNB-LAMBDA 'psx_ rd-01 '(+ pz0_ (* psx_ pzw_))))
(define rd-dgm (list 'VNB-LAMBDA 'psx_ rd-01 'pzw_))
(define (rd-coord proj f) (list 'VNB-LAMBDA 'pat_ rd-01 (list proj (list f 'pat_))))
(define rd-gr (rd-coord 'real-part rd-gam))
(define rd-gi (rd-coord 'imag-part rd-gam))
(define rd-dr (rd-coord 'real-part rd-dgm))
(define rd-di (rd-coord 'imag-part rd-dgm))

(sp (make-wff (forall-guarded '(pz0_ pzw_) '((IN pz0_ CC) (IN pzw_ CC))
                (list 'IS-ROAD rd-gam rd-dgm 0 1))))
(dk-peel!)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 0 1)
(fact 'subclass-of-set-is-set rd-01 'RR)
(fact 'real-part-in-rr 'pz0_)
(fact 'imag-part-in-rr 'pz0_)
(fact 'real-part-in-rr 'pzw_)
(fact 'imag-part-in-rr 'pzw_)

;;; t in [0,1] gives t in RR and t in CC, and the value of the segment there.
(define (rd-seg-point! z)
  (fact 'ccint-elt-in-rr 0 1 z)
  (fact 'rr-subset-cc z)
  (have! (list 'AND (list 'IN z 'CC) '(IN pzw_ CC)))
  (fact 'cc-mul-closed z 'pzw_)
  (have! (list 'AND '(IN pz0_ CC) (list 'IN (list '* z 'pzw_) 'CC)))
  (fact 'cc-add-closed 'pz0_ (list '* z 'pzw_)))

;;; the segment and its derivative are functions on [0,1] into CC.
(dk-have! (list 'IN rd-gam (list 'FUN rd-01 'CC))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (rd-head (dk-goal)) 'FORALL))
           (ass)
           (let ((z (dk-di-var!))) (rd-seg-point! z) (ass))))
     (dk-opened (lambda () (lam-t))))))
(dk-have! (list 'IN rd-dgm (list 'FUN rd-01 'CC))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (rd-head (dk-goal)) 'FORALL))
           (ass)
           (let ((z (dk-di-var!))) (ass))))
     (dk-opened (lambda () (lam-t))))))

;;; each coordinate map is a function on [0,1] into RR.
(define (rd-coord-in-fun! lam proj src)
  (dk-have! (list 'IN lam (list 'FUN rd-01 'RR))
    (lambda ()
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (not (eq? (rd-head (dk-goal)) 'FORALL))
             (ass)
             (let ((z (dk-di-var!)))
               (rd-seg-point! z)
               (fact 'fun-apply-type-c src rd-01 'CC z)
               (fact (if (eq? proj 'real-part) 'real-part-in-rr 'imag-part-in-rr)
                     (list src z))
               (ass))))
       (dk-opened (lambda () (lam-t)))))))
(rd-coord-in-fun! rd-gr 'real-part rd-gam)
(rd-coord-in-fun! rd-gi 'imag-part rd-gam)
(rd-coord-in-fun! rd-dr 'real-part rd-dgm)
(rd-coord-in-fun! rd-di 'imag-part rd-dgm)

;;; THE COORDINATE VALUES.  re(gamma(t)) = re(z0) + re(w)*t and
;;; im(gamma(t)) = im(z0) + im(w)*t, by cc-re-add / cc-re-real-mul; the
;;; commutation to the `c + m*t' shape pw-affine-antiderivative asks for is one
;;; `crs'.
(define (rd-gam-value! lam proj addlaw mullaw c m)
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ rd-01)
              (list '== (list lam 'pay_) (list '+ c (list '* m 'pay_)))))
    (lambda ()
      (let ((z (dk-di-var!)))
        (rd-seg-point! z)
        (dk-lam-b!)
        (fact addlaw 'pz0_ (list '* z 'pzw_))
        (fact mullaw z 'pzw_)
        (subst (list '= (list proj (list '+ 'pz0_ (list '* z 'pzw_)))
                     (list '+ (list proj 'pz0_) (list proj (list '* z 'pzw_)))))
        (subst (list '= (list proj (list '* z 'pzw_)) (list '* z (list proj 'pzw_))))
        (have! (list '= (list '+ (list proj 'pz0_) (list '* z (list proj 'pzw_)))
                     (list '+ c (list '* m z)))
               (lambda () (crs)))
        (subst (list '= (list '+ (list proj 'pz0_) (list '* z (list proj 'pzw_)))
                     (list '+ c (list '* m z))))
        (qrfl)))))
(rd-gam-value! rd-gr 'real-part 'cc-re-add 'cc-re-real-mul
               '(real-part pz0_) '(real-part pzw_))
(rd-gam-value! rd-gi 'imag-part 'cc-im-add 'cc-im-real-mul
               '(imag-part pz0_) '(imag-part pzw_))

;;; the derivative's coordinates are the constants re(w), im(w).
(define (rd-dgm-value! lam c)
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ rd-01)
              (list '== (list lam 'pay_) c)))
    (lambda ()
      (let ((z (dk-di-var!)))
        (fact 'ccint-elt-in-rr 0 1 z)
        (dk-lam-b!)
        (qrfl)))))
(rd-dgm-value! rd-dr '(real-part pzw_))
(rd-dgm-value! rd-di '(imag-part pzw_))

;;; each coordinate of gamma is a piecewise antiderivative of the corresponding
;;; coordinate of dgamma -- the AFFINE witness.
(fact 'pw-affine-antiderivative 0 1 '(real-part pz0_) '(real-part pzw_) rd-gr rd-dr)
(fact 'pw-affine-antiderivative 0 1 '(imag-part pz0_) '(imag-part pzw_) rd-gi rd-di)
(fact 'pw-antiderivative-continuous rd-gr rd-dr 0 1)
(fact 'pw-antiderivative-continuous rd-gi rd-di 0 1)

;;; dgamma's coordinates are constant, hence continuous on [0,1], hence
;;; piecewise continuous.
(define (rd-dgm-pw-continuous! lam c)
  (let ((tot (list 'VNB-LAMBDA 'x 'RR c)))
    (fact 'const-lam-in-fun c)
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES '(IN pay_ RR)
                (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS tot 'pay_)))
      (lambda ()
        (let ((z (dk-di-var!))) (fact 'const-continuous-at c z) (ass))))
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ rd-01)
                (list '== (list lam 'pay_) (list tot 'pay_))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'ccint-elt-in-rr 0 1 z)
          (dk-lam-b!)
          (qrfl))))
    (fact 'pw-restrict-continuous-on 0 1 tot lam)
    (fact 'pw-continuous-one-piece 0 1 lam)))
(rd-dgm-pw-continuous! rd-dr '(real-part pzw_))
(rd-dgm-pw-continuous! rd-di '(imag-part pzw_))

;;; the segment is a PATH: its coordinates are continuous on [0,1].
(define (rd-path-coord-eq! lam proj)
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ rd-01)
              (list '= (list proj (list rd-gam 'pay_)) (list lam 'pay_))))
    (lambda ()
      (let ((z (dk-di-var!)))
        (rd-seg-point! z)
        (fact (if (eq? proj 'real-part) 'real-part-in-rr 'imag-part-in-rr)
              (list '+ 'pz0_ (list '* z 'pzw_)))
        (dk-lam-b!)
        (rfl)))))
(rd-path-coord-eq! rd-gr 'real-part)
(rd-path-coord-eq! rd-gi 'imag-part)
(fact 'is-path-of-coords 0 1 rd-gam rd-gr rd-gi)

;;; ... and everything IS-ROAD asks for is now in the context.
(mac 'IS-ROAD)
(dk-conj-close! (lambda () (ass)))
(qed 'segment-is-road)
(topic! 'segment-is-road 'analysis)
(alias! 'segment-is-road
        "the line segment from z0 in the direction w is a road on [0,1]")

;;; =====================================================================
;;; (5) THE FIRST COMPUTATION: THE INTEGRAL OF THE CONSTANT 1 ALONG A ROAD.
;;;
;;;     LINE-INT(1, gamma, dgamma, a, b)  =  gamma(b) - gamma(a)
;;;
;;; Dieudonne 9.6 and the identity every later computation of chapter 3 of the
;;; notes reduces to.  The proof is the definition run backwards: the integrand
;;; t |-> 1 * dgamma(t) agrees pointwise with dgamma, so each coordinate's
;;; integral is the corresponding coordinate of gamma at the endpoints
;;; (`pw-int-value' on the two IS-PW-ANTIDERIVATIVE conjuncts of IS-ROAD), and
;;; `cc-re-im-decompose' puts the two coordinates back together.
;;;
;;; `pf' is ANY function whose value on the trace is 1; the constant map is the
;;; instance, and taking it as a hypothesis spares the caller a beta-reduction.
;;; =====================================================================

;;; the coordinate lambda of a term, in the spelling CC-INT's own body builds.
(define (rd-proj proj f) (list 'VNB-LAMBDA 'pat_ rd-cc (list proj (list f 'pat_))))

(define rd-integ
  (list 'VNB-LAMBDA 'pat_ rd-cc '(* (pf (pgam pat_)) (dgam pat_))))

(sp (make-wff "forall([pgam, dgam, a, b, pf, pad_],
   is-road(pgam, dgam, a, b) implies
   pf in fun(pad_, cc) implies
   subset(trace(pgam, a, b), pad_) implies
   forall([pay_ in pad_], pf(pay_) = 1) implies
   line-int(pf, pgam, dgam, a, b) = pgam(b) - pgam(a))"))
(dk-peel!)
(define rd-pfval
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pf)))
           "the value of the integrand"))
(fact 'is-road-is-path 'pgam 'dgam 'a 'b)
(fact 'is-path-in-fun 'pgam 'a 'b)
(fact 'is-road-dgam-in-fun 'pgam 'dgam 'a 'b)
(dk-split! (dk-fact! 'is-path-endpoints 'pgam 'a 'b))
(dk-split-all!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set rd-cc 'RR)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(fact 'rr-lt-implies-le 'a 'b)
(define (rd-endpoint! z)
  (dk-have! (list 'IN z rd-cc)
    (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass))))))
(rd-endpoint! 'a)
(rd-endpoint! 'b)
(fact 'fun-apply-type-c 'pgam rd-cc 'CC 'a)
(fact 'fun-apply-type-c 'pgam rd-cc 'CC 'b)
(fact 'line-int-integrand-in-fun 'a 'b 'pgam 'dgam 'pf 'pad_)
(fact 'is-road-re-antiderivative 'pgam 'dgam 'a 'b)
(fact 'is-road-im-antiderivative 'pgam 'dgam 'a 'b)

;;; the value of the integrand at a point of the interval: 1 * dgamma(t).
(define (rd-point! z)
  (fact 'fun-apply-type-c 'pgam rd-cc 'CC z)
  (fact 'trace-value-in 'pgam 'a 'b z)
  (fact 'subset-mem-fwd '(TRACE pgam a b) 'pad_ (list 'pgam z))
  (fact 'fun-apply-type-c 'pf 'pad_ 'CC (list 'pgam z))
  (fact 'fun-apply-type-c 'dgam rd-cc 'CC z)
  (have! (list 'AND (list 'IN (list 'pf (list 'pgam z)) 'CC)
               (list 'IN (list 'dgam z) 'CC)))
  (fact 'cc-mul-closed (list 'pf (list 'pgam z)) (list 'dgam z))
  (dk-apply! rd-pfval (list 'pgam z)))

;;; ONE COORDINATE.  Lands
;;;     PW-INT(<the coordinate of the integrand>, a, b)
;;;        =  proj(gamma(b)) - proj(gamma(a))
(define (rd-coord! proj inr lam1)
  (let ((gl (rd-proj proj 'pgam))
        (dl (rd-proj proj 'dgam)))
    ;; the coordinate of the integrand is a function on the interval
    (dk-have! (list 'IN lam1 (list 'FUN rd-cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (rd-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (rd-point! z)
                 (dk-lam-b!)
                 (fact inr (list '* (list 'pf (list 'pgam z)) (list 'dgam z)))
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    ;; ... and it agrees pointwise with the coordinate of dgamma
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ rd-cc)
                (list '== (list dl 'pay_) (list lam1 'pay_))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (rd-point! z)
          (dk-lam-b!)
          (subst (list '= (list 'pf (list 'pgam z)) 1))
          (have! (list '= (list '* 1 (list 'dgam z)) (list 'dgam z))
                 (lambda () (crs)))
          (subst (list '= (list '* 1 (list 'dgam z)) (list 'dgam z)))
          (qrfl))))
    (fact 'pw-int-congruence gl dl lam1 'a 'b)
    (fact 'pw-int-value gl dl 'a 'b)
    (fact inr '(pgam a))
    (fact inr '(pgam b))
    (dk-have! (list '= (list gl 'a) (list proj '(pgam a)))
      (lambda () (dk-lam-b!) (rfl)))
    (dk-have! (list '= (list gl 'b) (list proj '(pgam b)))
      (lambda () (dk-lam-b!) (rfl)))
    (dk-have! (list '= (list 'PW-INT lam1 'a 'b)
                    (list '- (list proj '(pgam b)) (list proj '(pgam a))))
      (lambda ()
        (subst (list '= (list proj '(pgam b)) (list gl 'b)))
        (subst (list '= (list proj '(pgam a)) (list gl 'a)))
        (subst (list '= (list 'PW-INT lam1 'a 'b) (list 'PW-INT dl 'a 'b)))
        (ass)))))

(mac 'LINE-INT)
(mac 'CC-INT)
(let* ((g   (dk-goal))
       (lhs (cadr g))
       (re1 (cadr (cadr lhs)))
       (im1 (cadr (cadr (caddr lhs)))))
  (rd-coord! 'real-part 'real-part-in-rr re1)
  (rd-coord! 'imag-part 'imag-part-in-rr im1)
  (subst (list '= (list 'PW-INT re1 'a 'b)
               '(- (real-part (pgam b)) (real-part (pgam a)))))
  (subst (list '= (list 'PW-INT im1 'a 'b)
               '(- (imag-part (pgam b)) (imag-part (pgam a)))))
  ;; the two coordinates put back together
  (fact 'cc-sub-in-cc '(pgam b) '(pgam a))
  (fact 'cc-re-sub '(pgam b) '(pgam a))
  (fact 'cc-im-sub '(pgam b) '(pgam a))
  (fact 'cc-re-im-decompose '(- (pgam b) (pgam a)))
  (fact 'real-part-in-rr '(- (pgam b) (pgam a)))
  (fact 'imag-part-in-rr '(- (pgam b) (pgam a)))
  (subst '(= (- (real-part (pgam b)) (real-part (pgam a)))
             (real-part (- (pgam b) (pgam a)))))
  (subst '(= (- (imag-part (pgam b)) (imag-part (pgam a)))
             (imag-part (- (pgam b) (pgam a)))))
  ;; `cc-re-im-decompose' writes  z = re(z) + 1i * im(z)  and CC-INT's body
  ;; writes  ... + PW-INT(...) * 1i : one commutation.
  (fact 'cc-i-in)
  (fact 'rr-subset-cc '(imag-part (- (pgam b) (pgam a))))
  (have! '(AND (IN (imag-part (- (pgam b) (pgam a))) CC) (IN +i CC)))
  (fact 'cc-mul-comm '(imag-part (- (pgam b) (pgam a))) '+i)
  (subst '(= (* (imag-part (- (pgam b) (pgam a))) +i)
             (* +i (imag-part (- (pgam b) (pgam a))))))
  (fact 'eq-sym '(- (pgam b) (pgam a))
        '(+ (real-part (- (pgam b) (pgam a)))
            (* +i (imag-part (- (pgam b) (pgam a))))))
  (ass))
(qed 'line-int-of-one)
(topic! 'line-int-of-one 'analysis)
(alias! 'line-int-of-one
        "the integral of 1 along a road is the difference of the endpoints")
