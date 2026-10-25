;;; product2-hopf.scm -- Prop. 1.22 of the complex-analysis notes in its literal
;;; form: "pi is continuous C^2 -> C x R", with C^2 = PRODUCT2-MS(CC-MS, CC-MS)
;;; and C x R = PRODUCT2-MS(CC-MS, RR-MS).  Helper prefix p2h-.
;;;
;;;   product2-cc-cc-pts           PTS(PRODUCT2-MS(CC-MS, CC-MS)) == CARTESIAN(CC, CC)
;;;   product2-cc-rr-pts           PTS(PRODUCT2-MS(CC-MS, RR-MS)) == CARTESIAN(CC, RR)
;;;   hopf-map-continuous-at-product  pi continuous at every w of C^2
;;;   hopf-map-continuous-product     IS-CONTINUOUS(C^2, C x R, pi)
;;;
;;; The map pi is the lambda w |-> HOPF-MAP(w) on CARTESIAN(CC, CC) (HOPF-MAP is a
;;; def-functoid, not a function).  ASSEMBLY, no epsilon: the two projections of
;;; C^2 are continuous (product2-fst/snd-continuous-at); CA-HOPF's
;;; hopf-map-continuous at s := C^2, u1, u2 := the projections gives the two
;;; coordinates of pi continuous; the pairing property (product2-pair-continuous-at)
;;; puts them together.  The one computation is the pointwise identity
;;; pi(w) = [pi([w1, w2])_1, pi([w1, w2])_2].
;;;
;;; Needs CA-HOPF (structure-library/ca-hopf-vocab, theorem-library/ca-hopf-fibration)
;;; and the PRODUCT2 files; library complex-analysis.

(define P2H-S '(PRODUCT2-MS CC-MS CC-MS))
(define P2H-T '(PRODUCT2-MS CC-MS RR-MS))
(define P2H-U1 '(VNB-LAMBDA p2hz_ (CARTESIAN CC CC) (NTH 1 p2hz_)))
(define P2H-U2 '(VNB-LAMBDA p2hz_ (CARTESIAN CC CC) (NTH 2 p2hz_)))
(define P2H-HF '(VNB-LAMBDA p2hv_ (CARTESIAN CC CC) (HOPF-MAP p2hv_)))
;;; the two coordinate maps hopf-map-continuous speaks of, at s := C^2, u1, u2 := U1, U2
(define P2H-F1 (list 'VNB-LAMBDA 'hcz_ (list 'PTS P2H-S)
                 (list 'NTH 1 (list 'HOPF-MAP (list 'LIST (list P2H-U1 'hcz_) (list P2H-U2 'hcz_))))))
(define P2H-F2 (list 'VNB-LAMBDA 'hcz_ (list 'PTS P2H-S)
                 (list 'NTH 2 (list 'HOPF-MAP (list 'LIST (list P2H-U1 'hcz_) (list P2H-U2 'hcz_))))))

;;; =====================================================================
(sp (make-wff '(== (PTS (PRODUCT2-MS CC-MS CC-MS)) (CARTESIAN CC CC))))
(fact 'cc-is-metric-space)
(mac 'product2-pts)
(slot 'PTS)
(qrfl)
(qed 'product2-cc-cc-pts)
(topic! 'product2-cc-cc-pts 'constructions)
(alias! 'product2-cc-cc-pts "the points of C^2 with the max metric are the complex pairs")

(sp (make-wff '(== (PTS (PRODUCT2-MS CC-MS RR-MS)) (CARTESIAN CC RR))))
(fact 'cc-is-metric-space)
(fact 'rr-is-metric-space)
(mac 'product2-pts)
(slot 'PTS)
(qrfl)
(qed 'product2-cc-rr-pts)
(topic! 'product2-cc-rr-pts 'constructions)
(alias! 'product2-cc-rr-pts "the points of C x R with the max metric are the pairs [z, r]")

;;; =====================================================================
;;; Helpers.
;;; =====================================================================
(define (p2h-set-facts!)
  (fact 'cc-is-set) (fact 'rr-is-set)
  (dk-have! '(IN (CARTESIAN CC CC) SET)
    (lambda () (mac 'cartesian-set-iff) (dk-conj-close! (lambda () (ass)))))
  (dk-have! '(IN (CARTESIAN CC RR) SET)
    (lambda () (mac 'cartesian-set-iff) (dk-conj-close! (lambda () (ass))))))

;;; The projection U_K: its FUN typing and its agreement with NTH K, both in the
;;; PTS form product2-fst/snd-continuous-at states them in; then its continuity at W.
(define (p2h-proj! k u w)
  (dk-have! (list 'IN u '(FUN (CARTESIAN (PTS CC-MS) (PTS CC-MS)) (PTS CC-MS)))
    (lambda ()
      (slot 'PTS)
      (dk-lam-type!
        (lambda ()
          (let ((z (dk-di-var!)))
            (dk-split! (dk-cite! 'cartesian-nth z 'CC 'CC))
            (ass)))
        (lambda () (ass)))))
  (dk-have! (list 'FORALL 'p2hq_ (list 'IMPLIES '(IN p2hq_ (CARTESIAN (PTS CC-MS) (PTS CC-MS)))
                                       (list '= (list u 'p2hq_) (list 'NTH k 'p2hq_))))
    (lambda ()
      (slot 'PTS)
      (let ((z (dk-di-var!)))
        (dk-split! (dk-cite! 'cartesian-nth z 'CC 'CC))
        (if (not (dk-lam-b!)) (rfl)))))
  (dk-cite! (if (= k 1) 'product2-fst-continuous-at 'product2-snd-continuous-at)
            'CC-MS 'CC-MS u w))

;;; =====================================================================
;;; pi is continuous at every point of C^2.
;;; =====================================================================
(sp (make-wff (list 'FORALL 'p2hw_ (list 'IMPLIES '(IN p2hw_ (CARTESIAN CC CC))
     (list 'IS-CONTINUOUS-AT P2H-S P2H-T P2H-HF 'p2hw_)))))
(dk-peel!)
(fact 'cc-is-metric-space)
(fact 'rr-is-metric-space)
(dk-cite! 'product2-is-metric-space 'CC-MS 'CC-MS)
(dk-cite! 'product2-is-metric-space 'CC-MS 'RR-MS)
(p2h-set-facts!)
(dk-have! '(IN p2hw_ (CARTESIAN (PTS CC-MS) (PTS CC-MS))) (lambda () (slot 'PTS) (ass)))
;; the projections of C^2 are continuous at w
(p2h-proj! 1 P2H-U1 'p2hw_)
(p2h-proj! 2 P2H-U2 'p2hw_)
;; CA-HOPF: the two coordinates of z |-> pi(U1 z, U2 z) are continuous at w
(dk-split! (dk-cite! 'hopf-map-continuous P2H-S P2H-U1 P2H-U2 'p2hw_))
;; pi : PTS(C^2) -> C x R
(dk-have! (list 'IN P2H-HF (list 'FUN (list 'PTS P2H-S) '(CARTESIAN (PTS CC-MS) (PTS RR-MS))))
  (lambda ()
    (mac 'product2-cc-cc-pts)
    (slot 'PTS)
    (dk-lam-type!
      (lambda ()
        (let* ((leaf (proof-state-focus *ps*)) (z (dk-di-var!)))
          (dk-cite! 'hopf-map-in-cr z) (ass)))
      (lambda () (ass)))))
;; pi(z) = [pi([z1, z2])_1, pi([z1, z2])_2] on PTS(C^2)
(dk-have! (list 'FORALL 'p2hq_ (list 'IMPLIES (list 'IN 'p2hq_ (list 'PTS P2H-S))
            (list '= (list P2H-HF 'p2hq_) (list 'LIST (list P2H-F1 'p2hq_) (list P2H-F2 'p2hq_)))))
  (lambda ()
    (let* ((z (dk-di-var!))
           (a (list 'NTH 1 z)) (b (list 'NTH 2 z)) (ab (list 'LIST a b)))
      (dk-cite! 'product2-cc-cc-pts)
      (dk-rewrite-h! (list 'IN z (list 'PTS P2H-S)) (list 'PTS P2H-S) '(CARTESIAN CC CC))
      (dk-split! (dk-cite! 'cartesian-nth z 'CC 'CC))
      (if (not (dk-lam-b!))
          (let* ((e  (dk-cite! 'hopf-map-pair a b))
                 (l  (caddr e))
                 (zt (dk-cite! 'cartesian-pair-eq z 'CC 'CC)))
            ;; the value pair is in C x R, so its components are sets
            (dk-cite! 'pair-in-cartesian 'CC 'CC a b)
            (dk-rewrite-h! (dk-cite! 'hopf-map-in-cr ab) (list 'HOPF-MAP ab) l)
            ;; cartesian-nth and a hypothesis-side NTH reduction, not pair-in-cartesian-parts:
            ;; that lemma lives in the strand library (CA-HOPF kit finding 3)
            (dk-split! (dk-nth-h! (dk-cite! 'cartesian-nth l 'CC 'RR)))
            (dk-cite! 'membership-implies-sethood (cadr l) 'CC)
            (dk-cite! 'membership-implies-sethood (caddr l) 'RR)
            ;; pi(z) = l, from pi([a, b]) = l and z = [a, b]
            (dk-rewrite-h! e ab z)
            (subst e)
            (nth-r)
            (ass))))))
(dk-cite! 'product2-pair-continuous-at P2H-S 'CC-MS 'RR-MS P2H-F1 P2H-F2 'p2hw_ P2H-HF)
(ass)
(qed 'hopf-map-continuous-at-product)
(topic! 'hopf-map-continuous-at-product 'analysis)
(alias! 'hopf-map-continuous-at-product
        "the Hopf map C^2 -> C x R (max metrics) is continuous at every point")

;;; The notes' statement: pi is continuous C^2 -> C x R.
(sp (make-wff (list 'IS-CONTINUOUS P2H-S P2H-T P2H-HF)))
(fact 'cc-is-metric-space)
(fact 'rr-is-metric-space)
(dk-cite! 'product2-is-metric-space 'CC-MS 'CC-MS)
(dk-cite! 'product2-is-metric-space 'CC-MS 'RR-MS)
(mac 'IS-CONTINUOUS)
(mac 'product2-cc-cc-pts)
(mac 'product2-cc-rr-pts)
(p2h-set-facts!)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((dk-asm? g) (ass))
       ((dk-head-is? g 'FORALL)
        (let ((w (dk-di-var!)))
          (dk-cite! 'hopf-map-continuous-at-product w)
          (ass)))
       (#t
        (dk-lam-type!
          (lambda ()
            (let ((z (dk-di-var!)))
              (dk-cite! 'hopf-map-in-cr z) (ass)))
          (lambda () (ass))))))))
(qed 'hopf-map-continuous-product)
(topic! 'hopf-map-continuous-product 'analysis)
(alias! 'hopf-map-continuous-product
        "Prop. 1.22: the Hopf map pi is continuous from C^2 to C x R")
