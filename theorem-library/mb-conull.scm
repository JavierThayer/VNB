;;; mb-conull.scm -- construction-of-measures.pdf Prop. 2.9: conull sets are closed under
;;; countable intersections, and a (measurable) superset of a conull set is conull.
;;; Agent M-B, 2026-10-26.  DESTINATION: theorem-library/mb-conull.scm.  Library: measure.
;;;
;;;   conull-countable-inter   f in FUN(NN, cA), every f(k) conull  =>  the intersection
;;;                            COMPLEMENT-IN(omega, U_n COMPLEMENT-IN(omega, f(n))) is conull
;;;                            (the countable intersection in the form measure-continuity-from-
;;;                            above writes it)
;;;   conull-superset          a conull, b in cA, a subset b  =>  b conull
;;;
;;; THE ROUTE (the notes'): the complement of the intersection lies inside the union of the
;;; complements, whose measure is at most the sum of the measures (measure-countably-
;;; subadditive), every term 0 (esum-nn-zero).
;;;
;;; CITATIONS: is-measure, is-conull (vocabulary), sigma-algebra-complement-closed,
;;; sigma-algebra-union-closed, measure-countably-subadditive, measure-monotone (measure-laws),
;;; esum-nn-zero, complement-in-membership, class-extensionality, fun-apply-type-c,
;;; rr-pos-star-le-real-in-rr, rr-pos-star-nonneg, rr-leq-antisymmetric.
;;; LOAD WINDOW: after theorem-library/measure-laws (3498) and structure-library/mb-vocab.
;;; Helper prefix: mbc-.

(define (mbc-measure-parts! om ca mu)
  (let* ((iff (dk-fact! 'is-measure om ca mu))
         (rhs (caddr iff))
         (c1 (cadr rhs)) (c2 (cadr (caddr rhs))))
    (map (lambda (c) (dk-project! c 'IS-MEASURE (list 'IS-MEASURE om ca mu)))
         (list c1 c2))))

(define (mbc-and! . fs)
  (let ((c (let loop ((l fs)) (if (null? (cdr l)) (car l) (list 'AND (car l) (loop (cdr l)))))))
    (if (not (dk-asm? c)) (dk-have! c (lambda () (dk-conj-close! (lambda () (ass))))))))

;;; open (IN W BU) for a BIG-UNION BU: land the index typing and the member
(define (mbc-bu-open! w bu)
  (let* ((landed (dk-landed (lambda () (bu-me (list 'IN w bu)))))
         (ein (find-first (lambda (f) (and (eq? (car f) 'IN) (not (equal? (cadr f) w)))) landed))
         (app (find-first (lambda (f) (not (eq? f ein))) landed)))
    (cons ein app)))

;;; goal (SUBSET X Y): open by subset-def, cite MEMB! on the fresh point, keep what mentions
;;; it, prop
(define (mbc-subset-prop! memb!)
  (mac 'subset-def)
  (let ((w (dk-di-var!)))
    (memb! w)
    (apply dk-only! (filter (lambda (f) (dk-contains? f w)) (dk-asms)))
    (prop)))

;;; (= (mu X) 0) from (<= (mu X) 0) and X in cA, mu typed
(define (mbc-zero! mux)
  (dk-have! (list '= mux 0)
    (lambda ()
      (fact 'rr-zero-in)
      (mbc-and! (list 'IN mux 'RR-POS-STAR) '(IN 0 RR))
      (dk-cite! 'rr-pos-star-le-real-in-rr mux 0)   ; (IN mux RR)
      (dk-cite! 'rr-pos-star-nonneg mux)
      (mbc-and! (list 'IN mux 'RR) '(IN 0 RR))
      (mbc-and! (list '<= mux 0) (list '<= 0 mux))
      (dk-cite! 'rr-leq-antisymmetric mux 0)
      (ass))))

;;; ---------------------------------------------------------------------------
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f_
  (IMPLIES (IS-MEASURE omega cA mu)
    (IMPLIES (IN f_ (FUN NN cA))
      (IMPLIES (FORALL k (IMPLIES (IN k NN) (IS-CONULL omega cA mu (f_ k))))
        (IS-CONULL omega cA mu
          (COMPLEMENT-IN omega (BIG-UNION n_ NN (COMPLEMENT-IN omega (f_ n_))))))))))))))
(dk-peel!)
(mbc-measure-parts! 'omega 'cA 'mu)
(let* ((fv 'f_)
       (cf '(VNB-LAMBDA n_ NN (COMPLEMENT-IN omega (f_ n_))))
       (bul (list 'BIG-UNION 'n_ 'NN (list cf 'n_)))
       (buc '(BIG-UNION n_ NN (COMPLEMENT-IN omega (f_ n_))))
       (iv (list 'COMPLEMENT-IN 'omega buc))
       (civ (list 'COMPLEMENT-IN 'omega iv))
       (esf (list 'VNB-LAMBDA 'n_ 'NN (list 'mu (list cf 'n_))))
       (conull-all (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'IS-CONULL)))
                            "the conull hypothesis")))
  ;; (1) the complements as a sequence in cA, and their union
  (dk-have! (list 'IN cf '(FUN NN cA))
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((kv (car (map cadr (filter (lambda (f) (dk-head-is? f 'IN)) (dk-peel!))))))
            (fact 'fun-apply-type-c fv 'NN 'cA kv)
            (fact 'sigma-algebra-complement-closed 'omega 'cA (list fv kv))
            (ass))))))
  (fact 'sigma-algebra-union-closed 'omega 'cA cf)
  ;; the union of the redexes is the union of the reduced terms (extensionality; beta is not
  ;; licensed under the BIG-UNION binder) -- measure-laws' route
  (dk-have! (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ bul) (list 'IN 'w_ buc)))
    (lambda ()
      (let ((wv (dk-di-var! (lambda (g) (cadr (cadr g))))))
        (for-each
          (lambda (l)
            (dk-focus! l)
            (if (equal? (dk-goal) (list 'IN wv buc))
                (let* ((r (mbc-bu-open! wv bul)) (e (cadr (car r))))
                  (fact 'fun-apply-type-c fv 'NN 'cA e)
                  (fact 'sigma-algebra-complement-closed 'omega 'cA (list fv e))
                  (fact 'membership-implies-sethood (list 'COMPLEMENT-IN 'omega (list fv e)) 'cA)
                  (dk-lam-b-h! (cdr r))
                  (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (bu-mi e)))))
                (let* ((r (mbc-bu-open! wv buc)) (e (cadr (car r))))
                  (fact 'fun-apply-type-c fv 'NN 'cA e)
                  (fact 'sigma-algebra-complement-closed 'omega 'cA (list fv e))
                  (fact 'membership-implies-sethood (list 'COMPLEMENT-IN 'omega (list fv e)) 'cA)
                  (for-each (lambda (n) (dk-focus! n)
                              (if (equal? (dk-goal) (list 'IN e 'NN)) (ass)
                                  (begin (dk-lam-b!) (ass))))
                            (dk-opened (lambda () (bu-mi e)))))))
          (dk-opened (lambda () (di)))))))
  (fact 'class-extensionality bul buc)
  (dk-have! (list 'IN buc 'cA) (lambda () (subst (list '= buc bul)) (ass)))
  (fact 'sigma-algebra-complement-closed 'omega 'cA buc)    ; I in cA
  (fact 'sigma-algebra-complement-closed 'omega 'cA iv)     ; its complement in cA
  ;; (2) mu(U complements) <= sum of mu(complements) = 0
  (fact 'measure-countably-subadditive 'omega 'cA 'mu cf)
  (dk-have! (list 'IN esf '(FUN NN RR-POS-STAR))
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((kv (car (map cadr (filter (lambda (f) (dk-head-is? f 'IN)) (dk-peel!))))))
            (fact 'fun-apply-type-c cf 'NN 'cA kv)
            (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR (list cf kv))
            (ass))))))
  (dk-have! '(FORALL ozn (IMPLIES (IN ozn NN) (= ((VNB-LAMBDA n_ NN (mu ((VNB-LAMBDA n_ NN (COMPLEMENT-IN omega (f_ n_))) n_))) ozn) 0)))
    (lambda ()
      (let ((kv (car (map cadr (filter (lambda (f) (dk-head-is? f 'IN)) (dk-peel!))))))
        (fact 'fun-apply-type-c fv 'NN 'cA kv)
        (fact 'sigma-algebra-complement-closed 'omega 'cA (list fv kv))
        (fact 'fun-apply-type-c cf 'NN 'cA kv)
        (dk-lam-b!)
        (let ((cn (list 'IS-CONULL 'omega 'cA 'mu (list fv kv))))
          (if (not (dk-asm? cn)) (inst*! conull-all kv))
          (dk-have! (list '= (list 'mu (list 'COMPLEMENT-IN 'omega (list fv kv))) 0)
            (lambda () (mac-h 'IS-CONULL cn) (dk-split-all!) (ass)))
          (ass)))))
  (fact 'esum-nn-zero esf)
  (let ((le (dk-rewrite-h! (list '<= (list 'mu bul) (list 'ESUM esf)) (list 'ESUM esf) 0)))
    (dk-rewrite-h! le bul buc))
  (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR buc)
  (mbc-zero! (list 'mu buc))
  ;; (3) the complement of the intersection lies inside the union of the complements
  (dk-have! (list 'SUBSET civ buc)
    (lambda ()
      (mbc-subset-prop!
        (lambda (w)
          (dk-cite! 'complement-in-membership 'omega iv w)
          (dk-cite! 'complement-in-membership 'omega buc w)))))
  (fact 'measure-monotone 'omega 'cA 'mu civ buc)
  (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR civ)
  (dk-have! (list '<= (list 'mu civ) 0)
    (lambda () (subst (list '= 0 (list 'mu buc))) (ass)))
  (mbc-zero! (list 'mu civ))
  (mac 'IS-CONULL)
  (dk-conj-close! (lambda () (ass))))
(qed 'conull-countable-inter)
(topic! 'conull-countable-inter 'analysis)

;;; ---------------------------------------------------------------------------
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL a_ (FORALL b_
  (IMPLIES (IS-MEASURE omega cA mu)
    (IMPLIES (IS-CONULL omega cA mu a_)
      (IMPLIES (IN b_ cA)
        (IMPLIES (SUBSET a_ b_) (IS-CONULL omega cA mu b_))))))))))))
(dk-peel!)
(mbc-measure-parts! 'omega 'cA 'mu)
(let* ((ca_ '(COMPLEMENT-IN omega a_)) (cb_ '(COMPLEMENT-IN omega b_)))
  (dk-have! '(IN a_ cA) (lambda () (mac-h 'IS-CONULL '(IS-CONULL omega cA mu a_)) (dk-split-all!) (ass)))
  (dk-have! (list '= (list 'mu ca_) 0)
    (lambda () (mac-h 'IS-CONULL '(IS-CONULL omega cA mu a_)) (dk-split-all!) (ass)))
  (fact 'sigma-algebra-complement-closed 'omega 'cA 'a_)
  (fact 'sigma-algebra-complement-closed 'omega 'cA 'b_)
  (dk-have! (list 'SUBSET cb_ ca_)
    (lambda ()
      (mbc-subset-prop!
        (lambda (w)
          (dk-cite! 'complement-in-membership 'omega 'a_ w)
          (dk-cite! 'complement-in-membership 'omega 'b_ w)
          (let ((s (dk-cite! 'subset-def 'a_ 'b_)))
            (dk-project! (caddr s) (lambda () (mac-h 'subset-def '(SUBSET a_ b_)) (ass)))
            (inst*! (caddr s) w))))))
  (fact 'measure-monotone 'omega 'cA 'mu cb_ ca_)
  (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR cb_)
  (dk-have! (list '<= (list 'mu cb_) 0)
    (lambda () (subst (list '= 0 (list 'mu ca_))) (ass)))
  (mbc-zero! (list 'mu cb_))
  (mac 'IS-CONULL)
  (dk-conj-close! (lambda () (ass))))
(qed 'conull-superset)
(topic! 'conull-superset 'analysis)
