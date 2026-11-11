;;; ccr1109a-late.scm -- wave of 2026-11-09/10 (agent CCR-1109-A), wired 2026-11-10 from scratchpad/ccr1109a/ccr1109a-late.scm.
;;; Library: complex-analysis.

;;; ccr1109a-late.scm -- CCR.pdf Corollary 1.20 (IS-DENSE form) and Proposition 2.23 (residue fields agree).
;;; Agent CCR-1109-A, wave 2026-11-09.  Destination: theorem-library/ccr1109a-late.scm.  Library:
;;; complex-analysis (it cites padic-laws, which is complex-analysis).  Helper prefix c9p-.
;;;
;;; metric-dense-of-near: in a metric space s, a subset A that meets every ball about every point of s is
;;; dense (IS-DENSE: PTS s inside CLOSURE(s, A)).  Corollary 1.20 is then ccr-1-20 (the metric form,
;;; padic-laws) read in the subspace Z(Q) of Q.
;;;
;;; LOAD WINDOW: after theorem-library/padic-laws (ccr-1-20, pc-nv-integers-eq) and qp-laws (rs-class-eq-iff,
;;; nv-integers-domain); the metric-closure / metric-subspace laws load earlier.  Nothing cites it.

;; (SUBSET X Y) in context, E in X in context: land E in Y
(define (c9p-sub-elim! xs ys e)
  (let ((iff (dk-cite! 'subset-def xs ys)))
    (if (not (dk-asm? (caddr iff))) (dk-iff-fwd! iff))
    (dk-chain-ass! (dk-apply! (caddr iff) e))))

(define c9p-near '(FORALL x (IMPLIES (IN x (PTS s)) (FORALL eps (IMPLIES (POS-RR eps)
              (FORSOME pa (AND (IN pa A) (< ((DIST s) x pa) eps))))))))

;;; -----------------------------------------------------------------------
;;; A set meeting every ball about every point is dense.

(sp (make-wff `(FORALL s (IMPLIES (IS-METRIC-SPACE s) (FORALL A (IMPLIES (SUBSET A (PTS s))
  (IMPLIES ,c9p-near (IS-DENSE s A))))))))
(dk-peel!)
(mac 'is-dense)
(dk-conj-close!
  (lambda ()
    (if (not (dk-ass!))
        (begin
          (mac 'subset-def)
          (let ((x (dk-di-var!)))
            (mac 'closure)
            (in-sep!
              (lambda () (dk-ass!))
              (lambda ()
                (let* ((landed (dk-landed (lambda () (dk-peel!))))
                       (opn (find-first (lambda (f) (dk-head-is? f 'IS-OPEN)) (begin (dk-split-all!) (dk-asms))))
                       (u (caddr opn))
                       (oparts (begin (dk-iff-fwd! (dk-cite! 'is-open 's u)) (dk-asms)))
                       (fa (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'BALL))) (dk-asms)))
                       (r (dk-skolem! (dk-chain-ass! (dk-apply! fa x))))
                       (pa (begin (dk-cite! 'rr-pos-rr-in-rr r)
                                  (dk-skolem! (dk-chain-ass! (dk-apply! c9p-near x r))))))
                  (c9p-sub-elim! 'A '(PTS s) pa)
                  (dk-cite! 'metric-dist-real 's x pa)
                  (let ((bm (dk-cite! 'ball-membership 's x r pa))
                        (dd `((DIST s) ,x ,pa)))
                    (dk-have! (caddr bm)
                      (lambda ()
                        (dk-conj-close!
                          (lambda ()
                            (cond ((dk-ass!) #t)
                                  ((dk-head-is? (dk-goal) 'NOT)
                                   (di) (dk-absurd! `(= ,dd ,r) `(< ,dd ,r)))
                                  (#t (dk-ineq! `(< ,dd ,r))))))))
                    (dk-iff-bwd! bm)
                    (c9p-sub-elim! `(BALL s ,x ,r) u pa)
                    (ew pa)
                    (dk-conj-close! (lambda () (dk-ass!))))))))))))
(qed 'metric-dense-of-near)

;;; -----------------------------------------------------------------------
;;; Corollary 1.20: Z is dense in Z(Q), with the metric of |.|_p.

(define c9p-k '(QQ-PADIC p))
(define c9p-ms '(NF-METRIC-SPACE (QQ-PADIC p)))
(define c9p-z '(NV-INTEGERS (QQ-PADIC p)))
(define c9p-sub `(SUBSPACE-MS ,c9p-ms ,c9p-z))

(sp (make-wff `(FORALL p (IMPLIES (ZZ-PRIME p) (IS-DENSE ,c9p-sub ZZ)))))
(dk-peel!)
(dk-cite! 'qq-padic-is-normed-field 'p)
(dk-cite! 'nf-metric-space-is-metric-space c9p-k)
(dk-cite! 'nf-metric-carrier c9p-k)
(dk-cite! 'pq-carr 'p)
(dk-cite! 'pq-fnrm 'p)
(let ((zeq (dk-cite! 'pc-nv-integers-eq 'p)))
  ;; Z(Q) inside Q, Z(Q) a set, Z inside Z(Q)
  (dk-have! `(SUBSET ,c9p-z QQ)
    (lambda () (subst zeq) (mac 'subset-def)
              (let ((m (car (dk-landed (lambda () (di))))))
                (sep-me m) (dk-close-if-asm!))))
  (fact 'qq-is-set)
  (dk-have-and! `(SUBSET ,c9p-z QQ) '(IN QQ SET))
  (dk-chain-ass! (dk-cite! 'subclass-of-set-is-set c9p-z 'QQ))
  (dk-have! `(SUBSET ,c9p-z (PTS ,c9p-ms))
    (lambda () (subst `(== (PTS ,c9p-ms) (CARR ,c9p-k))) (subst `(= (CARR ,c9p-k) QQ)) (dk-close-if-asm!)))
  (dk-chain-ass! (dk-cite! 'subspace-is-metric-space c9p-ms c9p-z))
  (dk-cite! 'subspace-pts c9p-ms c9p-z)
  (dk-have! `(SUBSET ZZ (PTS ,c9p-sub))
    (lambda ()
      (subst `(== (PTS ,c9p-sub) ,c9p-z))
      (mac 'subset-def)
      (let ((n (dk-di-var!)))
        (dk-cite! 'zz-subset-qq n)
        (dk-cite! 'pc-abs-int 'p n)
        (subst zeq)
        (in-sep! (lambda () (dk-ass!)) (lambda () (dk-ass!))))))
  (let ((near `(FORALL x (IMPLIES (IN x (PTS ,c9p-sub)) (FORALL eps (IMPLIES (POS-RR eps)
                 (FORSOME pa (AND (IN pa ZZ) (< ((DIST ,c9p-sub) x pa) eps)))))))))
    (dk-have! near
      (lambda ()
        (let* ((landed (dk-landed (lambda () (dk-peel!))))
               (x (cadr (find-first (lambda (f) (dk-head-is? f 'IN)) landed)))
               (eps (cadr (find-first (lambda (f) (dk-head-is? f 'POS-RR)) landed))))
          (dk-have! `(IN ,x ,c9p-z) (lambda () (subst `(== ,c9p-z (PTS ,c9p-sub))) (dk-close-if-asm!)))
          (let ((th (dk-skolem! (dk-chain-ass! (dk-cite! 'ccr-1-20 'p x eps)))))
            (dk-have! `(IN ,th ,c9p-z)
              (lambda () (subst `(== ,c9p-z (PTS ,c9p-sub)))
                         (c9p-sub-elim! 'ZZ `(PTS ,c9p-sub) th)
                         (dk-close-if-asm!)))
            (for-each (lambda (v)
                        (dk-have! `(IN ,v (PTS ,c9p-ms))
                          (lambda () (subst `(== (PTS ,c9p-ms) (CARR ,c9p-k))) (subst `(= (CARR ,c9p-k) QQ))
                                     (c9p-sub-elim! c9p-z 'QQ v)
                                     (dk-close-if-asm!))))
                      (list x th))
            (let* ((e1 (dk-chain-ass! (dk-cite! 'subspace-dist c9p-ms c9p-z x th)))
                  (e2 (dk-cite! 'metric-sym c9p-ms x th)))
              (ew th)
              (dk-conj-close!
                (lambda ()
                  (if (not (dk-ass!))
                      (begin (subst e1) (subst e2) (dk-close-if-asm!))))))))))
    (dk-chain-ass! (dk-cite! 'metric-dense-of-near c9p-sub 'ZZ))
    (dk-close-if-asm!)))
(qed 'ccr-1-20-dense)

;;; -----------------------------------------------------------------------
;;; Remark 2.22 and Proposition 2.23.  K an NV field, A an NV domain of K (so A inside Z(K)), and a map
;;; phi : Z(K) -> A with |x - phi(x)| < 1 and phi(x) = x on A (the map a dense A provides; the notes' "(i)
;;; |x - phi(x)| < |x|" is read "< 1", the bound the proof uses).  The class of phi(x) in Z(K)/M(K) is the
;;; class of x.  The residue ring A/M(A) is NV-RESIDUE(K, A) (nvlocal-vocab), so Z(K)/M(K) is
;;; NV-RESIDUE(K, Z(K)), and its class map is CLASS over RINGOID-SETOID(NV-RES-RINGOID(K, Z(K))).

(define c9p-zk '(NV-INTEGERS K))
(define c9p-zs `(RINGOID-SETOID (NV-RES-RINGOID K ,c9p-zk)))
(define c9p-phi-hyps
  `((IS-NV-DOMAIN K A) (IN phi (FUN ,c9p-zk A))
    (FORALL x (IMPLIES (IN x ,c9p-zk) (< ((FNRM K) ((ADD K) x ((NEG K) (phi x)))) 1)))
    (FORALL x (IMPLIES (IN x A) (= (phi x) x)))))
(define (c9p-curry hs body) (if (null? hs) body `(IMPLIES ,(car hs) ,(c9p-curry (cdr hs) body))))

;; the common setup: K a normed NV field, Z(K) an NV domain
(define (c9p-res-setup!)
  (dk-cite! 'nv-domain-field 'K 'A)
  (dk-cite! 'nv-field-normed 'K)
  (dk-cite! 'nv-integers-domain 'K))
;; X in Z(K): land phi(X) in A, phi(X) in Z(K), both in CARR K, and the two norms real
(define (c9p-phi-at! x)
  (dk-have-and! `(IN phi (FUN ,c9p-zk A)) `(IN ,x ,c9p-zk))
  (dk-cite! 'fun-apply-type 'phi c9p-zk 'A x)
  (dk-cite! 'nv-domain-integral 'K 'A `(phi ,x))
  (dk-cite! 'nv-domain-sub 'K c9p-zk x)
  (dk-cite! 'nv-domain-sub 'K c9p-zk `(phi ,x))
  `(phi ,x))

(sp (make-wff `(FORALL K (FORALL A (FORALL phi ,(c9p-curry c9p-phi-hyps
  `(FORALL x (IMPLIES (IN x ,c9p-zk) (= (CLASS ,c9p-zs (phi x)) (CLASS ,c9p-zs x))))))))))
(dk-peel!)
(c9p-res-setup!)
(let* ((x (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) c9p-zk) (symbol? (cadr f)))) (dk-asms))))
       (px (c9p-phi-at! x))
       (law (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'FNRM))) (dk-asms)))
       (lt (dk-chain-ass! (dk-apply! law x)))
       (d `((ADD K) ,px ((NEG K) ,x))))
  (dk-cite! 'nv-domain-neg 'K c9p-zk x)
  (dk-cite! 'nv-domain-add 'K c9p-zk px `((NEG K) ,x))
  (let ((e (dk-cite! 'nf-norm-sub-sym 'K x px))
        )
    (dk-have! `(IN ,d (NV-MAXIMAL K ,c9p-zk))
      (lambda ()
        (subst (dk-cite! 'nv-maximal-unfold 'K c9p-zk))
        (in-sep! (lambda () (dk-ass!))
                 (lambda () (subst `(= ((FNRM K) ,d) ((FNRM K) ((ADD K) ,x ((NEG K) ,px))))) (dk-ass!)))))
    (dk-iff-bwd! (dk-cite! 'rs-class-eq-iff 'K c9p-zk px x))
    (dk-close-if-asm!)))
(qed 'ccr-2-23-class)
