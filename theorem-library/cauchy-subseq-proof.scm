;;; theorem-library/cauchy-subseq-proof.scm
;;; ====================================================================
;;; totally-bounded-has-cauchy-subsequence -- PROVEN (was asserted).
;;;
;;; Total boundedness => every sequence has a Cauchy subsequence
;;; (calculus.pdf Prop 3.31), proven to QED via the combinatorial route:
;;;
;;;   rad  <- null-rr-seq-exists           (a positive null radius seq)
;;;   cov  <- tb-rad-ball-cover (s, rad)    (finite ball-cover per level)  [bridge]
;;;   blk  <- block-family-combinatorial(X s, f, cov)   ***** WITNESS *****
;;;   phi  <- diagonalization (blk)         (strictly mono, tail in blk(k))
;;;   ew phi;  strictly-mono closes;  the Cauchy estimate is cauchy-block-
;;;   estimate at the common block radius rad(N0), with rad(N0)+rad(N0) <= eps
;;;   supplied by halving (rr-pos-halvable) + the null threshold.
;;;
;;; The metric leaf (two points of one r-ball, r<=d, d+d=eps => <= eps apart)
;;; is folded into cauchy-block-estimate so the whole assembly is forward
;;; fact/inst+/ai/ew with no eq-subst gymnastics.  Rests on (proof-debt
;;; ledger): block-family-combinatorial, diagonalization, tb-rad-ball-cover,
;;; cauchy-block-estimate, subseq-is-fun, null-rr-seq-exists, rr-pos-halvable,
;;; nn-le-refl + the rr order lemmas.
;;;
;;; Loaded after cauchy-subsequence (the cited supports) + interactive +
;;; proof-debt (sp/di/mac/fact/qed).  See calculus/cauchy-subseq-via-
;;; combinatorial.scm for the same assembly as an annotated probe.
;;; ====================================================================

;; ---- proof helpers (file-local; names verified unique across the load) ----
(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
  (define (asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
  (define (find-asm pred)
    (let loop ((as (asms)))
      (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
  (define (head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
  (define (typed-elt cod)
    (let ((a (find-asm (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (caddr a) cod))))))
      (and a (cadr a))))
  (define (split-ands)
    (let loop ((n 0)) (let ((a (find-asm (head? 'AND))))
      (cond ((and a (< n 10)) (ai a) (loop (+ n 1))) (else n)))))
  (define (contains? sym form)
    (cond ((equal? form sym) #t)
          ((pair? form) (or (contains? sym (car form)) (contains? sym (cdr form))))
          (else #f)))
  (define (subterm-head h form)   ; first subterm whose head is h
    (cond ((and (pair? form) (eq? (car form) h)) form)
          ((pair? form)
           (let loop ((xs form))
             (cond ((null? xs) #f)
                   ((subterm-head h (car xs)) => (lambda (r) r))
                   (else (loop (cdr xs))))))
          (else #f)))
  (define (leaf-goals)
    (filter (lambda (n) (null? (sequent-node-in-arrows n)))
            (dg-ungrounded-nodes (proof-state-dg *ps*))))
  (define (leaf-head? h)
    (let loop ((gs (leaf-goals)))
      (cond ((null? gs) #f)
            ((let ((a (wff-formula (sequent-node-assertion (car gs)))))
               (and (pair? a) (eq? (car a) h)))
             (set! *ps* (focus-on *ps* (car gs))) #t)
            (else (loop (cdr gs))))))
  (define (leaf-pred? p)
    (let loop ((gs (leaf-goals)))
      (cond ((null? gs) #f)
            ((p (wff-formula (sequent-node-assertion (car gs))))
             (set! *ps* (focus-on *ps* (car gs))) #t)
            (else (loop (cdr gs))))))

  ;; ---- the goal ----
  (sp (make-wff
       '(FORALL s (IMPLIES (TOTALLY-BOUNDED s)
          (FORALL f (IMPLIES (IN f (FUN NN (PTS s)))
            (FORSOME phi (AND (STRICTLY-MONO-NN phi)
                              (IS-CAUCHY-SEQ s (SUBSEQ f phi))))))))))
  (quietly (lambda () (di)(di)(di)(di)))
  (define s* (cadr (find-asm (head? 'TOTALLY-BOUNDED))))
  (define f* (typed-elt '(FUN NN (PTS s))))

  ;; rad : positive null radius sequence
  (quietly (lambda ()
    (fact 'null-rr-seq-exists)
    (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs)))))
  (define rad* (cadr (find-asm (head? 'NULL-RR-SEQ))))
  (quietly (lambda () (mac-h 'NULL-RR-SEQ (list 'NULL-RR-SEQ rad*)) (split-ands)))

  ;; cov : finite ball-cover sequence (the only metric step)
  (quietly (lambda ()
    (fact 'tb-rad-ball-cover s* rad*) (split-ands)
    (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs))) (split-ands)))
  ;; cov is the operator in (i): ...(IS-FINITE-COVER (cov k) (X s))...  -- nested
  ;; inside a FORALL, so dig it out by subterm.
  (define cov* (let* ((a (find-asm (lambda (f) (subterm-head 'IS-FINITE-COVER f))))
                      (ifc (and a (subterm-head 'IS-FINITE-COVER a))))
                 (and ifc (car (cadr ifc)))))

  ;; blk : the nested block family -- the combinatorial witness
  (quietly (lambda ()
    (fact 'block-family-combinatorial (list 'PTS s*) f* cov*)
    (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs))) (split-ands)))
  (define blk* (typed-elt '(FUN NN (INF-SUBSETS NN))))

  ;; phi : strictly monotone diagonal
  (quietly (lambda ()
    (if blk* (fact 'diagonalization blk*))
    (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs))) (split-ands)))
  (define phi* (let ((sm (find-asm (head? 'STRICTLY-MONO-NN)))) (and sm (cadr sm))))

  ;; witness phi; close the strictly-mono conjunct; focus the Cauchy conjunct
  (quietly (lambda () (if phi* (ew phi*)) (di)))
  (leaf-head? 'STRICTLY-MONO-NN) (quietly (lambda () (ass)))
  (leaf-head? 'IS-CAUCHY-SEQ)

  ;; bring IS-METRIC-SPACE s into context
  (define tb* (find-asm (head? 'TOTALLY-BOUNDED)))
  (quietly (lambda () (mac-h 'TOTALLY-BOUNDED tb*) (split-ands)))

  ;; unfold IS-CAUCHY-SEQ; close IS-MS + SUBSEQ-typing conjuncts (typing's AND
  ;; antecedent needs backward bc*, not fact)
  (quietly (lambda () (mac 'IS-CAUCHY-SEQ)))
  (quietly (lambda ()
    (let loop ((n 0))
      (when (< n 6)
        (cond ((leaf-head? 'AND) (di) (loop (+ n 1)))
              ((leaf-head? 'IS-METRIC-SPACE) (ass) (loop (+ n 1)))
              ((leaf-head? 'STRICTLY-MONO-NN) (ass) (loop (+ n 1)))
              ((leaf-pred? (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                            (equal? (caddr a) (list 'FUN 'NN (list 'PTS s*))))))
               (bc* 'subseq-is-fun) (di) (ass-all) (loop (+ n 1)))
              (else 'done))))))

  ;; the eps estimate
  (leaf-head? 'FORALL)
  (quietly (lambda () (di) (di)))
  (define eps* (cadr (find-asm (head? 'POS-RR))))

  ;; eps = d + d, d > 0  (cite rr-pos-halvable before unfolding POS-RR eps)
  (quietly (lambda ()
    (fact 'rr-pos-halvable eps*)
    (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs))) (split-ands)
    (mac-h 'POS-RR (list 'POS-RR eps*)) (split-ands)))
  (define d* (cadr (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'POS-RR)
                                              (symbol? (cadr a)) (not (eq? (cadr a) eps*)))))))

  ;; null property at d -> threshold N0
  (define nullprop (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)
     (contains? 'FORSOME a)(contains? '<= a)(contains? rad* a)))))
  (quietly (lambda ()
    (and nullprop (inst+ nullprop d*))
    (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs))) (split-ands)))
  (define N0* (let ((a (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'IN)(equal? (caddr a) 'NN))))))
                (and a (cadr a))))

  ;; witness N := N0; close (IN N0 NN); intro m, n_, and their order hyps
  (quietly (lambda () (if N0* (ew N0*)) (di)))
  (leaf-pred? (lambda (a) (equal? a (list 'IN N0* 'NN)))) (quietly (lambda () (ass)))
  (leaf-head? 'FORALL)
  (quietly (lambda () (di)(di)(di)(di)(di) (split-ands)))

  ;; eigenvars m, n_ from the goal (<= ((d s) ((subseq f phi) m) ((subseq f phi) n_)) eps)
  (define gg (gf))
  (define m*  (cadr (cadr  (cadr gg))))
  (define n_* (cadr (caddr (cadr gg))))

  ;; tail: phi(m), phi(n_) in blk(N0)
  (define tailp (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)
     (contains? phi* a)(contains? blk* a)))))
  (quietly (lambda () (inst+ tailp N0*)))
  (define t1 (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)
     (contains? phi* a)(contains? blk* a)(contains? N0* a)))))
  (quietly (lambda () (inst+ t1 m*) (inst+ t1 n_*)))

  ;; capture: f(phi m), f(phi n_) in U
  (define capp (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)
     (contains? cov* a)(contains? 'FORSOME a)(not (contains? 'BALL a))))))
  (quietly (lambda () (inst+ capp N0*)
    (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs))) (split-ands)))
  (define Ustar (cadr (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'IN)
     (equal? (caddr a) (list cov* N0*)))))))
  (define capinner (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)
     (contains? Ustar a)(contains? blk* a)))))
  (quietly (lambda () (inst+ capinner (list phi* m*)) (inst+ capinner (list phi* n_*))))

  ;; bridge (ii): U = BALL(s,c,rad N0), c in X(s)
  (define brii (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)
     (contains? cov* a)(contains? 'BALL a)))))
  (quietly (lambda () (inst+ brii N0*)))
  (define b1 (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)
     (contains? 'BALL a)(contains? N0* a)))))
  (quietly (lambda () (inst+ b1 Ustar)
    (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs))) (split-ands)))
  (define eqU (find-asm (lambda (a) (and (pair? a)(eq? (car a) '=)(contains? 'BALL a)(contains? Ustar a)))))
  (define c* (caddr (caddr eqU)))

  ;; POS-RR(rad N0); rad(N0) <= d (null-inner at N0, AND guard built explicitly)
  (define posrad (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)
     (contains? 'POS-RR a)(contains? rad* a)(not (contains? 'FORSOME a))(not (contains? '<= a))))))
  (quietly (lambda () (inst+ posrad N0*)))
  (quietly (lambda () (fact 'nn-le-refl N0*)))
  (quietly (lambda () (cut (list 'AND (list 'IN N0* 'NN) (list '<= N0* N0*)))))
  (leaf-pred? (lambda (a) (equal? a (list 'AND (list 'IN N0* 'NN) (list '<= N0* N0*)))))
  (quietly (lambda () (di)))
  (leaf-pred? (lambda (a) (equal? a (list 'IN N0* 'NN))))  (quietly (lambda () (ass)))
  (leaf-pred? (lambda (a) (equal? a (list '<= N0* N0*))))  (quietly (lambda () (ass)))
  (leaf-head? '<=)
  (define nullinner (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)
     (contains? rad* a)(contains? d* a)(not (contains? 'FORSOME a))))))
  (quietly (lambda () (inst+ nullinner N0*)))

  ;; rewrite SUBSEQ in the goal; close by cauchy-block-estimate
  (quietly (lambda () (mac 'SUBSEQ) (lam-b) (lam-b) (lam-b)))
  (quietly (lambda ()
    (fact 'cauchy-block-estimate s* c* (list rad* N0*) Ustar
          (list f* (list phi* m*)) (list f* (list phi* n_*)) d* eps*)
    (ass)))

(if (proof-done? *ps*)
    (qed 'totally-bounded-has-cauchy-subsequence)
    (error "cauchy-subseq-proof: proof did not complete"))
