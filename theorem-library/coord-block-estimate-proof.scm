;;; theorem-library/coord-block-estimate-proof.scm
;;; ====================================================================
;;; coord-block-estimate -- PROVEN.
;;;
;;;   Convergence ALONG an index block B transfers to a reindexing whose tail
;;;   lands in B:
;;;     CONVERGES-ALONG(s,g,B,p) and STRICTLY-MONO-NN(delta) and m0 in NN and
;;;     (forall j in NN. j>=m0 => delta(j) in B)
;;;       => CONVERGES-TO(s, SUBSEQ(g,delta), p).
;;;
;;; The estimate brick of the coordinatewise-diagonal-subseq keystone (the other
;;; pieces being convergence-block-tower and diagonalization).  Proof: given eps,
;;; CONVERGES-ALONG supplies a threshold N0 (convergence along B); pick a common
;;; upper bound c of m0 and N0 (nn-pair-upper-bound); for n>=c the reindex value
;;; delta(n) satisfies n>=m0 so delta(n) in B (the tail hypothesis), and
;;; delta(n)>=n>=N0 (strictly-mono-ge-id), so the along-B bound fires:
;;; d(g(delta n),p)=d(SUBSEQ(g,delta)(n),p)<=eps.
;;;
;;; FRESH-VAR NOTE.  The tail-threshold bound var is named m0, NOT n0: the
;;; cainner existential of CONVERGES-ALONG is skolemized into the kernel's
;;; fresh-name namespace (n_1, n_2, ...), and a lemma var literally named `n0'
;;; COLLIDES with it -- the skolemizer reuses n_k, fusing the tail threshold and
;;; the convergence skolem N0 into one object (its symbol even renders as n_11),
;;; which defeats every forward-detach.  Naming it m0 (outside the n_* namespace)
;;; keeps raw eigenvar extraction faithful and lets the plain inst+ flow close.
;;; LESSON: name lemma bound vars away from the skolemizer's n_* namespace.
;;;
;;; Modulo {subseq-is-fun, nn-pair-upper-bound, strictly-mono-ge-id,
;;; fun-apply-type-c, nn-in-rr, rr-le-trans-c} [trust: well-known] + the
;;; CONVERGES-ALONG/CONVERGES-TO/STRICTLY-MONO-NN/SUBSEQ defs.  Loads in the
;;; interactive phase (sp/di/mac/fact/inst+/qed).  Build:
;;; calculus/coord-block-est-build.scm.
;;; ====================================================================

(define (cbe--gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (cbe--asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (cbe--find pred) (let loop ((as (cbe--asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (cbe--head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (cbe--has? sym form) (cond ((equal? form sym) #t)
  ((pair? form) (or (cbe--has? sym (car form)) (cbe--has? sym (cdr form)))) (else #f)))
(define (cbe--split) (let loop ((n 0)) (let ((a (cbe--find (cbe--head? 'AND))))
  (cond ((and a (< n 12)) (ai a) (loop (+ n 1))) (else n)))))
(define (cbe--leaves) (filter (lambda (n) (null? (sequent-node-in-arrows n)))
                              (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (cbe--fpred p)
  (let ((cands (filter (lambda (n) (p (wff-formula (sequent-node-assertion n)))) (cbe--leaves))))
    (and (pair? cands)
         (begin (set! *ps* (focus-on *ps*
                  (car (sort cands (lambda (a b)
                    (> (length (sequent-node-assumptions a))
                       (length (sequent-node-assumptions b))))))))
                #t))))
(define (cbe--fhead h) (cbe--fpred (lambda (a) (and (pair? a) (eq? (car a) h)))))

;; tail-threshold var is m0 (NOT n0) -- see FRESH-VAR NOTE above.
(sp (make-wff
     '(FORALL s (FORALL g (FORALL B (FORALL p (FORALL delta (FORALL m0
        (IMPLIES (CONVERGES-ALONG s g B p)
        (IMPLIES (STRICTLY-MONO-NN delta)
        (IMPLIES (IN m0 NN)
        (IMPLIES (FORALL j (IMPLIES (IN j NN) (IMPLIES (<= m0 j) (IN (delta j) B))))
          (CONVERGES-TO s (SUBSEQ g delta) p)))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)(di)(di)(di)(di)))
(define cbe--s   (cadr (cbe--find (cbe--head? 'CONVERGES-ALONG))))
(define cbe--Hca (cbe--find (cbe--head? 'CONVERGES-ALONG)))
(define cbe--g   (caddr cbe--Hca))
(define cbe--B   (cadddr cbe--Hca))
(define cbe--p   (car (cddddr cbe--Hca)))
(define cbe--delta (cadr (cbe--find (cbe--head? 'STRICTLY-MONO-NN))))
(define cbe--Hmono (cbe--find (cbe--head? 'STRICTLY-MONO-NN)))
;; tail = (FORALL j (IMPLIES (IN j NN) (IMPLIES (<= m0 j) (IN (delta j) B)))).
;; Signature: <=, delta, B, no FUN (the STRICTLY-MONO-NN unfold also has delta+a
;; bound `b' but carries FUN).
(define (cbe--tail) (cbe--find (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(cbe--has? '<= a)(cbe--has? cbe--delta a)(cbe--has? cbe--B a)(not (cbe--has? 'FUN a))))))
(define cbe--m0 (cadr (cadr (caddr (caddr (cbe--tail))))))    ; (<= m0 j) -> m0

;; unfold CONVERGES-ALONG hyp
(quietly (lambda () (mac-h 'CONVERGES-ALONG cbe--Hca) (cbe--split)))
(define cbe--cainner (cbe--find (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(cbe--has? cbe--g a)(cbe--has? cbe--B a)(cbe--has? 'POS-RR a)))))

;; unfold goal, dispatch structural conjuncts (IS-MS / SUBSEQ-typing)
(quietly (lambda () (mac 'CONVERGES-TO)))
(quietly (lambda ()
  (let loop ((n 0))
    (when (< n 8)
      (cond ((cbe--fhead 'AND) (di) (loop (+ n 1)))
            ((cbe--fhead 'IS-METRIC-SPACE) (ass) (loop (+ n 1)))
            ((cbe--fpred (lambda (a) (and (pair? a)(eq? (car a) 'IN)(equal? (caddr a) (list 'FUN 'NN (list 'X cbe--s))))))
             (if (cbe--has? 'SUBSEQ (cbe--gf)) (begin (bc* 'subseq-is-fun)(di)(ass-all)) (ass))
             (loop (+ n 1)))
            (else 'done))))))
;; the eps goal
(cbe--fhead 'FORALL)
(quietly (lambda () (di)(di)))
(define cbe--eps (cadr (cbe--find (cbe--head? 'POS-RR))))
;; N0 from cainner @ eps
(quietly (lambda () (inst+ cbe--cainner cbe--eps)
  (let ((fs (cbe--find (cbe--head? 'FORSOME)))) (and fs (ai fs))) (cbe--split)))
(define cbe--caN0 (cbe--find (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(cbe--has? cbe--g a)(cbe--has? cbe--B a)(not (cbe--has? 'POS-RR a))))))
(define cbe--N0 (cadr (cadr (caddr (caddr (caddr cbe--caN0))))))   ; (<= N0 i) -> N0
;; common upper bound c of m0, N0
(quietly (lambda () (fact 'nn-pair-upper-bound cbe--m0 cbe--N0)
  (let ((fs (cbe--find (cbe--head? 'FORSOME)))) (and fs (ai fs))) (cbe--split)))
(define cbe--c (caddr (cbe--find (lambda (a) (and (pair? a)(eq? (car a) '<=)(equal? (cadr a) cbe--m0))))))
;; ew c; close c in NN; intro n_
(quietly (lambda () (ew cbe--c) (di)))
(cbe--fpred (lambda (a) (equal? a (list 'IN cbe--c 'NN)))) (quietly (lambda () (ass)))
(cbe--fhead 'FORALL)
(quietly (lambda () (di)(di)(di)))
(define cbe--gg (cbe--gf))
(define cbe--n (cadr (cadr (cadr cbe--gg))))

;; strictly-mono-ge-id FIRST (needs the STRICTLY-MONO-NN hyp), THEN unfold it.
(quietly (lambda () (fact 'strictly-mono-ge-id cbe--delta cbe--n)))     ; n_ <= delta(n_)
(quietly (lambda () (mac-h 'STRICTLY-MONO-NN cbe--Hmono) (cbe--split))) ; delta in FUN(NN,NN)
;; typings + transitivity, all forward via fact auto-detach (curried, no cuts)
(quietly (lambda ()
  (fact 'fun-apply-type-c cbe--delta 'NN 'NN cbe--n)        ; delta(n_) in NN
  (fact 'nn-in-rr cbe--m0) (fact 'nn-in-rr cbe--N0) (fact 'nn-in-rr cbe--c)
  (fact 'nn-in-rr cbe--n) (fact 'nn-in-rr (list cbe--delta cbe--n))
  (fact 'rr-le-trans-c cbe--m0 cbe--c cbe--n)               ; m0 <= n_
  (fact 'rr-le-trans-c cbe--N0 cbe--c cbe--n)               ; N0 <= n_
  (fact 'rr-le-trans-c cbe--N0 cbe--n (list cbe--delta cbe--n)))) ; N0 <= delta(n_)
;; delta(n_) in B: inst+ tail peels (in n_ NN) and (<= m0 n_)
(quietly (lambda () (inst+ (cbe--tail) cbe--n)))
;; d(g(delta n_),p)<=eps: inst+ caN0 peels (in delta(n_) NN),(in delta(n_) B),(N0<=delta(n_))
(quietly (lambda () (inst+ cbe--caN0 (list cbe--delta cbe--n))))
;; rewrite SUBSEQ in goal, close
(quietly (lambda () (mac 'SUBSEQ) (lam-b) (lam-b) (ass)))

(if (proof-done? *ps*)
    (qed 'coord-block-estimate)
    (error "coord-block-estimate-proof: proof did not complete"))
