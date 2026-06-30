;;; theorem-library/subseq-convergence-proof.scm
;;; ====================================================================
;;; subseq-of-convergent -- PROVEN.
;;;
;;;   A subsequence of a convergent sequence converges to the same limit:
;;;   CONVERGES-TO(s,f,L) and STRICTLY-MONO-NN(phi) => CONVERGES-TO(s,SUBSEQ(f,phi),L).
;;;
;;; A foundational convergence brick (was missing), and a building block toward
;;; the coordinatewise-diagonal-subseq keystone.  Proof: given eps, f->L supplies
;;; N0 with d(f m,L)<=eps for m>=N0; for n>=N0 the reindex phi(n) >= n >= N0
;;; (strictly-mono-ge-id), so d(f(phi n),L)=d(SUBSEQ(f,phi)(n),L)<=eps.
;;;
;;; Modulo {strictly-mono-ge-id, fun-apply-type, nn-in-rr, rr-le-trans,
;;; subseq-is-fun} + the CONVERGES-TO/STRICTLY-MONO defs.  Loads in the
;;; interactive phase (sp/di/mac/fact/qed).  Build: calculus/subseq-conv-build.scm.
;;; ====================================================================

(define (sc--gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (sc--asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (sc--find pred) (let loop ((as (sc--asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (sc--head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (sc--has? sym form) (cond ((equal? form sym) #t)
  ((pair? form) (or (sc--has? sym (car form)) (sc--has? sym (cdr form)))) (else #f)))
(define (sc--split) (let loop ((n 0)) (let ((a (sc--find (sc--head? 'AND))))
  (cond ((and a (< n 12)) (ai a) (loop (+ n 1))) (else n)))))
(define (sc--leaves) (filter (lambda (n) (null? (sequent-node-in-arrows n)))
                             (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (sc--fpred p) (let loop ((gs (sc--leaves)))
  (cond ((null? gs) #f)
        ((p (wff-formula (sequent-node-assertion (car gs)))) (set! *ps* (focus-on *ps* (car gs))) #t)
        (else (loop (cdr gs))))))
(define (sc--fhead h) (sc--fpred (lambda (a) (and (pair? a) (eq? (car a) h)))))
(define (sc--estab a b g)   ; ensure (AND a b) in ctx (a,b present); refocus goal g
  (cut (list 'AND a b))
  (sc--fpred (lambda (x) (equal? x (list 'AND a b)))) (di)
  (sc--fpred (lambda (x) (equal? x a))) (ass)
  (sc--fpred (lambda (x) (equal? x b))) (ass)
  (sc--fpred (lambda (x) (equal? x g))))

(sp (make-wff
     '(FORALL s (FORALL f (FORALL phi (FORALL L
        (IMPLIES (CONVERGES-TO s f L)
          (IMPLIES (STRICTLY-MONO-NN phi)
            (CONVERGES-TO s (SUBSEQ f phi) L)))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)))
(define sc--s   (cadr (sc--find (sc--head? 'CONVERGES-TO))))
(define sc--Hc  (sc--find (sc--head? 'CONVERGES-TO)))
(define sc--f   (caddr sc--Hc))
(define sc--L   (cadddr sc--Hc))
(define sc--phi (cadr (sc--find (sc--head? 'STRICTLY-MONO-NN))))
(define sc--Hm  (sc--find (sc--head? 'STRICTLY-MONO-NN)))

;; unfold the convergent hypothesis
(quietly (lambda () (mac-h 'CONVERGES-TO sc--Hc) (sc--split)))
(define sc--inner (sc--find (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)
   (sc--has? sc--f a)(sc--has? '<= a)(sc--has? 'POS-RR a)))))

;; unfold goal; close IS-MS / SUBSEQ-typing / L-typing conjuncts
(quietly (lambda () (mac 'CONVERGES-TO)))
(quietly (lambda ()
  (let loop ((n 0))
    (when (< n 8)
      (cond ((sc--fhead 'AND) (di) (loop (+ n 1)))
            ((sc--fhead 'IS-METRIC-SPACE) (ass) (loop (+ n 1)))
            ((sc--fpred (lambda (a) (and (pair? a)(eq? (car a) 'IN)
                                         (equal? (caddr a) (list 'FUN 'NN (list 'PTS sc--s))))))
             (if (sc--has? 'SUBSEQ (sc--gf)) (begin (bc* 'subseq-is-fun)(di)(ass-all)) (ass))
             (loop (+ n 1)))
            (else 'done))))))

;; the eps goal
(sc--fhead 'FORALL)
(quietly (lambda () (di)(di)))
(define sc--eps (cadr (sc--find (sc--head? 'POS-RR))))
(quietly (lambda () (inst+ sc--inner sc--eps)
  (let ((fs (sc--find (sc--head? 'FORSOME)))) (and fs (ai fs))) (sc--split)))
(define sc--N0 (let ((a (sc--find (lambda (a) (and (pair? a)(eq? (car a) 'IN)(equal? (caddr a) 'NN)))))) (and a (cadr a))))
(define sc--cN0 (sc--find (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)
   (sc--has? sc--f a)(sc--has? '<= a)(not (sc--has? 'POS-RR a))))))
(quietly (lambda () (ew sc--N0) (di)))
(sc--fpred (lambda (a) (equal? a (list 'IN sc--N0 'NN)))) (quietly (lambda () (ass)))
(sc--fhead 'FORALL)
(quietly (lambda () (di)(di)(di)))
(define sc--gg (sc--gf))
(define sc--n (cadr (cadr (cadr sc--gg))))

;; phi(n) >= n ; phi(n) in NN ; N0 <= phi(n) ; convergence @ phi(n) ; close
(quietly (lambda () (fact 'strictly-mono-ge-id sc--phi sc--n)))
(quietly (lambda () (mac-h 'STRICTLY-MONO-NN sc--Hm) (sc--split)))
(sc--estab (list 'IN sc--phi (list 'FUN 'NN 'NN)) (list 'IN sc--n 'NN) sc--gg)
(quietly (lambda () (fact 'fun-apply-type sc--phi 'NN 'NN sc--n)))
(quietly (lambda () (fact 'nn-in-rr sc--N0) (fact 'nn-in-rr sc--n) (fact 'nn-in-rr (list sc--phi sc--n))))
(sc--estab (list '<= sc--N0 sc--n) (list '<= sc--n (list sc--phi sc--n)) sc--gg)
(quietly (lambda () (fact 'rr-le-trans sc--N0 sc--n (list sc--phi sc--n))))
(sc--estab (list 'IN (list sc--phi sc--n) 'NN) (list '<= sc--N0 (list sc--phi sc--n)) sc--gg)
(quietly (lambda () (and sc--cN0 (inst+ sc--cN0 (list sc--phi sc--n)))))
(quietly (lambda () (mac 'SUBSEQ) (lam-b) (lam-b) (ass)))

(if (proof-done? *ps*)
    (qed 'subseq-of-convergent)
    (error "subseq-convergence-proof: proof did not complete"))
