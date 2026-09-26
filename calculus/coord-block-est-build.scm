;;; calculus/coord-block-est-build.scm -- BUILD SCRATCH (not loaded)
;;; Prove coord-block-estimate: convergence ALONG a block B transfers to a
;;; reindexing whose tail lands in B.

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (find-asm pred) (let loop ((as (asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (has? sym form) (cond ((equal? form sym) #t)
  ((pair? form) (or (has? sym (car form)) (has? sym (cdr form)))) (else #f)))
(define (--- t) (newline)(display ";;; ===== ")(display t)(display " =====")(newline))
(define (dump tag) (display ";;; [")(display tag)(display "] done?=")(display (proof-done? *ps*))
  (display "  GOAL: ")(write (gf))(newline))
(define (split-ands) (let loop ((n 0)) (let ((a (find-asm (head? 'AND))))
  (cond ((and a (< n 12)) (ai a) (loop (+ n 1))) (else n)))))
(define (leaves) (filter (lambda (n) (null? (sequent-node-in-arrows n)))
                         (dg-ungrounded-nodes (proof-state-dg *ps*))))
;; focus the MATCHING leaf with the most assumptions (the live, deepest copy --
;; same-formula leaves from earlier cuts have fewer hyps and must not win)
(define (fpred p)
  (let ((cands (filter (lambda (n) (p (wff-formula (sequent-node-assertion n)))) (leaves))))
    (and (pair? cands)
         (begin (dk-focus!
                  (car (sort cands (lambda (a b)
                    (> (length (sequent-node-assumptions a))
                       (length (sequent-node-assumptions b)))))))
                #t))))
(define (fhead h) (fpred (lambda (a) (and (pair? a) (eq? (car a) h)))))
(define (lheads) (map (lambda (n) (let ((a (wff-formula (sequent-node-assertion n)))) (if (pair? a)(car a) a))) (leaves)))
(define (estab a b g)
  (cut (list 'AND a b))
  (fpred (lambda (x) (equal? x (list 'AND a b)))) (di)
  (fpred (lambda (x) (equal? x a))) (ass)
  (fpred (lambda (x) (equal? x b))) (ass)
  (fpred (lambda (x) (equal? x g))))
;; establish (<= a c) from (<= a b),(<= b c) in ctx; refocus g
(define (letr a b c g)
  (fact 'nn-in-rr a) (fact 'nn-in-rr b) (fact 'nn-in-rr c)
  (estab (list '<= a b) (list '<= b c) g)
  (fact 'rr-le-trans a b c))
;; detach (IMPLIES A C) with A (or A's conjuncts) in ctx; leaves C in ctx; refocus g
(define (detach-impl impl g)
  (let ((C (caddr impl)) (A (cadr impl)))
    (cut C) (fpred (lambda (x) (equal? x C)))
    (bc impl)
    (fpred (lambda (x) (equal? x A)))            ; focus the antecedent bc opened
    (if (and (pair? A) (eq? (car A) 'AND)) (begin (di) (ass-all)) (ass))
    (fpred (lambda (x) (equal? x g)))))
;; the once-detached implication: head IMPLIES, ANTECEDENT head in heads (<= / AND
;; -- not a typing IN, which inst+ already peeled), conclusion mentions `incl'
(define (find-impl-ante heads . incl)
  (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'IMPLIES)(pair? (cadr a))
                             (memq (caadr a) heads)
                             (let loop ((xs incl)) (or (null? xs) (and (has? (car xs) a) (loop (cdr xs)))))))))

;; The tail-threshold bound var is named m0, NOT n0: the cainner existential is
;; skolemized into the kernel's fresh-name namespace (n_1, n_2, ...), and a lemma
;; var literally named `n0' COLLIDES with that namespace -- the skolemizer reuses
;; n_k, so the tail threshold and the convergence skolem N0 end up the same object
;; (proved exhaustively: (eq n0 N0)=#t, and the symbol n0 even renders as "n_11").
;; Naming it m0 (outside the n_* namespace) keeps raw extraction faithful and lets
;; the plain inst+ flow go through.  DRIFT LESSON: name lemma bound vars away from
;; the skolemizer's n_* namespace.
(sp (make-wff
     '(FORALL s (FORALL g (FORALL B (FORALL p (FORALL delta (FORALL m0
        (IMPLIES (CONVERGES-ALONG s g B p)
        (IMPLIES (STRICTLY-MONO-NN delta)
        (IMPLIES (IN m0 NN)
        (IMPLIES (FORALL j (IMPLIES (IN j NN) (IMPLIES (<= m0 j) (IN (delta j) B))))
          (CONVERGES-TO s (SUBSEQ g delta) p)))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)(di)(di)(di)(di)))
(define s*   (cadr (find-asm (head? 'CONVERGES-ALONG))))
(define Hca  (find-asm (head? 'CONVERGES-ALONG)))
(define g*   (caddr Hca))
(define B*   (cadddr Hca))
(define p*   (car (cddddr Hca)))
(define delta* (cadr (find-asm (head? 'STRICTLY-MONO-NN))))
(define Hmono (find-asm (head? 'STRICTLY-MONO-NN)))
;; tail = (FORALL j (IMPLIES (IN j NN) (IMPLIES (<= m0 j) (IN (delta j) B)))).
;; Signature: has <=, delta and B, no FUN (the STRICTLY-MONO-NN unfold is also a
;; FORALL with delta and a bound `b', but it carries FUN).
(define (live-tail) (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(has? '<= a)(has? delta* a)(has? B* a)(not (has? 'FUN a))))))
(define m0* (cadr (cadr (caddr (caddr (live-tail))))))     ; (<= m0 j) -> m0 (faithful)
(dump "after strip")
(display ";;; s*=")(write s*)(display " delta*=")(write delta*)(display " m0*=")(write m0*)(newline)

;; unfold CONVERGES-ALONG hyp
(quietly (lambda () (mac-h 'CONVERGES-ALONG Hca) (split-ands)))
(define cainner (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(has? g* a)(has? B* a)(has? 'POS-RR a)))))

;; unfold goal, dispatch structural
(quietly (lambda () (mac 'CONVERGES-TO)))
(quietly (lambda ()
  (let loop ((n 0))
    (when (< n 8)
      (cond ((fhead 'AND) (di) (loop (+ n 1)))
            ((fhead 'IS-METRIC-SPACE) (ass) (loop (+ n 1)))
            ((fpred (lambda (a) (and (pair? a)(eq? (car a) 'IN)(equal? (caddr a) (list 'FUN 'NN (list 'X s*))))))
             (if (has? 'SUBSEQ (gf)) (begin (bc* 'subseq-is-fun)(di)(ass-all)) (ass))
             (loop (+ n 1)))
            (else 'done))))))
;; the eps goal
(fhead 'FORALL)
(quietly (lambda () (di)(di)))
(define eps* (cadr (find-asm (head? 'POS-RR))))
;; N0 from cainner @ eps
(quietly (lambda () (inst+ cainner eps*)
  (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs))) (split-ands)))
(define caN0 (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(has? g* a)(has? B* a)(not (has? 'POS-RR a))))))
(define N0* (cadr (cadr (caddr (caddr (caddr caN0))))))    ; (<= N0 i) -> N0 (faithful)
;; common upper bound c of m0, N0
(quietly (lambda () (fact 'nn-pair-upper-bound m0* N0*)
  (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs))) (split-ands)))
(define c* (caddr (find-asm (lambda (a) (and (pair? a)(eq? (car a) '<=)(equal? (cadr a) m0*))))))
(dump "after N0, c")
(display ";;; m0*=")(write m0*)(display " N0*=")(write N0*)(display " c*=")(write c*)(newline)
;; ew c; close c in NN; intro n_
(quietly (lambda () (ew c*) (di)))
(fpred (lambda (a) (equal? a (list 'IN c* 'NN)))) (quietly (lambda () (ass)))
(fhead 'FORALL)
(quietly (lambda () (di)(di)(di)))
(define gg (gf))
(define n_* (cadr (cadr (cadr gg))))
(dump "estimate goal")

;; strictly-mono-ge-id FIRST (needs the STRICTLY-MONO-NN hyp), THEN unfold it for
;; fun-apply-type-c.
(quietly (lambda () (fact 'strictly-mono-ge-id delta* n_*)))            ; n_ <= delta(n_)
(quietly (lambda () (mac-h 'STRICTLY-MONO-NN Hmono) (split-ands)))      ; delta in FUN(NN,NN)
;; typings + transitivity, all forward via fact auto-detach (curried, no cuts)
(quietly (lambda ()
  (fact 'fun-apply-type-c delta* 'NN 'NN n_*)           ; delta(n_) in NN
  (fact 'nn-in-rr m0*) (fact 'nn-in-rr N0*) (fact 'nn-in-rr c*)
  (fact 'nn-in-rr n_*) (fact 'nn-in-rr (list delta* n_*))
  (fact 'rr-le-trans-c m0* c* n_*)                      ; m0 <= n_
  (fact 'rr-le-trans-c N0* c* n_*)                      ; N0 <= n_
  (fact 'rr-le-trans-c N0* n_* (list delta* n_*))))     ; N0 <= delta(n_)
(display ";;; m0<=n_? ")(write (and (find-asm (lambda(a)(equal? a (list '<= m0* n_*)))) #t))
(display " N0<=delta(n_)? ")(write (and (find-asm (lambda(a)(equal? a (list '<= N0* (list delta* n_*))))) #t))(newline)
;; delta(n_) in B: inst+ tail peels (in n_ NN) and (<= m0 n_)
(quietly (lambda () (inst+ (live-tail) n_*)))
(display ";;; delta(n_) in B? ")(write (and (find-asm (lambda(a)(equal? a (list 'IN (list delta* n_*) B*)))) #t))(newline)
;; d(g(delta n_),p)<=eps: inst+ caN0 peels (in delta(n_) NN),(in delta(n_) B),(N0<=delta(n_))
(quietly (lambda () (inst+ caN0 (list delta* n_*))))
(display ";;; d(g(delta n_),p)<=eps? ")
(write (and (find-asm (lambda(a)(equal? a (list '<= (list (list 'D s*) (list g* (list delta* n_*)) p*) eps*)))) #t))(newline)
;; rewrite SUBSEQ in goal, close
(quietly (lambda () (mac 'SUBSEQ) (lam-b) (lam-b) (ass)))
(dump "after close")
(display ";;; PROOF DONE? ")(write (proof-done? *ps*))(display "  ungrounded: ")
(write (length (dg-ungrounded-nodes (proof-state-dg *ps*))))(newline)
(display ";;; OPEN LEAVES:\n")
(for-each (lambda (n) (display ";;;   ")(write (wff-formula (sequent-node-assertion n)))(newline)) (leaves))
(qed 'coord-block-estimate)
(--- "END v3")
