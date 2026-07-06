;;; theorem-library/block-family-combinatorial-proof.scm
;;;
;;; block-family-combinatorial, PROVEN to QED (was asserted 'reference in
;;; theorem-library/block-family-combinatorial.scm, retired here).
;;;
;;; Statement: for a set V, a sequence f : NN -> V, and a sequence cov of finite
;;; covers of V (cov(k) a finite cover, each k), there is a nested tower of
;;; INFINITE index blocks blk(0) supseteq blk(1) supseteq ... with, at each level
;;; k, all f(i) (i in blk(k)) lying in a single member U of cov(k).  The metric-
;;; free combinatorial core of block-family (cauchy-subsequence.scm).
;;;
;;; PROOF -- the construction the 'reference warrant described, mechanised, and
;;; the same shape as theorem-library/diagonalization.scm (dc-on-nn-pred with a
;;; SEP step set):
;;;   * carrier X = INF-SUBSETS(NN), base a = NN (blk(0));
;;;   * step set nxt(k, J) = { J_ in INF-SUBSETS(NN) : J_ subset J and some
;;;       U in cov(k) has f(i) in U for all i in J_ };
;;;   * totality of nxt IS cover-block-step (cov(k) finite by hypothesis) --
;;;     the single infinite-pigeonhole step;
;;;   * dc-on-nn-pred yields aux : NN -> INF-SUBSETS(NN), aux(0)=NN, and
;;;     aux(succ k) in nxt(k, aux k) -- i.e. aux(succ k) subset aux(k) and
;;;     captured by cov(k);
;;;   * index-shift blk(k) := aux(succ k) delivers nesting (from the step at
;;;     succ k) and level-k capture (from the step at k) verbatim.
;;; The asserted leaves are cover-block-step, dc-on-nn-pred, nn-in-inf-subsets,
;;; and the NN/plumbing typing facts (see the proof bill at qed).
;;;
;;; Loads after interactive (needs sp/di/...) and after block-family-
;;; combinatorial.scm (cover-block-step, IS-FINITE-COVER) + dc-on-nn.scm +
;;; inf-subsets.scm; before cauchy-subseq-proof.scm, which cites it.

;;; ---- proof-local helpers (bfc- prefixed; top-level per loader convention) ----
(define (bfc-sqn) (proof-state-focus *ps*))
(define (bfc-goal) (wff-formula (sequent-node-assertion (bfc-sqn))))
(define (bfc-asms) (map wff-formula (sequent-node-assumptions (bfc-sqn))))
(define (bfc-any pred lst)
  (let loop ((l lst)) (cond ((null? l) #f) ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (bfc-head? h e) (and (pair? e) (eq? (car e) h)))
(define (bfc-find pred) (bfc-any pred (bfc-asms)))
(define (bfc-leaves)
  (filter (lambda (nd) (and (not (sequent-node-grounded? nd)) (null? (sequent-node-in-arrows nd))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (bfc-focus! raw)
  (let loop ((ls (bfc-leaves)))
    (cond ((null? ls) (error "bfc: no open leaf equals" raw))
          ((equal? (wff-formula (sequent-node-assertion (car ls))) raw)
           (set-proof-state-focus! *ps* (car ls)) (car ls))
          (else (loop (cdr ls))))))
(define (bfc-new thunk)
  (let ((before (bfc-asms))) (thunk)
    (bfc-any (lambda (f) (not (member f before))) (bfc-asms))))
(define (bfc-di*)
  (let loop ()
    (let* ((g (bfc-goal)) (h (and (pair? g) (car g))))
      (when (memq h '(FORALL IMPLIES)) (di) (loop)))))
(define (bfc-occurs? sym e)
  (cond ((equal? sym e) #t) ((pair? e) (or (bfc-occurs? sym (car e)) (bfc-occurs? sym (cdr e)))) (else #f)))
(define (bfc-beta!)
  (let loop ((prev #f) (n 8))
    (let ((g (bfc-goal)))
      (when (and (> n 0) (not (equal? g prev)))
        (quietly (lambda () (vnb-guard (lambda () (lam-b)))))
        (loop g (- n 1))))))

;;; ---- statement ----
(define bfc-stmt
  '(FORALL V (IMPLIES (IN V SET)
     (FORALL f (IMPLIES (IN f (FUN NN V))
       (FORALL cov (IMPLIES
         (FORALL k (IMPLIES (IN k NN) (IS-FINITE-COVER (cov k) V)))
         (FORSOME blk (AND (IN blk (FUN NN (INF-SUBSETS NN)))
                      (AND (FORALL k (IMPLIES (IN k NN) (SUBSET (blk (succ k)) (blk k))))
                           (FORALL k (IMPLIES (IN k NN)
                             (FORSOME U (AND (IN U (cov k))
                                        (FORALL i (IMPLIES (IN i (blk k)) (IN (f i) U)))))))))))))))))

(sp (make-wff bfc-stmt))
(bfc-di*)
(define bfc-main (bfc-goal))
;; capture eigenvars V, f, cov
(define bfc-V (cadr (bfc-find (lambda (a) (bfc-head? 'IN a)))))     ; (IN V SET) is first IN
(define bfc-Hcov (bfc-find (lambda (a) (and (bfc-head? 'FORALL a) (bfc-occurs? 'IS-FINITE-COVER a)))))
(define bfc-IFC (caddr (caddr bfc-Hcov)))          ; (IS-FINITE-COVER (cov k) V)
(define bfc-COV (car (cadr bfc-IFC)))
(define bfc-Vc  (caddr bfc-IFC))
(define bfc-F (cadr (bfc-find (lambda (a) (and (bfc-head? 'IN a)
                                               (equal? (caddr a) `(FUN NN ,bfc-Vc)))))))

;;; ---- step set NXT and its per-(k,u) SEP form ----
(define bfc-NXT
  `(VNB-LAMBDA (LIST kx ux)
     (SEP jx (INF-SUBSETS NN)
       (AND (SUBSET jx ux)
            (FORSOME um (AND (IN um (,bfc-COV kx))
                        (FORALL i (IMPLIES (IN i jx) (IN (,bfc-F i) um)))))))))
(define (bfc-app k u) (list bfc-NXT k u))
(define (bfc-sep kk uu)
  `(SEP jx (INF-SUBSETS NN)
     (AND (SUBSET jx ,uu)
          (FORSOME um (AND (IN um (,bfc-COV ,kk))
                      (FORALL i (IMPLIES (IN i jx) (IN (,bfc-F i) um))))))))

;;; ---- Phase A: totality of NXT (dc-on-nn-pred hypothesis) via cover-block-step ----
(define bfc-TOT
  `(FORALL k (IMPLIES (IN k NN)
     (FORALL u (IMPLIES (IN u (INF-SUBSETS NN))
       (FORSOME y (AND (IN y (INF-SUBSETS NN)) (IN y ,(bfc-app 'k 'u)))))))))
(cut bfc-TOT)
(bfc-focus! bfc-TOT)
(bfc-di*)                                   ; asms (IN kk NN),(IN uu (INF-SUBSETS NN)); goal FORSOME y
(define bfc-gy (bfc-goal))
(define bfc-appku (caddr (caddr (caddr bfc-gy))))   ; (NXT kk uu)
(define bfc-kk (cadr bfc-appku))
(define bfc-uu (caddr bfc-appku))
(inst+ bfc-Hcov bfc-kk)                     ; (IS-FINITE-COVER (cov kk) V)
(define bfc-Hcbs
  (bfc-new (lambda () (fact 'cover-block-step bfc-V bfc-F `(,bfc-COV ,bfc-kk) bfc-uu))))
;; skolemize the cover-block-step witness y (keep its inner AND intact)
(define bfc-b1 (bfc-new (lambda () (ai bfc-Hcbs))))
(define bfc-y (cadr (cadr bfc-b1)))
(ai bfc-b1)                                 ; -> (IN y INF) ; (AND (SUBSET y uu) (FORSOME U ...))
(ew bfc-y)
(di)                                        ; (IN y INF) ; (IN y (NXT kk uu))
(bfc-focus! `(IN ,bfc-y (INF-SUBSETS NN))) (ass)
(bfc-focus! `(IN ,bfc-y ,(bfc-app bfc-kk bfc-uu)))
(cut `(== ,(bfc-app bfc-kk bfc-uu) ,(bfc-sep bfc-kk bfc-uu)))
(bfc-focus! `(== ,(bfc-app bfc-kk bfc-uu) ,(bfc-sep bfc-kk bfc-uu))) (lam-b) (qrfl)
(bfc-focus! `(IN ,bfc-y ,(bfc-app bfc-kk bfc-uu)))
(subst `(== ,(bfc-app bfc-kk bfc-uu) ,(bfc-sep bfc-kk bfc-uu)))
(sep-mi)                                    ; -> (IN y INF) ; pred[y] = the kept AND (alpha)
(quietly (lambda () (ass-all)))

;;; ---- Phase B: apply dc-on-nn-pred; extract aux, aux(0)=NN, step membership ----
(bfc-focus! bfc-main)
(ta 'nn-is-set)
(fact 'inf-subsets-is-set 'NN)              ; (IN (INF-SUBSETS NN) SET)
(ta 'nn-in-inf-subsets)                     ; (IN NN (INF-SUBSETS NN))
(define bfc-CONCL
  (bfc-new (lambda () (fact 'dc-on-nn-pred '(INF-SUBSETS NN) 'NN bfc-NXT))))
(define bfc-body (bfc-new (lambda () (ai bfc-CONCL))))
(define bfc-aux (cadr (cadr bfc-body)))
(ai bfc-body)                               ; (IN aux (FUN NN INF)) ; (AND (=..) (FORALL..))
(define bfc-body2 (bfc-find (lambda (a) (and (bfc-head? 'AND a) (bfc-head? '= (cadr a))))))
(ai bfc-body2)                              ; (= (aux 0) NN) ; Hstep
(define bfc-Hstep
  (bfc-find (lambda (a) (and (bfc-head? 'FORALL a)
                             (let ((b (caddr a))) (and (bfc-head? 'IMPLIES b)
                                                       (bfc-head? 'IN (caddr b))
                                                       (bfc-occurs? 'succ (caddr b))))))))

;;; ---- Phase C: HstepP -- per k, nesting + capture read off the SEP membership ----
(define bfc-HstepP
  `(FORALL k (IMPLIES (IN k NN)
     (AND (SUBSET (,bfc-aux (succ k)) (,bfc-aux k))
          (FORSOME um (AND (IN um (,bfc-COV k))
                      (FORALL i (IMPLIES (IN i (,bfc-aux (succ k))) (IN (,bfc-F i) um)))))))))
(cut bfc-HstepP)
(bfc-focus! bfc-HstepP)
(di)
(define bfc-pg (bfc-goal))
(define bfc-kp (cadr (cadr (cadr (cadr bfc-pg)))))
(bfc-new (lambda () (inst+ bfc-Hstep bfc-kp)))   ; (IN (aux(succ kp)) (NXT kp (aux kp)))
(define bfc-NXTk (bfc-app bfc-kp (list bfc-aux bfc-kp)))
(define bfc-SEPk (bfc-sep bfc-kp (list bfc-aux bfc-kp)))
(cut `(== ,bfc-NXTk ,bfc-SEPk))
(bfc-focus! `(== ,bfc-NXTk ,bfc-SEPk)) (lam-b) (qrfl)
(bfc-focus! bfc-pg)
(cut `(IN (,bfc-aux (succ ,bfc-kp)) ,bfc-SEPk))
(bfc-focus! `(IN (,bfc-aux (succ ,bfc-kp)) ,bfc-SEPk)) (subst `(== ,bfc-SEPk ,bfc-NXTk)) (ass)
(bfc-focus! bfc-pg)
(sep-me `(IN (,bfc-aux (succ ,bfc-kp)) ,bfc-SEPk))    ; adds base + pred as asms
(ass)                                                 ; goal = pred (the AND) = added asm

;;; ---- Phase D: witness blk := lambda k. aux(succ k); typing; split conjunction ----
(bfc-focus! bfc-main)
(define bfc-blk `(VNB-LAMBDA k (,bfc-aux (succ k))))
(define bfc-Gnest `(FORALL k (IMPLIES (IN k NN) (SUBSET (,bfc-blk (succ k)) (,bfc-blk k)))))
(define bfc-Gcap `(FORALL k (IMPLIES (IN k NN)
                   (FORSOME U (AND (IN U (,bfc-COV k))
                              (FORALL i (IMPLIES (IN i (,bfc-blk k)) (IN (,bfc-F i) U))))))))
(ew bfc-blk)
(di)                                        ; (IN blk (FUN..)) ; (AND Gnest Gcap)
(bfc-focus! `(IN ,bfc-blk (FUN NN (INF-SUBSETS NN))))
(lam-t)
(bfc-di*)                                   ; eigen kt ; goal (IN (aux(succ kt)) (INF-SUBSETS NN))
(define bfc-tg (bfc-goal))
(define bfc-kt (cadr (cadr (cadr bfc-tg))))
(fact 'nn-succ-closed bfc-kt)
(fact 'fun-apply-type-c bfc-aux 'NN '(INF-SUBSETS NN) `(succ ,bfc-kt))
(ass)
(bfc-focus! `(AND ,bfc-Gnest ,bfc-Gcap))
(di)

;;; ---- Phase E: nesting  blk(succ k) = aux(succ(succ k)) subset aux(succ k) = blk(k) ----
(bfc-focus! bfc-Gnest)
(di)
(define bfc-ng (bfc-goal))
(define bfc-kn (cadr (cadr (cadr bfc-ng))))
(fact 'nn-succ-closed bfc-kn)
(bfc-new (lambda () (inst+ bfc-HstepP `(succ ,bfc-kn))))
(define bfc-andn (bfc-find (lambda (a) (and (bfc-head? 'AND a) (bfc-head? 'SUBSET (cadr a))
                                            (bfc-occurs? `(succ (succ ,bfc-kn)) a)))))
(ai bfc-andn)
(bfc-beta!)                                 ; reduce the two blk applications in the goal
(ass)

;;; ---- Phase F: capture  blk(k) = aux(succ k) captured by cov(k) ----
(bfc-focus! bfc-Gcap)
(di)
(define bfc-cg (bfc-goal))
(define bfc-kc (cadr (caddr (cadr (caddr bfc-cg)))))
(bfc-new (lambda () (inst+ bfc-HstepP bfc-kc)))
(define bfc-andc (bfc-find (lambda (a) (and (bfc-head? 'AND a) (bfc-head? 'SUBSET (cadr a))
                                            (bfc-occurs? `(,bfc-COV ,bfc-kc) a)))))
(ai bfc-andc)
(bfc-beta!)                                 ; reduce (blk kc) -> (aux (succ kc)) in the goal
(ass)

;;; ---- install ----
(if (proof-done? *ps*)
    (qed 'block-family-combinatorial)
    (begin (display ";; block-family-combinatorial NOT DONE -- open leaves:\n")
           (for-each (lambda (nd) (display ";;   ")
                       (display (expression->string (sequent-node-assertion nd))) (newline))
                     (bfc-leaves))))
