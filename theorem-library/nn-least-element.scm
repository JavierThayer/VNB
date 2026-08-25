;;; theorem-library/nn-least-element.scm
;;; ===================================================================
;;; The well-ordering of NN, PROVEN from the well-ordering of ORD.
;;;
;;;   nn-least-element :
;;;     SUBSET(T, NN) and T nonempty  =>  T has a <=-least element.
;;;
;;; Was an ad-hoc asserted support in structure-library/ideal.scm; now a
;;; theorem resting on ord-well-ordered (ordinals.scm), the canonical home
;;; of the well-ordering principle.  The proof:
;;;   * T subset NN subset ORD, so ord-well-ordered gives a ORD-LE-least m;
;;;   * ORD-LE and numeric <= coincide on NN (ord-le-nn-compat), so m is
;;;     <=-least too.
;;;
;;; The ORD-LE <-> <= bridge is a CONDITIONAL biconditional, so it cannot be
;;; used as a rewrite macete; it is landed by `fact' and then consumed by the
;;; new iff-elim case of `ai' (primitive-inferences.scm) -- the machinery gap
;;; this proof exposed.
;;;
;;; Re-runnable at load (deterministic).  Needs ordinals (ord-well-ordered,
;;; nn-subset-ord, ord-le-nn-compat), the set kernel (subset-def), and the
;;; interactive tactics + qed.
;;; ===================================================================

;;; ---- helpers (subset of prop-3-15-proof.scm) ----
;;; `proof-leaves' and `any-pred' used to be defined HERE, and were consumed by
;;; interactive.scm, macetes.scm and eighteen other drivers.  They now live in
;;; driver-kit.scm.  The rest are file-local, and this file now loads in its own
;;; environment, so they cannot escape.
(define (sub? substr s) (and (string-search-forward substr s 0) #t))
(define (cur-sqn) (proof-state-focus *ps*))
(define (cur-goal-raw) (wff-formula (sequent-node-assertion (cur-sqn))))
(define (asm-set) (map wff-formula (sequent-node-assumptions (cur-sqn))))
(define (asm-find-pred pred)
  (let ((w (any-pred (lambda (w) (pred (wff-formula w)))
                     (sequent-node-assumptions (cur-sqn)))))
    (and w (wff-formula w))))
(define (focus-leaf-goal! raw)
  (let ((s (any-pred (lambda (s) (equal? (wff-formula (sequent-node-assertion s)) raw))
                     (proof-leaves))))
    (if s (begin (set-proof-state-focus! *ps* s) s)
        (error "focus-leaf-goal!: none equal to" (expression->string (make-wff raw))))))
(define (split-ands!)
  (let loop ()
    (let scan ((as (sequent-node-assumptions (cur-sqn))))
      (cond ((null? as) 'done)
            ((let ((f (wff-formula (car as)))) (and (pair? f) (eq? (car f) 'AND)))
             (ai (wff-formula (car as))) (loop))
            (else (scan (cdr as)))))))
(define (ai-body forsome-raw)            ; eliminate FORSOME hyp, return body added
  (let ((before (asm-set)))
    (ai forsome-raw)
    (any-pred (lambda (f) (not (member f before))) (asm-set))))
(define (forall-asm-into substr)         ; FORALL hyp whose body's consequent mentions substr
  (asm-find-pred (lambda (w) (and (pair? w) (eq? (car w) 'FORALL)
                  (let ((b (caddr w))) (and (pair? b) (eq? (car b) 'IMPLIES)
                       (sub? substr (expression->string (make-wff (caddr b))))))))))

;;; ===================================================================
(sp (make-wff
     '(FORALL T (IMPLIES (AND (SUBSET T NN) (FORSOME n (IN n T)))
        (FORSOME m (AND (IN m T) (FORALL k (IMPLIES (IN k T) (<= m k)))))))))
(di)                                     ; peel FORALL T
(define NLE-TT (cadr (cadr (cadr (cur-goal-raw)))))   ; from (... (SUBSET NLE-TT NN) ...)
(di)                                     ; asm (AND (SUBSET NLE-TT NN) (FORSOME n (IN n NLE-TT)))
(define MAINGOAL (cur-goal-raw))         ; (FORSOME m (AND (IN m NLE-TT) (FORALL k ...)))
(split-ands!)                            ; H_sub: SUBSET NLE-TT NN ; H_ne: FORSOME n (IN n NLE-TT)

;;; ---- supply ord-well-ordered's antecedent, then apply it ----
(define WO-ANTE `(AND (FORALL x (IMPLIES (IN x ,NLE-TT) (IN x ORD)))
                      (FORSOME w (IN w ,NLE-TT))))
(cut WO-ANTE)
(focus-leaf-goal! WO-ANTE) (di)          ; split the antecedent AND into A1 / A2

;; (A1) FORALL x. x in T => x in ORD
(focus-leaf-goal! `(FORALL x (IMPLIES (IN x ,NLE-TT) (IN x ORD))))
(di)                                      ; bounded-forall peel: asm (IN XX NLE-TT) ; goal (IN XX ORD)
(define XX (cadr (cur-goal-raw)))         ; (IN XX ORD) -> XX
(mac-h 'subset-def `(SUBSET ,NLE-TT NN))      ; H_sub -> FORALL x'. x' in T => x' in NN
(inst (forall-asm-into "nn") XX)
(detach! `(IMPLIES (IN ,XX ,NLE-TT) (IN ,XX NN)))
(fact 'nn-subset-ord XX)                  ; (IN XX NN) -> (IN XX ORD)
(ass)

;; (A2) FORSOME w. w in T  -- from the nonemptiness hypothesis
(focus-leaf-goal! `(FORSOME w (IN w ,NLE-TT)))
(let* ((hne (asm-find-pred (lambda (w) (and (pair? w) (eq? (car w) 'FORSOME)))))
       (body (ai-body hne))               ; (IN wn NLE-TT)
       (wn  (cadr body)))
  (ew wn))
(ass)

;; ---- ord-well-ordered now applies: least m under ORD-LE ----
(focus-leaf-goal! MAINGOAL)
(fact 'ord-well-ordered NLE-TT)               ; detaches WO-ANTE -> FORSOME m (AND (IN m T)(FORALL k. k in T => m ORD-LE k))
(define GENEX (asm-find-pred (lambda (w) (and (pair? w) (eq? (car w) 'FORSOME)))))
(define BODY  (ai-body GENEX))
(define MM    (cadr (cadr BODY)))         ; the least element
(define HMLE  (caddr BODY))               ; FORALL k. k in T => MM ORD-LE k
(split-ands!)                             ; H_mT: IN MM NLE-TT ; H_mle: HMLE

;; ---- witness m := MM ----
(ew MM)
(di)
(focus-leaf-goal! `(IN ,MM ,NLE-TT)) (ass)    ; first conjunct

;; ---- FORALL k. k in T => MM <= k ----
(focus-leaf-goal! `(FORALL k (IMPLIES (IN k ,NLE-TT) (<= ,MM k))))
(di)                                      ; bounded-forall peel: asm (IN KK NLE-TT) ; goal (<= MM KK)
(define KK (caddr (cur-goal-raw)))        ; (<= MM KK) -> KK

;; MM ORD-LE KK from the least-element property
(inst HMLE KK)
(detach! `(IMPLIES (IN ,KK ,NLE-TT) (ORD-LE ,MM ,KK)))

;; MM, KK in NN (via subset-def), then their ORD-LE/<= coincide
(mac-h 'subset-def `(SUBSET ,NLE-TT NN))
(define HSUBF (forall-asm-into "nn"))
(inst HSUBF MM) (detach! `(IMPLIES (IN ,MM ,NLE-TT) (IN ,MM NN)))
(inst HSUBF KK) (detach! `(IMPLIES (IN ,KK ,NLE-TT) (IN ,KK NN)))
(cut `(AND (IN ,MM NN) (IN ,KK NN)))
(focus-leaf-goal! `(AND (IN ,MM NN) (IN ,KK NN))) (di)
(focus-leaf-goal! `(IN ,MM NN)) (ass)
(focus-leaf-goal! `(IN ,KK NN)) (ass)
(focus-leaf-goal! `(<= ,MM ,KK))
(fact 'ord-le-nn-compat MM KK)            ; lands (IFF (ORD-LE MM KK) (<= MM KK))
(ai `(IFF (ORD-LE ,MM ,KK) (<= ,MM ,KK)))  ; iff-elim -> both implications
(detach! `(IMPLIES (ORD-LE ,MM ,KK) (<= ,MM ,KK)))
(ass)

;;; ===================================================================
(if (proof-done? *ps*)
    (qed 'nn-least-element)
    (begin (display ";; NOT DONE -- open leaves:\n")
           (for-each (lambda (s) (display "  ")
                       (display (expression->string (sequent-node-assertion s))) (newline))
                     (proof-leaves))))
