;;; theorem-library/enum-append.scm -- enum-append-is-bijection, moved out of
;;; theorem-library/finsum-insert.scm on 2026-09-20 (batch 9-B, CARD := CARD-STAR).
;;;
;;;   enum-append-is-bijection   n in NN, sg in SET, pt in SET, pt not in sg,
;;;                              enm in BIJECTION(OS n, sg)
;;;                                =>  lambda i in OS(succ n). IF i in OS n THEN enm(i) ELSE pt
;;;                                    in BIJECTION(OS(succ n), sg u {pt})
;;;
;;; WHY IT MOVED.  It is the "EXTEND-BY" brick, and the one thing
;;; theorem-library/rake-card-star-laws.scm needs from finsum-insert.scm.  The CARD
;;; development now loads far above finsum-insert.scm, whose other theorems
;;; (finsum-insert, finsum-insert-ag, finsum-empty) rest on the CARD laws and must stay
;;; below them.  Nothing else in the tree cites enum-append-is-bijection, and
;;; finsum-insert.scm does not use it itself, so the extraction is clean.
;;;
;;; Its citations are the base theory, structure-library/ordinals, bijection-membership-iff
;;; (structure-library/bijection) and `ord-segment-self' (theorem-library/rake-inverse-bij),
;;; which loads immediately above this file.  The original is
;;; archive/2026-09-20-card-defined/finsum-insert-enum-append.scm.
;;;
;;; The helper block below is copied verbatim from finsum-insert.scm and keeps its `fsi-'
;;; prefix; each theorem-library file gets its own environment, so the two copies do not
;;; meet.

;;; ---------------------------------------------------------------------------
;;; helpers

(define (fsi-goal) (dk-goal))

(define (fsi-grounded! node who)
  (if (not (sequent-node-grounded? node))
      (error "fsi: leaf left open at" who (expression->string (dk-goal-of node)))))

;; Among LEAVES (as dk-opened returns them), the unique one whose GOAL satisfies PRED.
(define (fsi-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "fsi-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "fsi-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

;; The first (IF c a b) subterm of EXPR, in pre-order, whose condition satisfies PRED.
(define (fsi-find-if expr pred)
  (cond ((not (pair? expr)) #f)
        ((and (eq? (car expr) 'IF) (= (length expr) 4) (pred (cadr expr))) expr)
        (#t (let loop ((es expr))
              (cond ((null? es) #f)
                    ((not (pair? es)) #f)
                    (#t (or (fsi-find-if (car es) pred) (loop (cdr es)))))))))

;; `if-true' / `if-false' on the conditional term IFT.  The kernel rule spawns the
;; condition (resp. its negation) as a SIDE leaf and lands (= IFT branch) in the MAIN
;; branch.  CLOSER closes the side leaf (default `ass'); focus is left on the main branch.
;; Returns the landed equation.
(define (fsi-if-land! which ift . opt)
  (let* ((closer (if (pair? opt) (car opt) ass))
         (p      (cadr ift))
         (want   (if (eq? which 'true) p (list 'NOT p)))
         (val    (if (eq? which 'true) (caddr ift) (cadddr ift)))
         (new    (dk-opened (lambda () (if (eq? which 'true) (if-true ift) (if-false ift)))))
         (side   (fsi-leaf new (lambda (g) (alpha-equiv? g want)) "if side condition"))
         (main   (fsi-leaf new (lambda (g) (not (alpha-equiv? g want))) "if main branch")))
    (dk-focus! side) (closer) (fsi-grounded! side 'fsi-if-land!)
    (dk-focus! main)
    (list '= ift val)))

;; Reduce, IN THE GOAL, the first IF whose condition satisfies PRED, then substitute the
;; landed equation into the goal.
(define (fsi-reduce-if! which pred . opt)
  (let ((ift (or (fsi-find-if (fsi-goal) pred)
                 (error "fsi-reduce-if!: no IF with the wanted condition in"
                        (expression->string (fsi-goal))))))
    (subst (apply fsi-if-land! which ift opt))))

;; mac-h that also closes the side-condition leaves a GUARDED macete spawns (by `ass'),
;; and errors if the rewrite did nothing.
(define (fsi-mac-h! name hyp)
  (let* ((g0    (fsi-goal))
         (new   (dk-opened (lambda () (mac-h name hyp))))
         (sides (filter (lambda (l) (not (alpha-equiv? (dk-goal-of l) g0))) new))
         (mains (filter (lambda (l) (alpha-equiv? (dk-goal-of l) g0)) new)))
    (for-each (lambda (s) (dk-focus! s) (ass) (fsi-grounded! s (list 'fsi-mac-h! name))) sides)
    (if (null? mains) (error "fsi-mac-h!: no main branch after" name (expression->string hyp)))
    (dk-focus! (car mains))))

(define (fsi-check-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; fsi: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "fsi: proof not complete" name))))
;;; ---------------------------------------------------------------------------
;;; enum-append-is-bijection:  given a bijection enm : OS(n) -> sg and a set pt not in sg,
;;;
;;;   psi = lambda i in OS(succ n). IF i in OS(n) THEN enm(i) ELSE pt
;;;
;;; is a bijection OS(succ n) -> sg u {pt}.  Guards curried so `fact' detaches them.

(define (fsi-psi enm pt n)
  `(VNB-LAMBDA i (ORD-SEGMENT (succ ,n)) (IF (IN i (ORD-SEGMENT ,n)) (,enm i) ,pt)))

(define fsi-append-stmt
  `(FORALL n (IMPLIES (IN n NN)
     (FORALL sg (IMPLIES (IN sg SET)
     (FORALL pt (IMPLIES (IN pt SET) (IMPLIES (NOT (IN pt sg))
     (FORALL enm (IMPLIES (IN enm (BIJECTION (ORD-SEGMENT n) sg))
       (IN ,(fsi-psi 'enm 'pt 'n)
           (BIJECTION (ORD-SEGMENT (succ n)) (UNION sg (PAIR pt pt))))))))))))))

(sp (make-wff fsi-append-stmt))
(let* ((landed (dk-peel!))
       (bij  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                       (pair? (caddr f)) (eq? (car (caddr f)) 'BIJECTION)))
                      "enm in BIJECTION"))
       (enm  (cadr bij))
       (osn  (cadr (caddr bij)))                        ; (ORD-SEGMENT n)
       (nv   (cadr osn))
       (sg   (caddr (caddr bij)))
       (pt   (cadr (cadr (dk-pick (dk-head? 'NOT) "pt not in sg"))))
       (uu   `(UNION ,sg (PAIR ,pt ,pt)))
       (osn1 `(ORD-SEGMENT (succ ,nv))))
  ;; unpack enm's bijection: FUN typing, injectivity, surjectivity
  (fsi-mac-h! 'bijection-membership-iff bij)
  (let* ((conjs (dk-split! (dk-pick (dk-head? 'AND) "unfolded bijection")))
         (ante-class (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                      (caddr (cadr (caddr f))))))
         (inj  (or (find-first (lambda (f) (equal? (ante-class f) osn)) conjs)
                   (error "fsi: injectivity conjunct not found")))
         (surj (or (find-first (lambda (f) (equal? (ante-class f) sg)) conjs)
                   (error "fsi: surjectivity conjunct not found"))))
    ;; unfold the goal and split it into its three parts
    (mac 'bijection-membership-iff)
    (let* ((l1 (dk-opened (lambda () (di))))
           (fun-leaf (fsi-leaf l1 (dk-head? 'IN) "FUN leaf"))
           (rest     (fsi-leaf l1 (dk-head? 'AND) "inj/surj leaf")))
      (dk-focus! rest)
      (let* ((l2 (dk-opened (lambda () (di))))
             (inj-leaf  (fsi-leaf l2 (lambda (g) (equal? (caddr (cadr (caddr g))) osn1)) "inj leaf"))
             (surj-leaf (fsi-leaf l2 (lambda (g) (equal? (caddr (cadr (caddr g))) uu)) "surj leaf")))

        ;; ---- FUN: psi in FUN(OS(succ n), sg u {pt}) ----
        (dk-focus! fun-leaf)
        (let* ((l3 (dk-opened (lambda () (lam-t))))
               (set-leaf (fsi-leaf l3 (lambda (g) (eq? (caddr g) 'SET)) "domain sethood"))
               (typ-leaf (fsi-leaf l3 (lambda (g) (not (eq? (caddr g) 'SET))) "pointwise typing")))
          (dk-focus! set-leaf)
          (dk-fact! 'nn-succ-closed nv)
          (dk-fact! 'nn-subset-ord `(succ ,nv))
          (dk-fact! 'ord-segment-is-set `(succ ,nv))
          (ass)
          (fsi-grounded! set-leaf 'domain-sethood)
          (dk-focus! typ-leaf)
          (let* ((iv (dk-di-var!)))                     ; lands (IN i OS(succ n))
            (fsi-mac-h! 'ord-segment-nn-succ `(IN ,iv ,osn1))
            (use-cases `(OR (IN ,iv ,osn) (= ,iv ,nv))
              (lambda ()                                ; i in OS(n): the value is enm(i) in sg
                (fsi-reduce-if! 'true (lambda (c) (equal? c `(IN ,iv ,osn))))
                (mac 'union-membership) (oi-l)
                (have! `(AND (IN ,enm (FUN ,osn ,sg)) (IN ,iv ,osn)))
                (dk-fact! 'fun-apply-type enm osn sg iv)
                (ass))
              (lambda ()                                ; i = n: the value is pt
                (fsi-reduce-if! 'false (lambda (c) (equal? c `(IN ,iv ,osn)))
                  (lambda () (subst `(= ,iv ,nv)) (dk-fact! 'ord-segment-self nv) (ass)))
                (mac 'union-membership) (oi-r)
                (have! `(AND (IN ,pt SET) (IN ,pt SET)))
                (mac 'pairing-membership) (oi-l) (rfl)))))
        (fsi-grounded! fun-leaf 'FUN-part)

        ;; ---- INJ ----
        (dk-focus! inj-leaf)
        (let* ((landed (dk-peel!))                      ; (IN a OS1) (IN b OS1) (= (psi a) (psi b))
               (eqn (dk-pick (dk-head? '=) "psi a = psi b"))
               (av  (cadr (cadr eqn)))
               (bv  (cadr (caddr eqn)))
               (eqn2 (dk-landed-1 (lambda () (lam-b-h eqn))))   ; (= IFa IFb)
               (ifa (cadr eqn2))
               (ifb (caddr eqn2))
               (via-enm! (lambda (v)                    ; (IN (enm v) sg) for v in OS(n)
                           (have! `(AND (IN ,enm (FUN ,osn ,sg)) (IN ,v ,osn)))
                           (dk-fact! 'fun-apply-type enm osn sg v)))
               (n-side (lambda (v)                      ; closes (NOT (IN v OS(n))) when v = n
                         (lambda () (subst `(= ,v ,nv)) (dk-fact! 'ord-segment-self nv) (ass)))))
          (fsi-mac-h! 'ord-segment-nn-succ `(IN ,av ,osn1))
          (fsi-mac-h! 'ord-segment-nn-succ `(IN ,bv ,osn1))
          (use-cases `(OR (IN ,av ,osn) (= ,av ,nv))
            (lambda ()
              (use-cases `(OR (IN ,bv ,osn) (= ,bv ,nv))
                (lambda ()                              ; a, b in OS(n): enm a = enm b, enm injective
                  (fsi-if-land! 'true ifa)
                  (fsi-if-land! 'true ifb)
                  (have! `(= (,enm ,av) (,enm ,bv))
                         (lambda () (subst `(= (,enm ,av) ,ifa)) (subst `(= (,enm ,bv) ,ifb)) (ass)))
                  (dk-apply! inj av bv)
                  (ass))
                (lambda ()                              ; a in OS(n), b = n: enm a = pt in sg, absurd
                  (fsi-if-land! 'true ifa)
                  (fsi-if-land! 'false ifb (n-side bv))
                  (via-enm! av)
                  (have! `(IN ,pt ,sg)
                         (lambda () (subst `(= ,pt ,ifb)) (subst `(= ,ifb ,ifa))
                                    (subst `(= ,ifa (,enm ,av))) (ass)))
                  (ai `(NOT (IN ,pt ,sg))))))
            (lambda ()
              (use-cases `(OR (IN ,bv ,osn) (= ,bv ,nv))
                (lambda ()                              ; a = n, b in OS(n): mirror image
                  (fsi-if-land! 'false ifa (n-side av))
                  (fsi-if-land! 'true ifb)
                  (via-enm! bv)
                  (have! `(IN ,pt ,sg)
                         (lambda () (subst `(= ,pt ,ifa)) (subst `(= ,ifa ,ifb))
                                    (subst `(= ,ifb (,enm ,bv))) (ass)))
                  (ai `(NOT (IN ,pt ,sg))))
                (lambda ()                              ; a = n = b
                  (subst `(= ,av ,nv)) (subst `(= ,bv ,nv)) (rfl))))))
        (fsi-grounded! inj-leaf 'INJ-part)

        ;; ---- SURJ ----
        (dk-focus! surj-leaf)
        (let* ((landed (dk-peel!))                      ; (IN w sg u {pt})
               (wv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) uu)))
                                  "w in the union"))))
          (fsi-mac-h! 'union-membership `(IN ,wv ,uu))
          (use-cases `(OR (IN ,wv ,sg) (IN ,wv (PAIR ,pt ,pt)))
            (lambda ()                                  ; w in sg: its enm-preimage z
              (let* ((ex (dk-apply! surj wv))           ; (FORSOME z (AND (IN z OS(n)) (= (enm z) w)))
                     (zv (dk-skolem! ex)))
                (have! `(IN ,zv ,osn1) (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
                (ew zv)
                (dk-conj-close!
                  (lambda ()
                    (if (eq? (car (fsi-goal)) 'IN)
                        (ass)
                        (begin
                          (lam-b)
                          (fsi-reduce-if! 'true (lambda (c) (equal? c `(IN ,zv ,osn))))
                          (ass)))))))
            (lambda ()                                  ; w = pt: preimage n
              (have! `(AND (IN ,pt SET) (IN ,pt SET)))
              (fsi-mac-h! 'pairing-membership `(IN ,wv (PAIR ,pt ,pt)))
              (have! `(= ,wv ,pt) (lambda () (prop)))
              (have! `(IN ,nv ,osn1) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
              (ew nv)
              (dk-conj-close!
                (lambda ()
                  (if (eq? (car (fsi-goal)) 'IN)
                      (ass)
                      (begin
                        (lam-b)
                        (fsi-reduce-if! 'false (lambda (c) (equal? c `(IN ,nv ,osn)))
                          (lambda () (dk-fact! 'ord-segment-self nv) (ass)))
                        (subst `(= ,wv ,pt))
                        (rfl))))))))
        (fsi-grounded! surj-leaf 'SURJ-part)))))
(fsi-check-done! 'enum-append-is-bijection)
(qed 'enum-append-is-bijection)
