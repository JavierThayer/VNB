;;; rake-finsum-typing-nn.scm -- two NN typing leaves of the rake, PROVEN.
;;;
;;;     falling-in-nn-ind   (NEW)  the induction form of falling-in-nn
;;;     falling-in-nn              formerly a `well-known' support
;;;                                (structure-library/injection.scm:318)
;;;     nn-minus-in-nn             formerly a `hand-wave' support
;;;                                (theorem-library/finsum-additive.scm:72)
;;;
;;; Both statements are copied LITERALLY from their support sites.
;;;
;;; WHY A SEPARATE FILE from rake-finsum-typing.scm.  Both proofs need
;;; `nn-le-gap' -- "m <= k produces a d in NN with k = m + d" -- which is proven
;;; in theorem-library/series-block-abs (load position 379).  The other leaves of
;;; that batch have upper bounds at 346 (border-mult-proof) and 362
;;; (spans-transport-proof), so the two windows are disjoint and the batch cannot
;;; be one file.
;;;
;;; nn-minus-in-nn.  NN-MINUS is DEFINED (nn-minus-def, a def-constant) as
;;; (IF (<= l k) (- k l) 0), so the proof is the IF case split its warrant
;;; described and never ran: in the then-branch l <= k, so nn-le-gap produces the
;;; d with k = l + d and (- k l) = d by ring arithmetic; in the else-branch the
;;; value is the literal 0.
;;;
;;; falling-in-nn.  FALLING is a def-by-nn-recursion (injection.scm):
;;;   FALLING(n,0) = 1,   FALLING(n, succ k) = (n - k) * FALLING(n, k).
;;; The bare typing does not induct: at the step the factor (n - k) is a natural
;;; only while k < n, and past that point the product is 0 because the factor at
;;; k = n was 0.  So the induction carries the SECOND clause that makes it go
;;; through, and it is stated WITHOUT the order relation -- "n - m is a natural,
;;; or the falling factorial has already vanished":
;;;
;;;     m in NN => forall n in NN.  FALLING(n,m) in NN
;;;                 and ( (n - m) in NN  or  FALLING(n,m) = 0 )
;;;
;;; The step is then three ring identities and one citation of
;;; `nn-nonzero-is-succ': if (n - k) is a nonzero natural it is succ(j), and
;;; n - succ(k) = j; if it IS zero the product vanishes; and if FALLING(n,k) was
;;; already zero so is the product.  No <= reasoning anywhere, which is why
;;; nn-le-gap is not needed here -- only nn-minus-in-nn forces the position.
;;;
;;; BILL (probe on the band, worker-01): all three `proven modulo 0'
;;; [oracles: crs, arith, ineq].
;;;
;;; CITATIONS, with the file that installs each (load position):
;;;   theorem-library/finsum-additive (definitional):  nn-minus-def          118
;;;   structure-library/injection (definitional):      falling-zero/-succ     83
;;;   number-systems (primitive):                      nn-zero-in, nn-succ-closed,
;;;                                                    nn-mul-closed
;;;   theorem-library/series-block-abs:                nn-le-gap             379
;;;   theorem-library/nn-parity-proof:                 nn-nonzero-is-succ,
;;;                                                    nn-succ-plus-one      211
;;;   theorem-library/nn-in-rr-proof (or its file):    nn-in-rr
;;;   theorem-library/binary-minus-laws:               rr-sub-in-rr          162
;;;
;;; LOAD WINDOW, by FILE NAME:
;;;   lo -- AFTER theorem-library/series-block-abs (position 379), the latest
;;;         citation (nn-le-gap).
;;;   hi -- none.  Neither leaf has a PROVEN citer: nn-minus-in-nn is named only
;;;         in comments and in the unloaded theorem-library/binomial-probe, and
;;;         falling-in-nn only at its support site and in pss-topics.
;;;   i.e. [380, end).
;;;
;;; Helper prefix: rkf-.

;;; ---------------------------------------------------------------------------
;;; helpers

(define (rkf-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; rkf: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "rkf: proof not complete" name))))

;; Among LEAVES (as dk-opened returns them), the unique one whose GOAL satisfies PRED.
(define (rkf-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "rkf-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "rkf-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

;; Split the AND GOAL in focus; returns (left-leaf . right-leaf).  `di' is what
;; splits a conjunctive goal (CLAUDE.md, "di is greedy"), and the two leaves are
;; told apart by the conjunct each carries, never by position.
(define (rkf-and!)
  (let* ((g (dk-goal))
         (l (cadr g)) (r (caddr g))
         (ls (dk-opened (lambda () (di)))))
    (cons (rkf-leaf ls (lambda (x) (equal? x l)) "left conjunct")
          (rkf-leaf ls (lambda (x) (equal? x r)) "right conjunct"))))

;;; ---------------------------------------------------------------------------
;;; nn-minus-in-nn -- the statement as theorem-library/finsum-additive.scm
;;; spells it, copied literally.

(define rkf-ift '(IF (<= l k) (- k l) 0))

(sp (make-wff
     '(FORALL k (IMPLIES (IN k NN) (FORALL l (IMPLIES (IN l NN) (IN (NN-MINUS k l) NN)))))))
(dk-peel!)
(dk-fact! 'nn-minus-def 'k 'l)
(subst '(= (NN-MINUS k l) (IF (<= l k) (- k l) 0)))
(use-em '(<= l k)
  (lambda ()                                   ; l <= k: the value is the difference
    (let* ((ls  (dk-opened (lambda () (if-true rkf-ift))))
           (cnd (rkf-leaf ls (lambda (g) (equal? g '(<= l k))) "if-true condition"))
           (mn  (rkf-leaf ls (lambda (g) (not (equal? g '(<= l k)))) "if-true main")))
      (dk-focus! cnd) (ass)
      (dk-focus! mn)
      (subst (list '= rkf-ift '(- k l)))
      (let* ((ex (dk-fact! 'nn-le-gap 'k 'l))   ; forsome d in NN. k = l + d
             (dv (dk-skolem! ex)))
        (subst (list '= 'k (list '+ 'l dv)))
        (fact 'nn-in-rr 'l) (fact 'nn-in-rr dv)
        (have! (list '= (list '- (list '+ 'l dv) 'l) dv) (lambda () (crs)))
        (subst (list '= (list '- (list '+ 'l dv) 'l) dv))
        (ass))))
  (lambda ()                                   ; otherwise the value is the literal 0
    (let* ((ls  (dk-opened (lambda () (if-false rkf-ift))))
           (cnd (rkf-leaf ls (dk-head? 'NOT) "if-false condition"))
           (mn  (rkf-leaf ls (lambda (g) (not ((dk-head? 'NOT) g))) "if-false main")))
      (dk-focus! cnd) (ass)
      (dk-focus! mn)
      (subst (list '= rkf-ift 0))
      (fact 'nn-zero-in)
      (ass))))
(rkf-check! 'nn-minus-in-nn)
(qed 'nn-minus-in-nn)
(topic! 'nn-minus-in-nn 'plumbing)

;;; ---------------------------------------------------------------------------
;;; falling-in-nn-ind -- the induction form, the recursion index OUTERMOST.
;;;
;;;   m in NN => forall n in NN.  FALLING(n,m) in NN
;;;                and ( (- n m) in NN  or  FALLING(n,m) = 0 )
;;;
;;; m OUTERMOST because `ni' tests the goal's SHAPE and `di' is greedy
;;; (CLAUDE.md), so there is no peeling down to an inner universal and inducting
;;; there.  falling-in-nn is then one citation of this.

(define rkf-fall-ind-stmt
  '(FORALL m (IMPLIES (IN m NN)
     (FORALL n (IMPLIES (IN n NN)
       (AND (IN (FALLING n m) NN)
            (OR (IN (- n m) NN) (= (FALLING n m) 0))))))))

(sp (make-wff rkf-fall-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkf-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkf-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base: FALLING(n,0) = 1, and n - 0 = n ------------------------------
  (dk-focus! base)
  (dk-peel!)
  (mac 'falling-zero)
  (fact 'nn-zero-in)
  (fact 'nn-succ-closed 0)
  (fact 'nn-in-rr 'n)
  (let ((p (rkf-and!)))
    (dk-focus! (car p)) (ass)
    (dk-focus! (cdr p))
    (oi-l)
    (have! '(= (- n 0) n) (lambda () (crs)))
    (subst '(= (- n 0) n))
    (ass))
  ;; ---- step ---------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)
  (let* ((ih (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL))) "the IH"))
         (kv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                             (eq? (caddr f) 'NN)
                                             (not (eq? (cadr f) 'n))))
                            "the induction variable's typing"))))
    (mac 'falling-succ)                      ; guarded on (IN k NN), which is in context
    (let* ((nk   (list '- 'n kv))            ; the new factor
           (fnk  (list 'FALLING 'n kv))      ; the previous value
           (ihi  (dk-apply! ih 'n)))
      (dk-split! ihi)
      (fact 'nn-in-rr 'n) (fact 'nn-in-rr kv) (fact 'rr-one-in)
      (fact 'rr-sub-in-rr 'n kv)
      (fact 'nn-in-rr fnk)
      (use-cases (list 'OR (list 'IN nk 'NN) (list '= fnk 0))
        ;; ---- the factor is a natural ---------------------------------------
        (lambda ()
          (let ((p (rkf-and!)))
            (dk-focus! (car p))              ; the product is a natural
            (have! (list 'AND (list 'IN nk 'NN) (list 'IN fnk 'NN)))
            (fact 'nn-mul-closed nk fnk)
            (ass)
            (dk-focus! (cdr p))              ; and the second clause survives
            (use-em (list '= nk 0)
              (lambda ()                     ; a zero factor kills the product
                (oi-r)
                (subst (list '= nk 0))
                (crs))
              (lambda ()                     ; a nonzero natural factor is succ(j)
                (oi-l)
                (let* ((ex (dk-fact! 'nn-nonzero-is-succ nk))
                       (jv (dk-skolem! ex)))
                  (fact 'nn-in-rr jv)
                  (fact 'nn-succ-plus-one kv)
                  (subst (list '= (list 'succ kv) (list '+ kv 1)))
                  (have! (list '= (list '- 'n (list '+ kv 1)) (list '- nk 1))
                         (lambda () (crs)))
                  (subst (list '= (list '- 'n (list '+ kv 1)) (list '- nk 1)))
                  (subst (list '= nk (list 'succ jv)))
                  (fact 'nn-succ-plus-one jv)
                  (subst (list '= (list 'succ jv) (list '+ jv 1)))
                  (have! (list '= (list '- (list '+ jv 1) 1) jv) (lambda () (crs)))
                  (subst (list '= (list '- (list '+ jv 1) 1) jv))
                  (ass))))))
        ;; ---- the falling factorial had already vanished ---------------------
        (lambda ()
          (subst (list '= fnk 0))
          (have! (list '= (list '* nk 0) 0) (lambda () (crs)))
          (subst (list '= (list '* nk 0) 0))
          (fact 'nn-zero-in)
          (let ((p (rkf-and!)))
            (dk-focus! (car p)) (ass)
            (dk-focus! (cdr p)) (oi-r) (rfl)))))))
(rkf-check! 'falling-in-nn-ind)
(qed 'falling-in-nn-ind)
(topic! 'falling-in-nn-ind 'combinatorial)

;;; ---------------------------------------------------------------------------
;;; falling-in-nn -- the statement as structure-library/injection.scm spells it,
;;; copied literally.  One citation of the induction form, then the conjunct.

(sp (make-wff
     '(FORALL n (IMPLIES (IN n NN) (FORALL m (IMPLIES (IN m NN) (IN (FALLING n m) NN)))))))
(dk-peel!)
(dk-split! (dk-fact! 'falling-in-nn-ind 'm 'n))
(ass)
(rkf-check! 'falling-in-nn)
(qed 'falling-in-nn)
(topic! 'falling-in-nn 'combinatorial)
