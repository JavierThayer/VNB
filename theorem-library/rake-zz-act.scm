;;; rake-zz-act.scm -- BATCH 6 of the rake: ZZ-ACT made a DEFINITION, and the
;;; five billed ZZ-ACT laws proven from it, each `modulo 0'.
;;;
;;; WHAT WAS WRONG.  structure-library/zz-action.scm called
;;; `theory-add-definition!' DIRECTLY (line 31), outside `def-constant'.  Only
;;; `def-constant' binds *current-provenance* to `definitional'; a bare
;;; `theory-add-definition!' does not, so ZZ-ACT's two defining equations were
;;; installed with provenance `asserted' and NO warrant:
;;;
;;;     zz-act-nonneg   prov=asserted  debt={zz-act-nonneg}   trust: none
;;;     zz-act-neg      prov=asserted  debt={zz-act-neg}      trust: none
;;;
;;; Every route to the constant goes through one of the two, so proving any
;;; ZZ-ACT law FROM THEM would have replaced an `informal' bill by a
;;; `trust: none' one -- debt relabelling, not a rake.
;;;
;;; THE REPAIR.  ZZ-ACT is now an explicit `def-functoid' (see the PROBE-ONLY
;;; block below, which is the text the integrator moves into zz-action.scm),
;;; and the two equations are THEOREMS of it, stated here UNCHANGED, character
;;; for character, from their `theory-add-definition!' site.  Nothing that cites
;;; either name has to change.
;;;
;;; THE k = 0 OVERLAP.  zz-action.scm's header says the negative clause is
;;; "k in NN, k>0", but the INSTALLED zz-act-neg is guarded by `k in NN' alone,
;;; so the two clauses overlap at k = 0, where consistency needs
;;; INV(g)(IDEN(g)) = IDEN(g) -- a fact the tree did not have.  It is proven
;;; here as `abelian-group-inv-iden' (four citations), so zz-act-neg goes
;;; through UNGUARDED and no citer of it needs repair.
;;;
;;; ALSO PROVEN HERE, because the ZZ-ACT laws need them and they were asserted
;;; or absent:
;;;   mpow-one  / mpow-add        structure-library/monoid-power.scm:34, :49
;;;       (asserted, `informal'); mpow-add by NN induction on the LEFT exponent
;;;       -- mpow-succ peels the factor on the left, so that induction needs
;;;       only associativity, while inducting on the right exponent would need
;;;       x to commute with its own powers.
;;;   abelian-group-right-inv     a * INV(a) = e   (group.scm has LEFT only)
;;;   abelian-group-inv-iden      INV(e) = e
;;;   abelian-group-inv-inv       INV(INV a) = a
;;;   abelian-group-inv-opr       INV(a*b) = INV(a)*INV(b)
;;;   ag-as-monoid-carr/-iden/-opr  the three slot read-offs of the view
;;;   ag-mpow-diff-nonneg/-neg    the two "x^m * INV(x^n)" bricks, stated with
;;;       the exponent relation (d+n=m resp. p+m=n) as an ANTECEDENT, which is
;;;       what lets `fact' detach it from an equation already in context and
;;;       keeps every rewrite away from a term that contains its own pattern.
;;;
;;; LOAD WINDOW [235, 258) -- BY FILE NAME:
;;;   lo = 235, just after theorem-library/rake-monoid-laws (234: monoid-assoc,
;;;        monoid-left-id, monoid-right-id).  The next-latest citations are
;;;        theorem-library/rake-algebra2 (233: mpow-type, abelian-group-right-id,
;;;        abelian-group-inverse-unique), theorem-library/cancellation (215:
;;;        group-inv-in), theorem-library/finsum-type-proof (206:
;;;        group-carrier-closed-opr), structure-library/subtype-laws (204:
;;;        abelian-group-is-group, abelian-group-opr-comm, group-assoc,
;;;        group-left-id, group-left-inv), theorem-library/nn-order-ord (165:
;;;        nn-one-in), theorem-library/equality-basics (146: eq-sym, eq-trans).
;;;   hi = 258, theorem-library/rake-finsum-core, the ONLY citer of any zz-act
;;;        law (ring-scalar-zz-nn and finsum-ring-scalar-zz, lines 1364-1474).
;;;        NOTHING in the tree cites mpow-one or mpow-add, nor any view
;;;        companion of either (measured by grep over structure-library/,
;;;        theorem-library/, calculus/ and the root).
;;;   The natural slot is 235, beside the other rake algebra files.
;;;
;;; Helper prefix `rza-'.  All helpers are file-local.

;;; =====================================================================
;;; PROBE-ONLY -- DELETE THIS BLOCK ON INTEGRATION.
;;;
;;; This is the definition that replaces structure-library/zz-action.scm's
;;; `theory-add-definition!' call (lines 31-48).  It is repeated here so the
;;; file can be PROBED against a band built before the surgery; once
;;; zz-action.scm carries it, `def-functoid' has already run at load position
;;; 79 and this block must go (a second call would be a harmless re-register,
;;; but `install-duplicate-audit' discipline says one installer per name).
;;; =====================================================================

;;; (INTEGRATED 2026-09-19: the def-functoid now lives in structure-library/zz-action.scm.)
;;; ===================== end PROBE-ONLY ================================

;;; =====================================================================
;;; File-local helpers.
;;; =====================================================================

(define (rza-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; rza: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   GOAL ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (f)
                                (display ";;      | ")
                                (display (expression->string f)) (newline))
                              (list-head (dk-asms-of l) (min 10 (length (dk-asms-of l))))))
                  (proof-leaves))
        (error "rza: proof not complete" name))))

(define (rza-idx f)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rza-idx: not in context" (expression->string f)))
          ((equal? (car l) f) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (rza-ineq . fs) (apply ineq (map rza-idx fs)))

(define rza-gm '(ABELIAN-GROUP-AS-MONOID g))
(define (rza-mp e) (list 'MPOW rza-gm 'a e))

;;; ---- resolve a top-level IF in the goal.  COND-CLOSER proves the condition;
;;; BODY runs on the main branch, where the if-equation is in context.
(define (rza-if! true? cond-closer body)
  (let* ((goal (dk-goal)) (ifterm (cadr goal)))
    (if (not (and (pair? ifterm) (eq? (car ifterm) 'IF)))
        (error "rza-if!: goal's LHS is not an IF" (expression->string goal)))
    (for-each
     (lambda (s)
       (dk-focus! s)
       (if (equal? (dk-goal) goal)
           (begin (subst (list '= ifterm (if true? (caddr ifterm) (cadddr ifterm))))
                  (body))
           (cond-closer)))
     (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))))

;; cite a two-place NN axiom whose antecedent is ONE conjunction
(define (rza-nn2! name a b)
  (dk-have! (list 'AND (list 'IN a 'NN) (list 'IN b 'NN)) (lambda () (prop)))
  (fact name a b))

;; among LEAVES, the unique one whose goal does / does not mention `succ'
(define (rza-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "rza-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "rza-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

;;; every integer is a natural or the negative of one; POS/NEG are run on the
;;; two branches and are handed the eigenvariable dk-skolem! minted.
(define (rza-zz-cases! kv pos neg)
  (let* ((ex (dk-fact! 'zz-generated-by-nn kv))
         (n  (dk-skolem! ex)))
    (fact 'nn-in-rr n)
    (use-cases (list (list '= kv n) (list '= kv (list '- n)))
      (lambda () (pos n))
      (lambda () (neg n)))
    n))

;;; a is in CARR(g) iff it is in CARR of the monoid view; land the view form.
;;; ... and a claim that IS the focus goal must be CLOSED, not cut: `have!' of
;;; the goal is a silent self-loop (CLAUDE.md, "Writing proof drivers").
(define (rza-transport! claim closer)
  (cond ((dk-asm? claim) #t)
        ((alpha-equiv? (dk-goal) claim) (closer) (ass))
        (#t (dk-have! claim (lambda () (closer) (ass))))))
(define (rza-in-view! t)
  (rza-transport! (list 'IN t (list 'CARR rza-gm))
                  (lambda () (subst (list '== (list 'CARR rza-gm) '(CARR g))))))
(define (rza-in-carr! t)
  (rza-transport! (list 'IN t '(CARR g))
                  (lambda () (subst (list '== '(CARR g) (list 'CARR rza-gm))))))

(define (rza-op u v) (list '(OPR g) u v))
(define (rza-inv u) (list '(INV g) u))
(define rza-gm-op (list 'OPR rza-gm))

;;; rewrite (OPR g') to (OPR g) in the goal (subst reaches operator position)
(define (rza-opr->g!)
  (fact 'ag-as-monoid-opr-rev 'g)
  (subst (list '== rza-gm-op '(OPR g))))

;; cite a two-place ZZ axiom whose antecedent is ONE conjunction
(define (rza-zz2! name u v)
  (dk-have! (list 'AND (list 'IN u 'ZZ) (list 'IN v 'ZZ)) (lambda () (prop)))
  (fact name u v))

;; type x^e in CARR(g) (and in the view's carrier)
(define (rza-type-mpow! e)
  (fact 'mpow-type rza-gm 'a e)
  (rza-in-carr! (rza-mp e)))

;;; THE MIXED CASE.  Focus goal must be
;;;    ZZ-ACT(g, mv + (-nv), a)  =  x^mv * INV(x^nv)
;;; with mv, nv in NN in context.  Split the integer mv - nv by
;;; zz-generated-by-nn and feed each branch to one of the two diff bricks.
(define (rza-mixed! mv nv)
  (let ((dterm (list '+ mv (list '- nv))))
    (fact 'nn-in-rr mv)
    (fact 'nn-in-rr nv)
    (fact 'nn-subset-zz mv)
    (fact 'nn-subset-zz nv)
    (fact 'zz-neg-closed nv)
    (rza-zz2! 'zz-add-closed mv (list '- nv))
    (rza-type-mpow! mv)
    (rza-type-mpow! nv)
    (fact 'group-inv-in 'g (rza-mp nv))
    (rza-zz-cases! dterm
      ;; ---- mv - nv = p in NN:  p + nv = mv.
      (lambda (p)
        (subst (list '= dterm p))
        (fact 'zz-act-nonneg 'g p 'a)
        (subst (list '= (list 'ZZ-ACT 'g p 'a) (rza-mp p)))
        (dk-have! (list '= (list '+ p nv) mv)
          (lambda () (rza-ineq (list '= dterm p)
                               (list 'IN mv 'RR) (list 'IN nv 'RR) (list 'IN p 'RR))))
        (fact 'ag-mpow-diff-nonneg 'g p nv mv 'a)
        (fact 'eq-sym (rza-op (rza-mp mv) (rza-inv (rza-mp nv))) (rza-mp p))
        (ass))
      ;; ---- mv - nv = -p:  p + mv = nv.
      (lambda (p)
        (subst (list '= dterm (list '- p)))
        (fact 'zz-act-neg 'g p 'a)
        (subst (list '= (list 'ZZ-ACT 'g (list '- p) 'a) (rza-inv (rza-mp p))))
        (dk-have! (list '= (list '+ p mv) nv)
          (lambda () (rza-ineq (list '= dterm (list '- p))
                               (list 'IN mv 'RR) (list 'IN nv 'RR) (list 'IN p 'RR))))
        (fact 'ag-mpow-diff-neg 'g p mv nv 'a)
        (fact 'eq-sym (rza-op (rza-mp mv) (rza-inv (rza-mp nv))) (rza-inv (rza-mp p)))
        (ass)))))

;;; ---- view read-offs -------------------------------------------------
(sp (make-wff '(FORALL g (IMPLIES (IS-ABELIAN-GROUP g)
   (== (CARR g) (CARR (ABELIAN-GROUP-AS-MONOID g)))))))
(dk-peel!) (slot 'CARR) (mac 'ABELIAN-GROUP-AS-MONOID) (nth-r) (slot 'CARR) (qrfl)
(rza-check! 'ag-as-monoid-carr)
(qed 'ag-as-monoid-carr)
(topic! 'ag-as-monoid-carr 'algebra)

(sp (make-wff '(FORALL g (IMPLIES (IS-ABELIAN-GROUP g)
   (== (IDEN g) (IDEN (ABELIAN-GROUP-AS-MONOID g)))))))
(dk-peel!) (slot 'IDEN) (mac 'ABELIAN-GROUP-AS-MONOID) (nth-r) (slot 'IDEN) (qrfl)
(rza-check! 'ag-as-monoid-iden)
(qed 'ag-as-monoid-iden)
(topic! 'ag-as-monoid-iden 'algebra)

(sp (make-wff '(FORALL g (IMPLIES (IS-ABELIAN-GROUP g)
   (== (OPR g) (OPR (ABELIAN-GROUP-AS-MONOID g)))))))
(dk-peel!) (slot 'OPR) (mac 'ABELIAN-GROUP-AS-MONOID) (nth-r) (slot 'OPR) (qrfl)
(rza-check! 'ag-as-monoid-opr)
(qed 'ag-as-monoid-opr)
(topic! 'ag-as-monoid-opr 'algebra)

;;; =====================================================================
;;; abelian-group-right-inv -- a * INV(a) = e.  group.scm states only the LEFT
;;; inverse law; commutativity turns it round.
;;; =====================================================================
(sp (make-wff
 '(FORALL s
    (IMPLIES (IS-ABELIAN-GROUP s)
      (FORALL a (IMPLIES (IN a (CARR s))
        (= ((OPR s) a ((INV s) a)) (IDEN s))))))))
(dk-peel!)
(fact 'abelian-group-is-group 's)
(fact 'group-inv-in 's 'a)
(fact 'abelian-group-opr-comm 's 'a '((INV s) a))
(subst '(= ((OPR s) a ((INV s) a)) ((OPR s) ((INV s) a) a)))
(fact 'group-left-inv 's 'a)
(ass)
(rza-check! 'abelian-group-right-inv)
(qed 'abelian-group-right-inv)
(topic! 'abelian-group-right-inv 'algebra)

;;; ---- abelian-group-inv-iden -----------------------------------------
(sp (make-wff '(FORALL g (IMPLIES (IS-ABELIAN-GROUP g)
   (= ((INV g) (IDEN g)) (IDEN g))))))
(dk-peel!)
(fact 'abelian-group-is-group 'g)
(fact 'group-identity-in 'g)
(fact 'group-inv-in 'g '(IDEN g))
(fact 'group-left-inv 'g '(IDEN g))
(fact 'abelian-group-right-id 'g '((INV g) (IDEN g)))
(fact 'eq-sym '((OPR g) ((INV g) (IDEN g)) (IDEN g)) '((INV g) (IDEN g)))
(fact 'eq-trans '((INV g) (IDEN g))
                '((OPR g) ((INV g) (IDEN g)) (IDEN g))
                '(IDEN g))
(ass)
(rza-check! 'abelian-group-inv-iden)
(qed 'abelian-group-inv-iden)
(topic! 'abelian-group-inv-iden 'algebra)

;;; =====================================================================
;;; abelian-group-inv-inv -- INV(INV a) = a.  `abelian-group-inverse-unique'
;;; (a*b = e forces b = INV a) at (INV a, a), whose hypothesis IS group-left-inv.
;;; =====================================================================
(sp (make-wff
 '(FORALL s
    (IMPLIES (IS-ABELIAN-GROUP s)
      (FORALL a (IMPLIES (IN a (CARR s))
        (= ((INV s) ((INV s) a)) a)))))))
(dk-peel!)
(fact 'abelian-group-is-group 's)
(fact 'group-inv-in 's 'a)
(fact 'group-left-inv 's 'a)
(fact 'abelian-group-inverse-unique 's '((INV s) a) 'a)
(fact 'eq-sym 'a '((INV s) ((INV s) a)))
(ass)
(rza-check! 'abelian-group-inv-inv)
(qed 'abelian-group-inv-inv)
(topic! 'abelian-group-inv-inv 'algebra)

;;; =====================================================================
;;; abelian-group-inv-opr -- INV(a*b) = INV(a)*INV(b).
;;;   (a*b)*(b'*a') = a*(b*(b'*a')) = a*((b*b')*a') = a*(e*a') = a*a' = e,
;;; so INV(a*b) = b'*a' by abelian-group-inverse-unique, and comm reorders it.
;;; =====================================================================
(sp (make-wff
 '(FORALL s
    (IMPLIES (IS-ABELIAN-GROUP s)
      (FORALL a (IMPLIES (IN a (CARR s))
        (FORALL b (IMPLIES (IN b (CARR s))
          (= ((INV s) ((OPR s) a b))
             ((OPR s) ((INV s) a) ((INV s) b)))))))))))
(dk-peel!)
(fact 'abelian-group-is-group 's)
(fact 'group-inv-in 's 'a)
(fact 'group-inv-in 's 'b)
(fact 'group-carrier-closed-opr 's 'a 'b)
(fact 'group-carrier-closed-opr 's '((INV s) b) '((INV s) a))
(fact 'group-carrier-closed-opr 's 'b '((INV s) b))
;; (a*b)*(b'*a') = e
(dk-have! '(= ((OPR s) ((OPR s) a b) ((OPR s) ((INV s) b) ((INV s) a))) (IDEN s))
  (lambda ()
    (fact 'group-assoc 's 'a 'b '((OPR s) ((INV s) b) ((INV s) a)))
    (subst '(= ((OPR s) ((OPR s) a b) ((OPR s) ((INV s) b) ((INV s) a)))
               ((OPR s) a ((OPR s) b ((OPR s) ((INV s) b) ((INV s) a))))))
    (fact 'group-assoc 's 'b '((INV s) b) '((INV s) a))
    (fact 'eq-sym '((OPR s) ((OPR s) b ((INV s) b)) ((INV s) a))
                  '((OPR s) b ((OPR s) ((INV s) b) ((INV s) a))))
    (subst '(= ((OPR s) b ((OPR s) ((INV s) b) ((INV s) a)))
               ((OPR s) ((OPR s) b ((INV s) b)) ((INV s) a))))
    (fact 'abelian-group-right-inv 's 'b)
    (subst '(= ((OPR s) b ((INV s) b)) (IDEN s)))
    (fact 'group-left-id 's '((INV s) a))
    (subst '(= ((OPR s) (IDEN s) ((INV s) a)) ((INV s) a)))
    (fact 'abelian-group-right-inv 's 'a)
    (ass)))
(fact 'abelian-group-inverse-unique 's '((OPR s) a b) '((OPR s) ((INV s) b) ((INV s) a)))
;; ... gives  b'*a' = INV(a*b);  commute and flip.
(fact 'abelian-group-opr-comm 's '((INV s) b) '((INV s) a))
(fact 'eq-sym '((OPR s) ((INV s) b) ((INV s) a)) '((INV s) ((OPR s) a b)))
(subst '(= ((INV s) ((OPR s) a b)) ((OPR s) ((INV s) b) ((INV s) a))))
(ass)
(rza-check! 'abelian-group-inv-opr)
(qed 'abelian-group-inv-opr)
(topic! 'abelian-group-inv-opr 'algebra)

;;; =====================================================================
;;; mpow-one -- statement copied from structure-library/monoid-power.scm:34
;;;   x^1 = x * x^0 = x * e = x.
;;; =====================================================================
(sp (make-wff
 '(FORALL m
    (IMPLIES (IS-MONOID m)
      (FORALL x (IMPLIES (IN x (CARR m))
        (= (MPOW m x 1) x)))))))
(dk-peel!)
(dk-have! '(= 1 (succ 0)) (lambda () (arith)))
(subst '(= 1 (succ 0)))
(fact 'nn-zero-in)
(fact 'mpow-succ 'm 'x 0)
(subst '(== (MPOW m x (succ 0)) ((OPR m) x (MPOW m x 0))))
(fact 'mpow-zero 'm 'x)
(subst '(== (MPOW m x 0) (IDEN m)))
(fact 'monoid-right-id 'm 'x)
(ass)
(rza-check! 'mpow-one)
(qed 'mpow-one)
(topic! 'mpow-one 'algebra)

;;; =====================================================================
;;; mpow-add-ind (AUX) -- mpow-add with the LEFT exponent j OUTERMOST, so that
;;; `ni' fires.  The induction is on j, not on k: mpow-succ peels the factor on
;;; the LEFT (x^(succ n) = x * x^n), so inducting on j needs only associativity,
;;; while inducting on k would need x to commute with its own powers.
;;;   base   x^(0+k)      = e * x^k        = x^k
;;;   step   x^(succ j+k) = x^(succ(j+k))  = x * (x^j * x^k) = (x * x^j) * x^k
;;; =====================================================================
(sp (make-wff
 '(FORALL j (IMPLIES (IN j NN)
    (FORALL m (IMPLIES (IS-MONOID m)
      (FORALL x (IMPLIES (IN x (CARR m))
        (FORALL k (IMPLIES (IN k NN)
          (= (MPOW m x (+ j k))
             ((OPR m) (MPOW m x j) (MPOW m x k)))))))))))))
(let* ((rza-leaves (dk-opened (lambda () (ni))))
       (rza-base (rza-leaf rza-leaves (lambda (g) (not (dk-contains? g 'succ))) "base"))
       (rza-step (rza-leaf rza-leaves (lambda (g) (dk-contains? g 'succ)) "step")))
  ;; ---- base j = 0
  (dk-focus! rza-base)
  (dk-peel!)
  (let* ((gl (dk-goal)) (lhs (cadr gl))
         (mv (cadr lhs)) (xv (caddr lhs)) (kv (caddr (cadddr lhs))))
    (fact 'mpow-type mv xv kv)
    (fact 'nn-zero-in)
    (rza-nn2! 'nn-add-comm 0 kv)
    (subst (list '= (list '+ 0 kv) (list '+ kv 0)))
    (fact 'nn-add-zero kv)
    (subst (list '= (list '+ kv 0) kv))
    (fact 'mpow-zero mv xv)
    (subst (list '== (list 'MPOW mv xv 0) (list 'IDEN mv)))
    (fact 'monoid-left-id mv (list 'MPOW mv xv kv))
    (fact 'eq-sym (list (list 'OPR mv) (list 'IDEN mv) (list 'MPOW mv xv kv))
                  (list 'MPOW mv xv kv))
    (ass))
  ;; ---- step j -> succ j
  (dk-focus! rza-step)
  (dk-peel!)
  (let* ((gl (dk-goal)) (lhs (cadr gl))
         (mv (cadr lhs)) (xv (caddr lhs)) (sum (cadddr lhs))
         (jv (cadr (cadr sum))) (kv (caddr sum))
         (pw (lambda (e) (list 'MPOW mv xv e)))
         (op (lambda (u v) (list (list 'OPR mv) u v)))
         (ih (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                       (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                       (equal? (cadr (caddr f)) (list 'IS-MONOID (cadr f)))))
                      "the IH")))
    (fact 'nn-succ-closed jv)
    (rza-nn2! 'nn-add-closed jv kv)
    (fact 'mpow-type mv xv jv)
    (fact 'mpow-type mv xv kv)
    ;; succ j + k = k + succ j = succ (k + j) = succ (j + k)
    (rza-nn2! 'nn-add-comm (list 'succ jv) kv)
    (subst (list '= (list '+ (list 'succ jv) kv) (list '+ kv (list 'succ jv))))
    (fact 'nn-add-succ kv jv)
    (subst (list '= (list '+ kv (list 'succ jv)) (list 'succ (list '+ kv jv))))
    (rza-nn2! 'nn-add-comm kv jv)
    (subst (list '= (list '+ kv jv) (list '+ jv kv)))
    ;; x^(succ(j+k)) = x * x^(j+k)
    (fact 'mpow-succ mv xv (list '+ jv kv))
    (subst (list '== (pw (list 'succ (list '+ jv kv))) (op xv (pw (list '+ jv kv)))))
    ;; IH at (m, x, k)
    (dk-apply! ih mv xv kv)
    (subst (list '= (pw (list '+ jv kv)) (op (pw jv) (pw kv))))
    ;; x^(succ j) = x * x^j
    (fact 'mpow-succ mv xv jv)
    (subst (list '== (pw (list 'succ jv)) (op xv (pw jv))))
    ;; goal:  x * (x^j * x^k) = (x * x^j) * x^k
    (fact 'monoid-assoc mv xv (pw jv) (pw kv))
    (fact 'eq-sym (op (op xv (pw jv)) (pw kv)) (op xv (op (pw jv) (pw kv))))
    (ass)))
(rza-check! 'mpow-add-ind)
(qed 'mpow-add-ind)
(topic! 'mpow-add-ind 'algebra)

;;; =====================================================================
;;; mpow-add -- statement copied from structure-library/monoid-power.scm:49
;;; =====================================================================
(sp (make-wff
 '(FORALL m
    (IMPLIES (IS-MONOID m)
      (FORALL x (IMPLIES (IN x (CARR m))
        (FORALL j (IMPLIES (IN j NN)
          (FORALL k (IMPLIES (IN k NN)
            (= (MPOW m x (+ j k))
               ((OPR m) (MPOW m x j) (MPOW m x k)))))))))))))
(dk-peel!)
(fact 'mpow-add-ind 'j 'm 'x 'k)
(ass)
(rza-check! 'mpow-add)
(qed 'mpow-add)
(topic! 'mpow-add 'algebra)


;;; =====================================================================
;;; mpow-one and mpow-add were AXIOMS when structure-library/monoid-power.scm
;;; ran `(view-as-auto-specialize! 'ABELIAN-GROUP-AS-MONOID)' at line 81;
;;; proving them here moves them PAST that specializer, so their companions
;;; have to be rebuilt.  RESTRICTED to the two names on purpose: the
;;; unrestricted re-run installs every MONOID theorem proved since.
;;; No file in the tree cites either companion today -- this keeps the table
;;; the same shape it had before the retirement, nothing more.
;;; =====================================================================
(view-as-auto-specialize! 'ABELIAN-GROUP-AS-MONOID 'mpow-one)
(view-as-auto-specialize! 'ABELIAN-GROUP-AS-MONOID 'mpow-add)

;;; =====================================================================
;;; ag-mpow-diff-nonneg -- d + n = m  =>  x^m * INV(x^n) = x^d.
;;; =====================================================================
(sp (make-wff
 '(FORALL g
    (IMPLIES (IS-ABELIAN-GROUP g)
      (FORALL d_ (IMPLIES (IN d_ NN)
        (FORALL n_ (IMPLIES (IN n_ NN)
          (FORALL m_ (IMPLIES (IN m_ NN)
            (IMPLIES (= (+ d_ n_) m_)
              (FORALL a (IMPLIES (IN a (CARR g))
                (= ((OPR g) (MPOW (ABELIAN-GROUP-AS-MONOID g) a m_)
                            ((INV g) (MPOW (ABELIAN-GROUP-AS-MONOID g) a n_)))
                   (MPOW (ABELIAN-GROUP-AS-MONOID g) a d_)))))))))))))))
(dk-peel!)
(fact 'abelian-group-is-group 'g)
(fact 'abelian-group-as-monoid-is-monoid 'g)
(fact 'ag-as-monoid-carr 'g)
(rza-in-view! 'a)
(fact 'mpow-type rza-gm 'a 'd_)
(fact 'mpow-type rza-gm 'a 'n_)
(rza-in-carr! (rza-mp 'd_))
(rza-in-carr! (rza-mp 'n_))
(fact 'group-inv-in 'g (rza-mp 'n_))
(fact 'eq-sym '(+ d_ n_) 'm_)
(subst '(= m_ (+ d_ n_)))
(fact 'mpow-add rza-gm 'a 'd_ 'n_)
(subst (list '= (rza-mp '(+ d_ n_)) (list rza-gm-op (rza-mp 'd_) (rza-mp 'n_))))
(rza-opr->g!)
(fact 'group-assoc 'g (rza-mp 'd_) (rza-mp 'n_) (rza-inv (rza-mp 'n_)))
(subst (list '= (rza-op (rza-op (rza-mp 'd_) (rza-mp 'n_)) (rza-inv (rza-mp 'n_)))
                (rza-op (rza-mp 'd_) (rza-op (rza-mp 'n_) (rza-inv (rza-mp 'n_))))))
(fact 'abelian-group-right-inv 'g (rza-mp 'n_))
(subst (list '= (rza-op (rza-mp 'n_) (rza-inv (rza-mp 'n_))) '(IDEN g)))
(fact 'abelian-group-right-id 'g (rza-mp 'd_))
(ass)
(rza-check! 'ag-mpow-diff-nonneg)
(qed 'ag-mpow-diff-nonneg)
(topic! 'ag-mpow-diff-nonneg 'algebra)

;;; =====================================================================
;;; ag-mpow-diff-neg -- p + m = n  =>  x^m * INV(x^n) = INV(x^p).
;;; =====================================================================
(sp (make-wff
 '(FORALL g
    (IMPLIES (IS-ABELIAN-GROUP g)
      (FORALL p_ (IMPLIES (IN p_ NN)
        (FORALL m_ (IMPLIES (IN m_ NN)
          (FORALL n_ (IMPLIES (IN n_ NN)
            (IMPLIES (= (+ p_ m_) n_)
              (FORALL a (IMPLIES (IN a (CARR g))
                (= ((OPR g) (MPOW (ABELIAN-GROUP-AS-MONOID g) a m_)
                            ((INV g) (MPOW (ABELIAN-GROUP-AS-MONOID g) a n_)))
                   ((INV g) (MPOW (ABELIAN-GROUP-AS-MONOID g) a p_))))))))))))))))
(dk-peel!)
(fact 'abelian-group-is-group 'g)
(fact 'abelian-group-as-monoid-is-monoid 'g)
(fact 'ag-as-monoid-carr 'g)
(rza-in-view! 'a)
(fact 'mpow-type rza-gm 'a 'p_)
(fact 'mpow-type rza-gm 'a 'm_)
(rza-in-carr! (rza-mp 'p_))
(rza-in-carr! (rza-mp 'm_))
(fact 'group-inv-in 'g (rza-mp 'p_))
(fact 'group-inv-in 'g (rza-mp 'm_))
(fact 'eq-sym '(+ p_ m_) 'n_)
(subst '(= n_ (+ p_ m_)))
(fact 'mpow-add rza-gm 'a 'p_ 'm_)
(subst (list '= (rza-mp '(+ p_ m_)) (list rza-gm-op (rza-mp 'p_) (rza-mp 'm_))))
(rza-opr->g!)
(fact 'abelian-group-inv-opr 'g (rza-mp 'p_) (rza-mp 'm_))
(subst (list '= (rza-inv (rza-op (rza-mp 'p_) (rza-mp 'm_)))
                (rza-op (rza-inv (rza-mp 'p_)) (rza-inv (rza-mp 'm_)))))
(fact 'abelian-group-opr-comm 'g (rza-inv (rza-mp 'p_)) (rza-inv (rza-mp 'm_)))
(subst (list '= (rza-op (rza-inv (rza-mp 'p_)) (rza-inv (rza-mp 'm_)))
                (rza-op (rza-inv (rza-mp 'm_)) (rza-inv (rza-mp 'p_)))))
(fact 'group-assoc 'g (rza-mp 'm_) (rza-inv (rza-mp 'm_)) (rza-inv (rza-mp 'p_)))
(fact 'eq-sym (rza-op (rza-op (rza-mp 'm_) (rza-inv (rza-mp 'm_))) (rza-inv (rza-mp 'p_)))
              (rza-op (rza-mp 'm_) (rza-op (rza-inv (rza-mp 'm_)) (rza-inv (rza-mp 'p_)))))
(subst (list '= (rza-op (rza-mp 'm_) (rza-op (rza-inv (rza-mp 'm_)) (rza-inv (rza-mp 'p_))))
                (rza-op (rza-op (rza-mp 'm_) (rza-inv (rza-mp 'm_))) (rza-inv (rza-mp 'p_)))))
(fact 'abelian-group-right-inv 'g (rza-mp 'm_))
(subst (list '= (rza-op (rza-mp 'm_) (rza-inv (rza-mp 'm_))) '(IDEN g)))
(fact 'group-left-id 'g (rza-inv (rza-mp 'p_)))
(ass)
(rza-check! 'ag-mpow-diff-neg)
(qed 'ag-mpow-diff-neg)
(topic! 'ag-mpow-diff-neg 'algebra)

;;; =====================================================================
;;; zz-act-nonneg -- statement copied from structure-library/zz-action.scm:34
;;; =====================================================================
(sp (make-wff
 '(FORALL g
    (IMPLIES (IS-ABELIAN-GROUP g)
      (FORALL k (IMPLIES (IN k NN)
        (FORALL a (IMPLIES (IN a (CARR g))
          (= (ZZ-ACT g k a)
             (MPOW (ABELIAN-GROUP-AS-MONOID g) a k))))))))))
(dk-peel!)
(fact 'abelian-group-as-monoid-is-monoid 'g)
(fact 'ag-as-monoid-carr 'g)
(dk-have! (list 'IN 'a (list 'CARR rza-gm))
          (lambda () (subst (list '== (list 'CARR rza-gm) '(CARR g))) (ass)))
(fact 'mpow-type rza-gm 'a 'k)
(mac 'ZZ-ACT)
(rza-if! #t (lambda () (ass)) (lambda () (rfl)))
(rza-check! 'zz-act-nonneg)
(qed 'zz-act-nonneg)
(topic! 'zz-act-nonneg 'algebra)

;;; =====================================================================
;;; zz-act-neg -- statement copied from structure-library/zz-action.scm:42,
;;; UNCHANGED: guarded by `k in NN' only, so k = 0 is a real case.
;;; =====================================================================
(sp (make-wff
 '(FORALL g
    (IMPLIES (IS-ABELIAN-GROUP g)
      (FORALL k (IMPLIES (IN k NN)
        (FORALL a (IMPLIES (IN a (CARR g))
          (= (ZZ-ACT g (- k) a)
             ((INV g) (MPOW (ABELIAN-GROUP-AS-MONOID g) a k)))))))))))
(dk-peel!)
(fact 'abelian-group-as-monoid-is-monoid 'g)
(fact 'abelian-group-is-group 'g)
(fact 'nn-in-rr 'k)
(fact 'nn-zero-le 'k)
(fact 'ag-as-monoid-carr 'g)
(dk-have! (list 'IN 'a (list 'CARR rza-gm))
          (lambda () (subst (list '== (list 'CARR rza-gm) '(CARR g))) (ass)))
(fact 'mpow-type rza-gm 'a 'k)
(dk-have! (list 'IN (rza-mp 'k) '(CARR g))
          (lambda () (subst (list '== '(CARR g) (list 'CARR rza-gm))) (ass)))
(fact 'group-inv-in 'g (rza-mp 'k))
(mac 'ZZ-ACT)
(use-em '(IN (- k) NN)
  ;; ---- (- k) in NN: with k in NN too, k = 0 and both sides are IDEN(g).
  (lambda ()
    (fact 'nn-in-rr '(- k))
    (fact 'nn-zero-le '(- k))
    (dk-have! '(= k 0) (lambda () (rza-ineq '(IN k RR) '(<= 0 k) '(<= 0 (- k)))))
    (rza-if! #t (lambda () (ass))
      (lambda ()
        (subst '(= k 0))
        (dk-have! '(= (- 0) 0) (lambda () (crs)))
        (subst '(= (- 0) 0))
        (fact 'mpow-zero rza-gm 'a)
        (subst (list '== (rza-mp 0) (list 'IDEN rza-gm)))
        (fact 'ag-as-monoid-iden 'g)
        (fact 'ag-as-monoid-iden-rev 'g)
        (subst (list '== (list 'IDEN rza-gm) '(IDEN g)))
        (fact 'abelian-group-inv-iden 'g)
        (fact 'eq-sym '((INV g) (IDEN g)) '(IDEN g))
        (ass))))
  ;; ---- (- k) not in NN: the negative branch, and -(-k) = k.
  (lambda ()
    (rza-if! #f (lambda () (ass))
      (lambda ()
        (dk-have! '(= (- (- k)) k) (lambda () (crs)))
        (subst '(= (- (- k)) k))
        (rfl)))))
(rza-check! 'zz-act-neg)
(qed 'zz-act-neg)
(topic! 'zz-act-neg 'algebra)

;;; =====================================================================
;;; zz-act-zero -- statement copied from structure-library/zz-action.scm:52
;;; =====================================================================
(sp (make-wff
 '(FORALL g
    (IMPLIES (IS-ABELIAN-GROUP g)
      (FORALL a (IMPLIES (IN a (CARR g))
        (= (ZZ-ACT g 0 a) (IDEN g))))))))
(dk-peel!)
(fact 'nn-zero-in)
(fact 'zz-act-nonneg 'g 0 'a)
(subst (list '= '(ZZ-ACT g 0 a) (rza-mp 0)))
(fact 'mpow-zero rza-gm 'a)
(subst (list '== (rza-mp 0) (list 'IDEN rza-gm)))
(fact 'ag-as-monoid-iden 'g)
(fact 'ag-as-monoid-iden-rev 'g)
(subst (list '== (list 'IDEN rza-gm) '(IDEN g)))
(rfl)
(rza-check! 'zz-act-zero)
(qed 'zz-act-zero)
(topic! 'zz-act-zero 'algebra)

;;; =====================================================================
;;; zz-act-one -- statement copied from structure-library/zz-action.scm:61
;;; =====================================================================
(sp (make-wff
 '(FORALL g
    (IMPLIES (IS-ABELIAN-GROUP g)
      (FORALL a (IMPLIES (IN a (CARR g))
        (= (ZZ-ACT g 1 a) a)))))))
(dk-peel!)
(fact 'abelian-group-as-monoid-is-monoid 'g)
(fact 'ag-as-monoid-carr 'g)
(rza-in-view! 'a)
(fact 'nn-one-in)
(fact 'zz-act-nonneg 'g 1 'a)
(subst (list '= '(ZZ-ACT g 1 a) (rza-mp 1)))
(fact 'mpow-one rza-gm 'a)
(ass)
(rza-check! 'zz-act-one)
(qed 'zz-act-one)
(topic! 'zz-act-one 'algebra)

;;; =====================================================================
;;; zz-act-type -- statement copied from structure-library/zz-action.scm:71
;;; =====================================================================
(sp (make-wff
 '(FORALL g
    (IMPLIES (IS-ABELIAN-GROUP g)
      (FORALL k (IMPLIES (IN k ZZ)
        (FORALL a (IMPLIES (IN a (CARR g))
          (IN (ZZ-ACT g k a) (CARR g))))))))))
(dk-peel!)
(fact 'abelian-group-as-monoid-is-monoid 'g)
(fact 'abelian-group-is-group 'g)
(fact 'ag-as-monoid-carr 'g)
(rza-in-view! 'a)
(rza-zz-cases! 'k
  (lambda (n)
    (subst (list '= 'k n))
    (fact 'zz-act-nonneg 'g n 'a)
    (subst (list '= (list 'ZZ-ACT 'g n 'a) (rza-mp n)))
    (fact 'mpow-type rza-gm 'a n)
    (rza-in-carr! (rza-mp n)))
  (lambda (n)
    (subst (list '= 'k (list '- n)))
    (fact 'zz-act-neg 'g n 'a)
    (subst (list '= (list 'ZZ-ACT 'g (list '- n) 'a)
                 (list '(INV g) (rza-mp n))))
    (fact 'mpow-type rza-gm 'a n)
    (rza-in-carr! (rza-mp n))
    (fact 'group-inv-in 'g (rza-mp n))
    (ass)))
(rza-check! 'zz-act-type)
(qed 'zz-act-type)
(topic! 'zz-act-type 'algebra)

;;; =====================================================================
;;; zz-act-neg-sign -- statement copied from structure-library/zz-action.scm:82
;;; =====================================================================
(sp (make-wff
 '(FORALL g
    (IMPLIES (IS-ABELIAN-GROUP g)
      (FORALL k (IMPLIES (IN k ZZ)
        (FORALL a (IMPLIES (IN a (CARR g))
          (= (ZZ-ACT g (- k) a) ((INV g) (ZZ-ACT g k a)))))))))))
(dk-peel!)
(fact 'abelian-group-as-monoid-is-monoid 'g)
(fact 'abelian-group-is-group 'g)
(fact 'ag-as-monoid-carr 'g)
(rza-in-view! 'a)
(rza-zz-cases! 'k
  ;; ---- k = n, n in NN:  both sides are INV(g)(x^n).
  (lambda (n)
    (subst (list '= 'k n))
    (fact 'zz-act-neg 'g n 'a)
    (subst (list '= (list 'ZZ-ACT 'g (list '- n) 'a)
                 (list '(INV g) (rza-mp n))))
    (fact 'zz-act-nonneg 'g n 'a)
    (subst (list '= (list 'ZZ-ACT 'g n 'a) (rza-mp n)))
    (rfl))
  ;; ---- k = -n:  LHS is x^n, RHS is INV(INV(x^n)).
  (lambda (n)
    (subst (list '= 'k (list '- n)))
    (dk-have! (list '= (list '- (list '- n)) n) (lambda () (crs)))
    (subst (list '= (list '- (list '- n)) n))
    (fact 'zz-act-nonneg 'g n 'a)
    (subst (list '= (list 'ZZ-ACT 'g n 'a) (rza-mp n)))
    (fact 'zz-act-neg 'g n 'a)
    (subst (list '= (list 'ZZ-ACT 'g (list '- n) 'a)
                 (list '(INV g) (rza-mp n))))
    (fact 'mpow-type rza-gm 'a n)
    (rza-in-carr! (rza-mp n))
    (fact 'abelian-group-inv-inv 'g (rza-mp n))
    (fact 'eq-sym (list '(INV g) (list '(INV g) (rza-mp n))) (rza-mp n))
    (ass)))
(rza-check! 'zz-act-neg-sign)
(qed 'zz-act-neg-sign)
(topic! 'zz-act-neg-sign 'algebra)

;;; =====================================================================
;;; zz-act-add -- statement copied from structure-library/zz-action.scm:95
;;; =====================================================================
(sp (make-wff
 '(FORALL g
    (IMPLIES (IS-ABELIAN-GROUP g)
      (FORALL j (IMPLIES (IN j ZZ)
        (FORALL k (IMPLIES (IN k ZZ)
          (FORALL a (IMPLIES (IN a (CARR g))
            (= (ZZ-ACT g (+ j k) a)
               ((OPR g) (ZZ-ACT g j a) (ZZ-ACT g k a)))))))))))))
(dk-peel!)
(fact 'abelian-group-is-group 'g)
(fact 'abelian-group-as-monoid-is-monoid 'g)
(fact 'ag-as-monoid-carr 'g)
(rza-in-view! 'a)
(rza-zz-cases! 'j
  ;; =================== j = m >= 0 ===================
  (lambda (m)
    (subst (list '= 'j m))
    (rza-zz-cases! 'k
      ;; ---- (+,+)
      (lambda (n)
        (subst (list '= 'k n))
        (rza-nn2! 'nn-add-closed m n)
        (fact 'zz-act-nonneg 'g (list '+ m n) 'a)
        (subst (list '= (list 'ZZ-ACT 'g (list '+ m n) 'a) (rza-mp (list '+ m n))))
        (fact 'zz-act-nonneg 'g m 'a)
        (subst (list '= (list 'ZZ-ACT 'g m 'a) (rza-mp m)))
        (fact 'zz-act-nonneg 'g n 'a)
        (subst (list '= (list 'ZZ-ACT 'g n 'a) (rza-mp n)))
        (fact 'mpow-add rza-gm 'a m n)
        (subst (list '= (rza-mp (list '+ m n))
                        (list rza-gm-op (rza-mp m) (rza-mp n))))
        (rza-opr->g!)
        (rza-type-mpow! m)
        (rza-type-mpow! n)
        (rfl))
      ;; ---- (+,-)
      (lambda (n)
        (subst (list '= 'k (list '- n)))
        (fact 'zz-act-nonneg 'g m 'a)
        (subst (list '= (list 'ZZ-ACT 'g m 'a) (rza-mp m)))
        (fact 'zz-act-neg 'g n 'a)
        (subst (list '= (list 'ZZ-ACT 'g (list '- n) 'a) (rza-inv (rza-mp n))))
        (rza-mixed! m n))))
  ;; =================== j = -m ===================
  (lambda (m)
    (subst (list '= 'j (list '- m)))
    (rza-zz-cases! 'k
      ;; ---- (-,+):  commute to the (+,-) shape.
      (lambda (n)
        (subst (list '= 'k n))
        (fact 'zz-act-neg 'g m 'a)
        (subst (list '= (list 'ZZ-ACT 'g (list '- m) 'a) (rza-inv (rza-mp m))))
        (fact 'zz-act-nonneg 'g n 'a)
        (subst (list '= (list 'ZZ-ACT 'g n 'a) (rza-mp n)))
        (fact 'nn-in-rr m)
        (fact 'nn-in-rr n)
        (dk-have! (list '= (list '+ (list '- m) n) (list '+ n (list '- m)))
                  (lambda () (crs)))
        (subst (list '= (list '+ (list '- m) n) (list '+ n (list '- m))))
        (rza-type-mpow! m)
        (rza-type-mpow! n)
        (fact 'group-inv-in 'g (rza-mp m))
        (fact 'abelian-group-opr-comm 'g (rza-inv (rza-mp m)) (rza-mp n))
        (subst (list '= (rza-op (rza-inv (rza-mp m)) (rza-mp n))
                        (rza-op (rza-mp n) (rza-inv (rza-mp m)))))
        (rza-mixed! n m))
      ;; ---- (-,-)
      (lambda (n)
        (subst (list '= 'k (list '- n)))
        (fact 'zz-act-neg 'g m 'a)
        (subst (list '= (list 'ZZ-ACT 'g (list '- m) 'a) (rza-inv (rza-mp m))))
        (fact 'zz-act-neg 'g n 'a)
        (subst (list '= (list 'ZZ-ACT 'g (list '- n) 'a) (rza-inv (rza-mp n))))
        (fact 'nn-in-rr m)
        (fact 'nn-in-rr n)
        (dk-have! (list '= (list '+ (list '- m) (list '- n)) (list '- (list '+ m n)))
                  (lambda () (crs)))
        (subst (list '= (list '+ (list '- m) (list '- n)) (list '- (list '+ m n))))
        (rza-nn2! 'nn-add-closed m n)
        (fact 'zz-act-neg 'g (list '+ m n) 'a)
        (subst (list '= (list 'ZZ-ACT 'g (list '- (list '+ m n)) 'a)
                        (rza-inv (rza-mp (list '+ m n)))))
        (fact 'mpow-add rza-gm 'a m n)
        (subst (list '= (rza-mp (list '+ m n))
                        (list rza-gm-op (rza-mp m) (rza-mp n))))
        (rza-opr->g!)
        (rza-type-mpow! m)
        (rza-type-mpow! n)
        (fact 'abelian-group-inv-opr 'g (rza-mp m) (rza-mp n))
        (subst (list '= (rza-inv (rza-op (rza-mp m) (rza-mp n)))
                        (rza-op (rza-inv (rza-mp m)) (rza-inv (rza-mp n)))))
        (rfl)))))
(rza-check! 'zz-act-add)
(qed 'zz-act-add)
(topic! 'zz-act-add 'algebra)

