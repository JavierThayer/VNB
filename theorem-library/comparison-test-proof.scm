;;; comparison-test-proof.scm -- THE COMPARISON TEST for real series, PROVEN,
;;; together with the two order lemmas it rests on and the readouts that make
;;; a real partial sum computable.
;;;
;;;   0 <= f(n) <= g(n) for every n,  Sum g converges   =>   Sum f converges
;;;
;;; `comparison-test' (theorem-library/power-series.scm) carried an `informal'
;;; warrant whose text named its three ingredients and said "the chain is
;;; assembled, not missing".  Two of the three -- `series-partial-sum-monotone-
;;; nonneg' and `series-partial-sum-le-termwise' (theorem-library/series-order-
;;; lemmas.scm) -- were themselves `well-known' supports; the third,
;;; `monotone-convergence-rr', was proven on 2026-08-20.  All four are retired
;;; here, and a fifth fact the warrant did NOT name is proven beside them (L2.5
;;; below): the chain as written was one rung short.
;;;
;;; WHAT THE FILE COSTS.  Every theorem in it bills `modulo 0' except the three
;;; that reach through `nn-monotone-step-implies-le', which bill
;;; `modulo {nn-zero-le, nn-le-succ-cases}' [trust: well-known] -- the two
;;; NN-order supports of structure-library/order-lemmas.scm, inherited from
;;; monotone-convergence-proof.scm and NOTHING ELSE.  Two citations were
;;; declined on that ground and both are worth recording:
;;;
;;;   * `sum-ag-type' (structure-library/sequences.scm) is the obvious source
;;;     for (IN (SERIES-PARTIAL-SUM f k) RR), and it is an unwarranted
;;;     `theory-add-axiom!' -- its own bill is {sum-ag-type}, i.e. trust: none.
;;;     R2 below proves the RR instance by NN induction instead, from
;;;     `sum-ag-zero'/`sum-ag-succ' (both `definitional', so free) and
;;;     `rr-add-closed' (primitive).  Six lines, and the whole file stays clean.
;;;   * `(IS-ABELIAN-GROUP (NORMED-FIELD-ADDITIVE-AG RR-NORMED-FIELD))' is one
;;;     `fact' away (normed-field-additive-ag-is-abelian-group + rr-is-normed-
;;;     field) and costs {rr-is-normed-field} -- also trust: none, that axiom
;;;     carrying no warrant.  It is needed only by `sum-ag-type', so declining
;;;     the first citation removes the second.  Nothing here mentions
;;;     IS-ABELIAN-GROUP: `sum-ag-zero' and `sum-ag-succ' quantify their
;;;     structure argument UNGUARDED, so the recurrence is available at
;;;     RR's additive group without any group hypothesis at all.
;;;
;;; THE STRUCTURE, in the order the file builds it:
;;;
;;;   R0  the two READOUTS.  SERIES-PARTIAL-SUM(f,k) is
;;;       SUM-AG(NORMED-FIELD-ADDITIVE-AG(RR-NORMED-FIELD), f, k), and nothing
;;;       in the tree said what that group's OPR and IDEN are.  Both are one
;;;       functoid unfold, one accessor projection, one `nth-r' and one
;;;       instance macete: OPR is binplus, IDEN is 0.
;;;   R1  the RECURRENCE ON THE SURFACE: SERIES-PARTIAL-SUM(f,0) == 0 and
;;;       SERIES-PARTIAL-SUM(f,succ k) == SERIES-PARTIAL-SUM(f,k) + f(k).
;;;       This is the mechanism the whole file turns on -- after it, every
;;;       partial-sum argument is ordinary real arithmetic and `ineq' closes it.
;;;   R2  a real partial sum is real.
;;;   L1  series-partial-sum-monotone-nonneg   (retires the support)
;;;   L2  series-partial-sum-le-termwise       (retires the support)
;;;   L2.5 monotone-convergent-bounded-above -- THE RUNG THE WARRANT MISSED.
;;;   R3  the partial-sum SEQUENCE k |-> SERIES-PARTIAL-SUM(f,k) as an element
;;;       of FUN(NN,RR), and its beta rule.  One `lam-t' and one `lam-b', done
;;;       once here so that L3 -- and any later series proof -- needs neither.
;;;   L3  comparison-test                      (retires the support)
;;;
;;; L2.5 IS THE ONE PIECE OF REAL MATHEMATICS, and the warrant's chain does not
;;; go through without it.  `monotone-convergence-rr' wants a REAL NUMBER
;;; bounding the partial sums; the warrant offers "F_k <= G_k <= lim G", which
;;; needs "a nondecreasing sequence converging to L satisfies x_k <= L for every
;;; k".  That is a genuine lemma and it is not in the tree.  It is also not
;;; needed: monotone convergence needs SOME bound, not the sharp one, and the
;;; unsharp bound is much cheaper.  Take eps = 1 in the definition of
;;; CONVERGES-TO; it hands back a threshold N with |x_n - L| <= 1 for n >= N.
;;; Then for every k, either N <= k -- and x_k <= L + 1 directly -- or k <= N,
;;; and x_k <= x_N <= L + 1 by the monotone lift.  So L + 1 bounds the WHOLE
;;; sequence.  No eps-N limit argument, no trichotomy, no "for all eps" step:
;;; two instantiations, one case split on `rr-le-total', two `ineq' calls.
;;; The sharp lemma remains unproven and unneeded.
;;;
;;; Traps met, in the order they cost time:
;;;
;;;   * `ct4-F' and `ct4-f' ARE THE SAME SCHEME VARIABLE (the reader folds
;;;     case), so naming the lambda after the sequence silently overwrote the
;;;     sequence.  The lambdas are `ct4-fseq' / `ct4-gseq' for that reason.
;;;   * `di' takes a RUN of guarded universals whole: on
;;;     forall([k in nn, f in fun(nn,rr)], ...) one call lands BOTH typings, so
;;;     an induction on k stated after f's typing is unreachable.  R2 therefore
;;;     states k OUTERMOST and `ni' fires with no `di' at all.
;;;   * `rr-abs-bound' is an IFF: `mac-h' lands ONE conjunction, and `ineq'
;;;     reads nothing until it is split.
;;;   * `rr-add-closed' and `rr-leq-antisymmetric' have AND antecedents, which
;;;     `fact' will not split -- each wants a `have!' of the conjunction first.
;;;   * the antecedent of `monotone-convergence-rr' is built by `subst-free'
;;;     into the theorem's own statement rather than retyped: a hand-rebuilt
;;;     formula is what `fact' silently declines to detach.
;;;
;;; Loads after theorem-library/monotone-convergence-proof (monotone-convergence-rr,
;;; nn-monotone-step-implies-le); its other needs are power-series
;;; (SERIES-PARTIAL-SUM, SERIES-CONVERGES), sequences (sum-ag-zero/-succ), views
;;; (NORMED-FIELD-ADDITIVE-AG), numeric-instances (RR-NORMED-FIELD, binplus-apply),
;;; metric-completeness (CONVERGES, CONVERGES-TO), order-predicates (POS-RR),
;;; rr-order-basics (rr-le-total), nn-order-basics (nn-in-rr, nn-le-refl),
;;; rr-abs-basics (rr-abs-bound, rr-abs-closed), binary-minus-laws (rr-sub-in-rr),
;;; rr-ms-dist, fun-apply-type-proof (fun-apply-type-c) and driver-kit.

;;; ---- file-local driver helpers (the `ct-' prefix) --------------------

;;; Select a hypothesis by CONTENT and ERROR on a miss.
(define (ct-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "ct-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; `ineq' wants 1-based assumption indices, and the premises are named ONE BY
;;; ONE: one premise whose atoms cannot be certified in RR poisons the call.
(define (ct-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ct-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (ct-ineq . forms) (apply ineq (map ct-idx forms)))

(define (ct-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME already in the CONTEXT.  `obtain' recognises only an
;;; existential its own lane landed, so it cannot do this one; the
;;; eigenvariable is read off by free-variable set difference, and a miss ERRORS.
(define (ct-skolem! ex)
  (let* ((fv0 (ct-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (ct-fvs (dk-asms)))))
      (if (null? fresh)
          (error "ct-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

;;; di-split an AND goal to its leaves and run CLOSER on each.
(define (ct-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (ct-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `di' until an ASSUMPTION lands.  One `di' takes a guarded universal -- or a
;;; RUN of them -- whole, but on an unguarded (FORALL y (IMPLIES ...)) it peels
;;; the quantifier and lands nothing, so loop on the LANDING, not on a count.
(define (ct-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "ct-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (ct-di-landed-1!)
  (let ((new (ct-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "ct-di-landed-1!: expected 1 landing"
               (map expression->string new)))))

(define ct-ag '(NORMED-FIELD-ADDITIVE-AG RR-NORMED-FIELD))

;;; =====================================================================
;;; R0.  THE READOUTS.  What are the operation and the identity of the
;;; additive abelian group of RR?  NORMED-FIELD-ADDITIVE-AG is a def-functor,
;;; hence a functoid whose body is the LIST of the four source slots, so the
;;; route is: unfold the functoid, project the accessor (`slot'), compute the
;;; list index (`nth-r'), and fire the instance's own slot macete.
;;; =====================================================================

;;; 2026-08-29: the right-hand side was the shared constant `binplus'.  It is now
;;; the tupled VNB-LAMBDA that RR-NORMED-FIELD's ADD slot actually holds -- one
;;; function per instance, rather than one object asserted into five function
;;; classes at once, which proved NN = ZZ = QQ = RR = CC and thence FALSITY.
;;; Same fact, same four steps; only the slot's contents moved.
(define ct-add-lam '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR RR) (+ x_ y_)))

(sp (make-wff (list '== (list 'OPR ct-ag) ct-add-lam)))
(mac 'normed-field-additive-ag) (slot 'OPR) (nth-r) (slot 'ADD) (qrfl)
(qed 'rr-additive-ag-opr)
(topic! 'rr-additive-ag-opr 'analysis)
(alias! 'rr-additive-ag-opr "the operation of RR's additive group")

(sp (make-wff (list '== (list 'IDEN ct-ag) 0)))
(mac 'normed-field-additive-ag) (slot 'IDEN) (nth-r) (slot 'ZERO) (qrfl)
(qed 'rr-additive-ag-iden)
(topic! 'rr-additive-ag-iden 'analysis)
(alias! 'rr-additive-ag-iden "the identity of RR's additive group is 0")

;;; =====================================================================
;;; R1.  THE RECURRENCE, IN THE SURFACE LANGUAGE.  This is the mechanism the
;;; file turns on: SUM-AG's two defining equations, read through R0 and
;;; `binplus-apply', become statements about `+' on the reals, and after them
;;; every partial-sum argument is ordinary arithmetic.
;;;
;;; Both are stated with `==' (quasi-equality) because that is what
;;; `def-by-nn-recursion' installs and because f is UNGUARDED here: off-domain
;;; both sides are undefined, and a strict `=' would assert undefined=undefined.
;;; =====================================================================

(sp (make-wff '(FORALL f (== (SERIES-PARTIAL-SUM f 0) 0))))
(di) (mac 'series-partial-sum) (mac 'sum-ag-zero) (mac 'rr-additive-ag-iden) (qrfl)
(qed 'series-partial-sum-zero)
(topic! 'series-partial-sum-zero 'analysis)
(alias! 'series-partial-sum-zero "the empty partial sum is 0")

;;; =====================================================================
;;; R2 (now FIRST).  A REAL PARTIAL SUM IS REAL.
;;;
;;; `sum-ag-type' says this for any abelian group and is an unwarranted axiom
;;; (bill {sum-ag-type}, trust: none) which would additionally need
;;; IS-ABELIAN-GROUP of the view, itself costing {rr-is-normed-field}.  The
;;; induction is a few lines and costs nothing, so it is the one taken.
;;;
;;; IT RUNS AT THE GROUP LEVEL, AND SINCE 2026-08-29 IT HAS TO.  The step used to
;;; cite `series-partial-sum-succ' -- the surface recurrence -- but that theorem
;;; is now GUARDED on f (the operation slot holds a set function on
;;; CARTESIAN(RR,RR), not the total constant `binplus', so the unguarded
;;; statement is false), and typing its arguments needs exactly this result.
;;; Citing it here would be circular.  sum-ag-succ plus the OPR read-off reach
;;; the same place directly, and the typing comes from the group rather than
;;; from the surface.
;;;
;;; Stated about SUM-AG rather than SERIES-PARTIAL-SUM so that the IH is in the
;;; same language as sum-ag-succ; the SERIES-PARTIAL-SUM form is one unfold away
;;; and is derived immediately below.
;;;
;;; k is stated OUTERMOST: `ni' tests the goal's SHAPE, and one `di' would take
;;; the run  forall([k in nn, f in fun(nn,rr)], ...)  whole, after which the
;;; induction is gone and there is no undo.
;;; =====================================================================

(sp (make-wff (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
   (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN NN RR))
     (list 'IN (list 'SUM-AG ct-ag 'f 'k) 'RR)))))))

(define ct0-br (use-induction))

(dk-focus! (cdr (assq 'base ct0-br)))
(di)
(mac 'sum-ag-zero)
(mac 'rr-additive-ag-iden)
(fact 'rr-zero-in)
(ass)

(dk-focus! (cdr (assq 'step ct0-br)))
(define ct0-n  (cdr (assq 'var ct0-br)))
(define ct0-ih (cdr (assq 'ih  ct0-br)))
(define ct0-f  (cadr (ct-di-landed-1!)))
(inst+ ct0-ih ct0-f)                            ; SUM-AG(ag, f, n) in RR
(fact 'fun-apply-type-c ct0-f 'NN 'RR ct0-n)    ; f(n) in RR
(mac 'sum-ag-succ) (mac 'rr-additive-ag-opr)
(dk-saturate-slot-ops! 'RR '((+ . rr-add-closed)))
(ass)

(qed 'sum-ag-rr-in-rr)
(topic! 'sum-ag-rr-in-rr 'analysis)

;;; ... and the SERIES-PARTIAL-SUM form, one unfold away.
(sp (make-wff '(FORALL k (IMPLIES (IN k NN)
   (FORALL f (IMPLIES (IN f (FUN NN RR)) (IN (SERIES-PARTIAL-SUM f k) RR)))))))
(di) (di)
(mac 'series-partial-sum)
(fact 'sum-ag-rr-in-rr 'k 'f)
(ass)
(qed 'series-partial-sum-in-rr)
(topic! 'series-partial-sum-in-rr 'analysis)
(alias! 'series-partial-sum-in-rr "a real partial sum is real")

;;; The functoid's unfold equation, as a THEOREM.  `def-functoid' installs only a
;;; rewrite macete, so `mac-h' cannot unfold SERIES-PARTIAL-SUM in a HYPOTHESIS
;;; by the functoid's own name -- it warns and no-ops.  The equation is provable
;;; in one line, and the resulting theorem is what mac-h needs (CLAUDE.md).
(sp (make-wff (list 'FORALL 'f (list 'FORALL 'k
      (list '== '(SERIES-PARTIAL-SUM f k) (list 'SUM-AG ct-ag 'f 'k))))))
(di) (di) (mac 'series-partial-sum) (qrfl)
(qed 'series-partial-sum-unfold)
(topic! 'series-partial-sum-unfold 'analysis)

;;; GUARDED SINCE 2026-08-29 -- and guarded on the ARGUMENTS, which is the
;;; weakest hypothesis that works and the only one both consumers can supply.
;;;
;;; It was stated for unguarded f, and that was sound only because the group's
;;; operation slot held `binplus', a TOTAL class function whose apply equation
;;; holds unconditionally.  The slot now holds a set function on
;;; CARTESIAN(RR,RR), so off the reals the left side is an application outside
;;; its domain (undefined) while the right side is not, and `==' quasi-equality
;;; makes the unguarded statement FALSE.  It was true before only because of the
;;; over-strong axioms this repair removed.
;;;
;;; WHY NOT `IN f (FUN NN RR)'.  That was the first guard tried, and it is too
;;; strong: series-linearity.scm proves the POINTWISE forms, where f is assumed
;;; only pointwise real, and could no longer cite this.  Guarding on the two
;;; arguments instead -- which is exactly what the lambda application needs --
;;; serves both: a FUN-typed sequence yields them by fun-apply-type-c, and a
;;; pointwise-real one yields them directly.
(sp (make-wff (list 'FORALL 'f (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
   (list 'IMPLIES '(IN (SERIES-PARTIAL-SUM f k) RR)
     (list 'IMPLIES '(IN (f k) RR)
       '(== (SERIES-PARTIAL-SUM f (succ k))
            (+ (SERIES-PARTIAL-SUM f k) (f k))))))))))
(di) (di) (di) (di)
;; put the partial-sum typing into SUM-AG language, since unfolding the goal
;; does the same to it (CLAUDE.md: normalise BOTH sides).
(mac-h 'series-partial-sum-unfold '(IN (SERIES-PARTIAL-SUM f k) RR))
(mac 'series-partial-sum) (mac 'sum-ag-succ) (mac 'rr-additive-ag-opr)
(dk-saturate-slot-ops! 'RR '((+ . rr-add-closed)))
(qrfl)
(qed 'series-partial-sum-succ)
(topic! 'series-partial-sum-succ 'analysis)
(alias! 'series-partial-sum-succ "the partial-sum recurrence")

;;; =====================================================================
;;; L1.  series-partial-sum-monotone-nonneg.  Statement reproduced VERBATIM
;;; from the support this file retires (series-order-lemmas.scm), so that any
;;; citer sees the formula it always saw.
;;;
;;; NOT an induction -- one step of the recurrence, then `ineq'.
;;; =====================================================================

(define ct1-stmt
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORALL n_ (IMPLIES (IN n_ NN) (<= 0 (f n_))))
       (FORALL k (IMPLIES (IN k NN)
         (<= (SERIES-PARTIAL-SUM f k) (SERIES-PARTIAL-SUM f (succ k)))))))))

(sp (make-wff ct1-stmt))
(define ct1-f      (cadr (ct-di-landed-1!)))
(define ct1-nonneg (ct-di-landed-1!))
(define ct1-k      (cadr (ct-di-landed-1!)))
;; series-partial-sum-succ is guarded on its two ARGUMENTS being real (2026-08-29),
;; so land those typings BEFORE the rewrite rather than after it.
(fact 'series-partial-sum-in-rr ct1-k ct1-f)
(fact 'fun-apply-type-c ct1-f 'NN 'RR ct1-k)
(mac 'series-partial-sum-succ)
(inst+ ct1-nonneg ct1-k)
(ct-ineq (list '<= 0 (list ct1-f ct1-k)))
(qed 'series-partial-sum-monotone-nonneg)
(topic! 'series-partial-sum-monotone-nonneg 'analysis)
(alias! 'series-partial-sum-monotone-nonneg
        "nonnegative terms make the partial sums nondecreasing")

;;; =====================================================================
;;; L2.  series-partial-sum-le-termwise.  Statement VERBATIM from the retired
;;; support.  Induction on k: the base is 0 <= 0 and the step is the recurrence
;;; plus f(k) <= g(k).
;;; =====================================================================

(define ct2-stmt
  '(FORALL f (IMPLIES (IN f (FUN NN RR)) (FORALL g (IMPLIES (IN g (FUN NN RR))
     (IMPLIES (FORALL n_ (IMPLIES (IN n_ NN) (<= (f n_) (g n_))))
       (FORALL k (IMPLIES (IN k NN)
         (<= (SERIES-PARTIAL-SUM f k) (SERIES-PARTIAL-SUM g k))))))))))

(sp (make-wff ct2-stmt))
(define ct2-typs (ct-di-landed!))         ; ONE di lands BOTH function typings
(define ct2-f (cadr (car ct2-typs)))
(define ct2-g (cadr (cadr ct2-typs)))
(define ct2-le (ct-di-landed-1!))
(define ct2-br (use-induction))
(define ct2-k  (cdr (assq 'var ct2-br)))
(define ct2-ih (cdr (assq 'ih  ct2-br)))

(dk-focus! (cdr (assq 'base ct2-br)))
(mac 'series-partial-sum-zero)
(fact 'rr-zero-in)
(fact 'rr-leq-reflexive 0)
(ass)

(dk-focus! (cdr (assq 'step ct2-br)))
;; the recurrence is guarded on its two ARGUMENTS being real (2026-08-29), and it
;; rewrites BOTH sides here, so all four typings must precede it.
(fact 'series-partial-sum-in-rr ct2-k ct2-f)
(fact 'series-partial-sum-in-rr ct2-k ct2-g)
(fact 'fun-apply-type-c ct2-f 'NN 'RR ct2-k)
(fact 'fun-apply-type-c ct2-g 'NN 'RR ct2-k)
(mac 'series-partial-sum-succ)
(inst+ ct2-le ct2-k)
(ct-ineq ct2-ih (list '<= (list ct2-f ct2-k) (list ct2-g ct2-k)))
(qed 'series-partial-sum-le-termwise)
(topic! 'series-partial-sum-le-termwise 'analysis)
(alias! 'series-partial-sum-le-termwise
        "termwise domination passes to the partial sums")

;;; =====================================================================
;;; L2.5  monotone-convergent-bounded-above -- a nondecreasing sequence that
;;; CONVERGES is bounded above.  The converse of monotone-convergence-rr's
;;; hypothesis, and the rung comparison-test's warrant did not name.
;;;
;;; eps := 1 gives a threshold N with |f(n) - L| <= 1 for n >= N; L + 1 then
;;; bounds the whole sequence, the initial segment by the monotone lift.
;;; =====================================================================

(define ct3-stmt
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORALL k (IMPLIES (IN k NN) (<= (f k) (f (succ k)))))
       (IMPLIES (CONVERGES RR-MS f)
         (FORSOME bnd (AND (IN bnd RR)
           (FORALL k (IMPLIES (IN k NN) (<= (f k) bnd))))))))))

(sp (make-wff ct3-stmt))
(define ct3-f    (cadr (ct-di-landed-1!)))
(define ct3-step (ct-di-landed-1!))
(define ct3-conv (ct-di-landed-1!))
(define ct3-ex (dk-landed-1 (lambda () (mac-h 'converges ct3-conv))))
(define ct3-L (ct-skolem! ct3-ex))
(mac-h 'converges-to (list 'CONVERGES-TO 'RR-MS ct3-f ct3-L))
(dk-split! (list 'AND '(IS-METRIC-SPACE RR-MS)
             (list 'AND (list 'IN ct3-f '(FUN NN (PTS RR-MS)))
               (list 'AND (list 'IN ct3-L '(PTS RR-MS))
                 (list 'FORALL 'eps (list 'IMPLIES '(POS-RR eps)
                   (list 'FORSOME 'n (list 'AND '(IN n NN)
                     (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                       (list 'IMPLIES '(<= n n_)
                         (list '<= (list '(DIST RR-MS) (list ct3-f 'n_) ct3-L) 'eps))))))))))))
(slot-h 'PTS (list 'IN ct3-L '(PTS RR-MS)))          ; PTS(RR-MS) = RR

;;; Discriminate the eps universal on POS-RR: the tail universal below has the
;;; same head and mentions DIST too.
(define ct3-epsu
  (ct-find 'eps-universal
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'POS-RR)))))
(have! '(POS-RR 1) (lambda () (mac 'pos-rr) (ct-goal-and! (lambda () (arith)))))
(define ct3-tailex (dk-deepest (lambda () (inst+ ct3-epsu 1))))
(define ct3-N (ct-skolem! ct3-tailex))

(define ct3-tailu
  (ct-find 'tail-universal
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                     (dk-contains? a 'DIST) (not (dk-contains? a 'POS-RR))))))
(define ct3-bnd (list '+ ct3-L 1))

;;; f(m) <= L + 1, for an m in NN with N <= m already in context.  Every
;;; argument is typed BEFORE `rr-ms-dist' fires: that macete is GUARDED, and on
;;; untyped arguments it declines -- silently on a goal, with a spawned
;;; side-condition on a hypothesis.
(define (ct3-tail! m)
  (fact 'fun-apply-type-c ct3-f 'NN 'RR m)
  (inst+ ct3-tailu m)
  (fact 'rr-sub-in-rr (list ct3-f m) ct3-L)
  (fact 'rr-abs-closed (list '- (list ct3-f m) ct3-L))
  (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) (list ct3-f m) ct3-L) 1))
  ;; rr-abs-bound is an IFF: on a hypothesis it lands ONE conjunction
  ;; (-1 <= f(m)-L and f(m)-L <= 1), which `ineq' cannot read until it is split.
  (dk-split! (dk-landed-1
              (lambda ()
                (mac-h 'rr-abs-bound
                       (list '<= (list 'abs (list '- (list ct3-f m) ct3-L)) 1))))))

(fact 'rr-one-in)
(have! (list 'AND (list 'IN ct3-L 'RR) '(IN 1 RR)))
(fact 'rr-add-closed ct3-L 1)
(ew ct3-bnd)

(ct-goal-and!
 (lambda ()
   (if (eq? (car (dk-goal)) 'IN)
       (ass)                                        ; L + 1 in RR
       (let ((k (cadr (ct-di-landed-1!))))
         (fact 'nn-in-rr k)
         (fact 'nn-in-rr ct3-N)
         (have! (list 'AND (list 'IN k 'RR) (list 'IN ct3-N 'RR)))
         (fact 'rr-le-total k ct3-N)
         (use-cases (list (list '<= k ct3-N) (list '<= ct3-N k))
           (lambda ()                               ; k <= N: climb to f(N)
             (fact 'fun-apply-type-c ct3-f 'NN 'RR k)   ; `ineq' must certify f(k)
             (fact 'nn-le-refl ct3-N)
             (ct3-tail! ct3-N)
             (fact 'nn-monotone-step-implies-le ct3-f ct3-N k)
             (ct-ineq (list '<= (list ct3-f k) (list ct3-f ct3-N))
                      (list '<= (list '- (list ct3-f ct3-N) ct3-L) 1)))
           (lambda ()                               ; N <= k: the tail bound
             (ct3-tail! k)
             (ct-ineq (list '<= (list '- (list ct3-f k) ct3-L) 1))))))))

(qed 'monotone-convergent-bounded-above)
(topic! 'monotone-convergent-bounded-above 'analysis)
(alias! 'monotone-convergent-bounded-above
        "a convergent nondecreasing sequence is bounded above")

;;; =====================================================================
;;; R3.  The partial-sum SEQUENCE k |-> SERIES-PARTIAL-SUM(f,k) -- the object
;;; SERIES-CONVERGES is actually about -- as an element of FUN(NN,RR), and its
;;; beta rule.  One `lam-t' and one `lam-b', once, so that L3 (and any later
;;; series proof) works with macetes and never touches the lambda rules.
;;; =====================================================================

(sp (make-wff '(FORALL f (FORALL j (IMPLIES (IN j NN)
   (== ((VNB-LAMBDA k NN (SERIES-PARTIAL-SUM f k)) j) (SERIES-PARTIAL-SUM f j)))))))
(di) (di)
(lam-b)                                   ; the argument is typed FIRST, above
(qrfl)
(qed 'series-partial-sum-seq-apply)
(topic! 'series-partial-sum-seq-apply 'analysis)
(alias! 'series-partial-sum-seq-apply "the partial-sum sequence at an index")

(sp (make-wff '(FORALL f (IMPLIES (IN f (FUN NN RR))
   (IN (VNB-LAMBDA k NN (SERIES-PARTIAL-SUM f k)) (FUN NN RR))))))
(define ctr3-f (cadr (ct-di-landed-1!)))
(dk-lam-t!)                               ; TWO leaves: the typing and (IN NN SET)
(define ctr3-k (cadr (ct-di-landed-1!)))
(fact 'series-partial-sum-in-rr ctr3-k ctr3-f)
(ass)
(qed 'series-partial-sum-seq-in-fun)
(topic! 'series-partial-sum-seq-in-fun 'analysis)
(alias! 'series-partial-sum-seq-in-fun
        "the partial-sum sequence is a real sequence")

;;; ... and its sibling, the POINTWISE ABSOLUTE VALUE of a real sequence.  Same
;;; two leaves, same shape.
;;;
;;; It is here because the tree did not have it and the omission was not
;;; visible: `series-partial-sum-abs-le' -- |sum f| <= sum |f| -- is stated over
;;; SERIES-PARTIAL-SUM(VNB-LAMBDA n_ NN (abs (f n_)), k), so every proof of it
;;; must cite `series-partial-sum-in-rr' at that lambda, and that citation is
;;; guarded on the lambda being in FUN(NN,RR).  Without this lemma the citation
;;; lands the IMPLICATION, silently; the induction hypothesis then has an atom
;;; with no `in rr' certificate, `ineq-atom-rr-ok?' refuses the premise, and the
;;; oracle reports that the goal is not a linear consequence -- which is true,
;;; and says nothing about the missing typing.  Found 2026-08-21 driving that
;;; induction step.  `series-partial-sum-seq-in-fun' above is about the
;;; PARTIAL-SUM sequence and does not cover this one.
(sp (make-wff '(FORALL f (IMPLIES (IN f (FUN NN RR))
   (IN (VNB-LAMBDA n_ NN (abs (f n_))) (FUN NN RR))))))
(define ctr3a-f (cadr (ct-di-landed-1!)))
(dk-lam-t!)                               ; TWO leaves: the typing and (IN NN SET)
(define ctr3a-n (cadr (ct-di-landed-1!)))
(fact 'fun-apply-type-c ctr3a-f 'NN 'RR ctr3a-n)
(fact 'rr-abs-closed (list ctr3a-f ctr3a-n))
(ass)
(qed 'abs-seq-in-fun)
(topic! 'abs-seq-in-fun 'analysis)
(alias! 'abs-seq-in-fun
        "the pointwise absolute value of a real sequence is a real sequence")

;;; =====================================================================
;;; L3.  comparison-test.  Statement VERBATIM from the support this file
;;; retires (power-series.scm).
;;; =====================================================================

(define ct4-stmt
  '(FORALL f
     (IMPLIES (IN f (FUN NN RR))
       (FORALL g
         (IMPLIES (IN g (FUN NN RR))
           (IMPLIES (AND (FORALL n
                           (IMPLIES (IN n NN)
                             (AND (<= 0 (f n)) (<= (f n) (g n)))))
                         (SERIES-CONVERGES g))
             (SERIES-CONVERGES f)))))))

(sp (make-wff ct4-stmt))
(define ct4-typs  (ct-di-landed!))
(define ct4-f     (cadr (car ct4-typs)))
(define ct4-g     (cadr (cadr ct4-typs)))
(define ct4-parts (dk-split! (ct-di-landed-1!)))
(define ct4-terms (or (find-first (lambda (a) (eq? (car a) 'FORALL)) ct4-parts)
                      (error "comparison-test: no termwise hypothesis")))
(define ct4-cg    (or (find-first (lambda (a) (eq? (car a) 'SERIES-CONVERGES)) ct4-parts)
                      (error "comparison-test: no convergence hypothesis")))

;;; NOT `ct4-F' / `ct4-G': the reader folds case, so those name the SEQUENCES
;;; ct4-f / ct4-g and silently overwrite them.
(define ct4-fseq (list 'VNB-LAMBDA 'k 'NN (list 'SERIES-PARTIAL-SUM ct4-f 'k)))
(define ct4-gseq (list 'VNB-LAMBDA 'k 'NN (list 'SERIES-PARTIAL-SUM ct4-g 'k)))

;;; The hypothesis is one universal over a CONJUNCTION; the two order lemmas
;;; each want a universal over one conjunct, and g's nonnegativity (which the
;;; statement never says) follows from 0 <= f(n) <= g(n).
(define (ct4-termwise! concl extra)
  (have! (list 'FORALL 'n (list 'IMPLIES '(IN n NN) concl))
    (lambda ()
      (let ((n (cadr (ct-di-landed-1!))))
        (dk-split! (dk-deepest (lambda () (inst+ ct4-terms n))))
        (extra n)))))

(ct4-termwise! (list '<= 0 (list ct4-f 'n)) (lambda (n) (ass)))
(ct4-termwise! (list '<= (list ct4-f 'n) (list ct4-g 'n)) (lambda (n) (ass)))
(ct4-termwise! (list '<= 0 (list ct4-g 'n))
  (lambda (n)
    (fact 'fun-apply-type-c ct4-f 'NN 'RR n)
    (fact 'fun-apply-type-c ct4-g 'NN 'RR n)
    (ct-ineq (list '<= 0 (list ct4-f n))
             (list '<= (list ct4-f n) (list ct4-g n)))))

(have! (list 'IN ct4-fseq '(FUN NN RR))
  (lambda () (fact 'series-partial-sum-seq-in-fun ct4-f) (ass)))
(have! (list 'IN ct4-gseq '(FUN NN RR))
  (lambda () (fact 'series-partial-sum-seq-in-fun ct4-g) (ass)))

;;; the successor step, in the LAMBDA language monotone-convergence-rr speaks
(define (ct4-step-of seq)
  (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
                         (list '<= (list seq 'k) (list seq '(succ k))))))
(define (ct4-prove-step! h)
  (lambda ()
    (let ((k (cadr (ct-di-landed-1!))))
      (fact 'nn-succ-closed k)            ; both indices typed before the beta
      (mac 'series-partial-sum-seq-apply)
      (fact 'series-partial-sum-monotone-nonneg h k)
      (ass))))

(have! (ct4-step-of ct4-fseq) (ct4-prove-step! ct4-f))
(have! (ct4-step-of ct4-gseq) (ct4-prove-step! ct4-g))

;;; SERIES-CONVERGES g IS convergence of the g-partial-sum sequence (the
;;; def-predicate), unfolded on a SIDE branch: `mac-h' REPLACES the assumption,
;;; and the main branch still wants it.
(have! (list 'CONVERGES 'RR-MS ct4-gseq)
  (lambda () (mac-h 'series-converges ct4-cg) (ass)))

;;; the g-partial-sums are bounded above -- monotone and convergent (L2.5)
(define ct4-bex (dk-fact! 'monotone-convergent-bounded-above ct4-gseq))
(define ct4-bnd (ct-skolem! ct4-bex))
(define ct4-gbound
  (ct-find 'g-bound
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a ct4-bnd)))))

;;; The AND antecedent of monotone-convergence-rr at the f-partial-sums, built
;;; by SUBSTITUTION into the theorem's own statement rather than retyped: a
;;; hand-rebuilt formula is what `fact' silently declines to detach.
(define ct4-mcrr (let ((t (lookup-theorem 'monotone-convergence-rr)))
                   (if (wff? t) (wff-formula t) t)))
(define ct4-mc-ante (subst-free 'f ct4-fseq (cadr (caddr (caddr ct4-mcrr)))))

(mac 'series-converges)                   ; goal: CONVERGES(RR-MS, f-partial-sums)

(have! ct4-mc-ante
  (lambda ()
    (ct-goal-and!
     (lambda ()
       (let ((g (dk-goal)))
         (cond
           ((eq? (car g) 'FORALL) (ass))            ; the step, already in context
           ((eq? (car g) 'IN)     (ass))
           (else
            (ew ct4-bnd)                            ; the SAME bound as g's
            (ct-goal-and!
             (lambda ()
               (if (eq? (car (dk-goal)) 'IN)
                   (ass)
                   (let ((k (cadr (ct-di-landed-1!))))
                     ;; F_k = SPS(f,k) <= SPS(g,k) = G_k <= bnd
                     (mac 'series-partial-sum-seq-apply)
                     (inst+ ct4-gbound k)
                     (mac-h 'series-partial-sum-seq-apply
                            (list '<= (list ct4-gseq k) ct4-bnd))
                     (fact 'series-partial-sum-le-termwise ct4-f ct4-g k)
                     (fact 'series-partial-sum-in-rr k ct4-f)
                     (fact 'series-partial-sum-in-rr k ct4-g)
                     (ct-ineq (list '<= (list 'SERIES-PARTIAL-SUM ct4-f k)
                                        (list 'SERIES-PARTIAL-SUM ct4-g k))
                              (list '<= (list 'SERIES-PARTIAL-SUM ct4-g k)
                                        ct4-bnd)))))))))))))

(fact 'monotone-convergence-rr ct4-fseq)
(ass)

(qed 'comparison-test)
(topic! 'comparison-test 'analysis)
(alias! 'comparison-test "the comparison test"
        "a series dominated termwise by a convergent series converges")

;;; =====================================================================
;;; R4.  THE SERIES TRIANGLE INEQUALITY:  |sum_{n<k} f(n)| <= sum_{n<k} |f(n)|.
;;;
;;; Was an asserted `well-known' support in theorem-library/series-order-lemmas.scm
;;; whose warrant read "induction on k via the SUM-AG recurrence and
;;; rr-abs-triangle at each step".  That is exactly what this is; it lives here
;;; rather than there because the ingredients load here.
;;;
;;; Interactively the whole step from `lam-b' down is one `(supply)'
;;; (ineq-supply.scm) -- this proof is where that tactic's sequence was worked
;;; out.  It is spelled out here on purpose: `supply' is copilot machinery and
;;; loads at load.scm:1502, long after this file, and a library THEOREM should
;;; not depend on the advice layer in any case.  The tactic is for driving; the
;;; file records what it did.
;;;
;;; `k' is quantified FIRST so that `ni' can see the induction variable: the
;;; tactic tests the goal's shape, and with `f' outermost there is no induction
;;; to start.  The step is the panel's own SUPPLY THE ORACLE block -- the
;;; typings, then rr-abs-triangle-c at the two summands, then the oracle -- with
;;; one `lam-b' ahead of it, because until the applied lambda is reduced
;;; `(|f|)(k)' and `|f(k)|' are unrelated ATOMS to `ineq' and no set of true
;;; inequalities about them can close the goal.
;;; =====================================================================

;;; The leaf that is NOT the successor case.  Discriminating on a CONTEXT-free
;;; goal shape would be guesswork here -- both leaves are a guarded universal
;;; over f with the same head -- so the test is the one thing that distinguishes
;;; them, whether `succ' occurs.
;;; (suggest.scm's what-now--occurs? is the same test, but it loads at
;;; load.scm:1502, long after this file.)
(define (ct-occurs? x e)
  (or (equal? x e)
      (and (pair? e) (any-pred (lambda (y) (ct-occurs? x y)) e))))

(define (ct-abs-base-leaf!)
  (let ((hit (let loop ((ls (proof-leaves)))
               (cond ((null? ls) #f)
                     ((not (ct-occurs? 'succ (dk-goal-of (car ls)))) (car ls))
                     (else (loop (cdr ls)))))))
    (if (not hit)
        (error "ct-abs-base-leaf!: no leaf without a succ")
        (begin (set-proof-state-focus! *ps* hit) hit))))

(sp (make-wff "forall([k in nn, f in fun(nn, rr)],
        abs(series-partial-sum(f, k)) <= series-partial-sum(vnb-lambda(n_, nn, abs(f(n_))), k))"))
(ni)

;; BASE.  Both sides collapse to 0 by series-partial-sum-zero, and |0| <= 0 is
;; ground arithmetic.
(ct-abs-base-leaf!)
(di)
(mac 'series-partial-sum-zero)
(arith)

;; STEP.
(di)                                    ; k in nn
(di)                                    ; the induction hypothesis, over all f
(di)                                    ; f in fun(nn, rr)
(inst+ 2 'f)                            ; the hypothesis at THIS f -- BEFORE the
                                        ; facts below, which would shift the index
;; series-partial-sum-succ is GUARDED since 2026-08-29 on its two ARGUMENTS being
;; real (the operation slot holds a set function on CARTESIAN(RR,RR), not the
;; total constant `binplus').  It is applied to BOTH sides here, so all FOUR
;; typings -- the partial sum and the term, for f and for |f| -- have to be in
;; context before the rewrite, not after it.  Every one of them was already
;; cited by this proof; only the order changed.
(fact 'abs-seq-in-fun 'f)               ; |f| is a real sequence ...
(fact 'series-partial-sum-in-rr 'k '(vnb-lambda n_ nn (abs (f n_))))   ; ... so its sum is real
(fact 'fun-apply-type-c '(vnb-lambda n_ nn (abs (f n_))) 'nn 'rr 'k)   ; ... and |f|(k) is real
(fact 'series-partial-sum-in-rr 'k 'f)
(fact 'fun-apply-type-c 'f 'nn 'rr 'k)
(mac 'series-partial-sum-succ)          ; BOTH sides recurse: S(k+1) = S(k) + f(k)
(lam-b)                                 ; (|f|)(k)  ->  |f(k)|
(fact 'rr-abs-triangle-c '(series-partial-sum f k) '(f k))             ; SUBADDITIVITY
(fact 'rr-abs-closed '(series-partial-sum f k))
(fact 'rr-abs-closed '(f k))
(fact 'rr-abs-closed '(+ (series-partial-sum f k) (f k)))
(let ((n (length (dk-asms))))
  (apply ineq (let lp ((i n) (a '())) (if (= i 0) a (lp (- i 1) (cons i a))))))
(qed 'series-partial-sum-abs-le)
(topic! 'series-partial-sum-abs-le 'analysis)
(alias! 'series-partial-sum-abs-le "the series triangle inequality")

