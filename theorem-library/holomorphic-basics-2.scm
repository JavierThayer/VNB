;;; holomorphic-basics-2.scm -- section 2.1 of the user's complex-analysis
;;; notes, finished: the constant and the identity are holomorphic on any open
;;; set, sums and products of holomorphic functions are holomorphic, and so is
;;; z |-> z^n for every natural n.
;;;
;;; theorem-library/holomorphic-basics.scm (batch 13-B) says in its header what
;;; this file supplies:
;;;
;;;    "NOT HERE: `constants and the identity are holomorphic'.  Those are
;;;     instances of the derivative laws over a normed field ... When
;;;     theorem-library/diff-on-laws-2.scm lands, each is one citation of the
;;;     generic law at K = CC-NORMED-FIELD."
;;;
;;; That is right for the DERIVATIVE at a point.  It is NOT the whole story for
;;; HOLOMORPHIC-ON, and the gap is what most of this file is:
;;;
;;; THE MISSING TRANSFER.  `diff-on-sum' and `diff-on-product' conclude about
;;; the LITERAL term (VNB-LAMBDA d2x_ U ((ADD K) (f d2x_) (g d2x_))) -- syntax
;;; the caller did not write and, in the complex case, in the normed field's
;;; own operations rather than the numeric `+' and `*' the rest of the CC
;;; library speaks.  The function actually in hand is some other term agreeing
;;; with it at every point of U.  For IS-DIFF-AT that gap is closed by
;;; `diff-transfer-ptwise-eq' (theorem-library/diff-transfer.scm); for
;;; IS-DIFF-ON there was NO such theorem, so the first two items here are the
;;; two storeys of it:
;;;
;;;   diff-on-transfer-ptwise-eq    the exact mirror of diff-transfer-ptwise-eq:
;;;                                 the Caratheodory factor does not move, only
;;;                                 the last conjunct mentions the function, and
;;;                                 two instances of the pointwise equation
;;;                                 rewrite f(x) and f(a) to g(x) and g(a);
;;;   holomorphic-transfer-ptwise-eq  the same, one quantifier up.
;;;
;;; Everything after them is short.  The one place where CC is more than a
;;; parameter is the pointwise lane of the sum and the product, where the
;;; lambda's body ((ADD CC-NORMED-FIELD) (f x) (g x)) has to be read as
;;; (f x) + (g x): that is `cc-nf-add-apply' / `cc-nf-mul-apply'
;;; (theorem-library/holomorphic-basics.scm), one citation each.
;;;
;;; THE POWER.  `power' IS typed on CC: the kernel's `power-typing-nonneg'
;;; (number-systems.scm:846) gives (IN (power x n) CC) for x in CC and n in NN,
;;; and `power-zero' / `power-succ' are the recursion, so `x ^ n in cc' IS a
;;; theorem of the arithmetic base and nothing had to be assumed.  The
;;; induction is on n, stated FIRST so that `ni' sees the literal shape
;;; (FORALL n (IMPLIES (IN n NN) ...)) it tests for.  The base is `power-zero'
;;; plus the constant; the step is `power-succ' plus the identity, the product
;;; and the induction hypothesis instantiated at the lambda z |-> z^n.
;;;
;;; EMPTY U.  U = EMPTY-SET is open, and HOLOMORPHIC-ON(EMPTY-SET, f) is then
;;; TRUE and vacuous -- its last conjunct quantifies over the points of U and
;;; there are none -- exactly as structure-library/diff-on.scm:50 intends
;;; ("NO INHABITEDNESS GUARD ... Nothing below may acquire a guard that excludes
;;; it").  Every statement here is therefore also vacuously true at U =
;;; EMPTY-SET, and none of them carries an inhabitedness hypothesis.
;;;
;;; NOT HERE: 1/z AND THE QUOTIENT RULE.  The route through
;;; `normed-field-mul-inverses' would BILL that asserted support, and the batch
;;; brief forbids it; see the report for what a CC-specific route needs.
;;;
;;; WHY THE OPENNESS HYPOTHESES ARE STATED IN CC-MS.  HOLOMORPHIC-ON states its
;;; own openness conjunct over NF-METRIC-SPACE(CC-NORMED-FIELD), because that is
;;; the space IS-DIFF-ON speaks of; every other complex statement in the library
;;; says CC-MS.  `cc-ms-open-iff' is the single citation between them, and the
;;; two theorems below that take openness as a HYPOTHESIS (the constant and the
;;; identity, and the power) take it in the CC-MS reading, which is the one a
;;; consumer will have.
;;;
;;; LOAD WINDOW.  lo = theorem-library/diff-on-laws-2 (diff-on-const,
;;; diff-on-identity, diff-on-sum, diff-on-product, nf-lam-const-in-fun,
;;; nf-lam-id-in-fun, nf-zero-in-carr, nf-one-in-carr) and
;;; theorem-library/holomorphic-basics (cc-ms-open-iff, cc-nf-add-apply,
;;; cc-nf-mul-apply), whichever is later -- holomorphic-basics is slotted
;;; immediately after diff-on-laws, and diff-on-laws-2 after
;;; ms-continuity-algebra, so the file goes after BOTH.  Everything else is far
;;; below: diff-on-laws (the read-offs, cc-nf-carr, holomorphic-on-*),
;;; numeric-instances (CC-NORMED-FIELD), cc-normed-field (cc-is-normed-field),
;;; set-basics (subset-mem-fwd), number-systems (the `power' axioms).  hi is
;;; unconstrained: nothing cites these names yet.  Concretely
;;; (scratchpad/window.py, 2026-09-21): lo = 2870, the load.scm line of
;;; "theorem-library/holomorphic-basics"; hi = none.  The proposed slot is the
;;; line immediately after it.
;;;
;;; Helper prefix: `hb2-'.

;;; =====================================================================
;;; File-local driver helpers.
;;; =====================================================================

(define (hb2-head e) (and (pair? e) (car e)))

(define (hb2-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "hb2-find: no context formula" what))
          ((pred (car l)) (car l))
          (#t (loop (cdr l))))))

;;; the pointwise hypothesis of a transfer-form statement: the FORALL mentioning
;;; the combined function FN.
(define (hb2-ptw fn)
  (hb2-find (list 'pointwise fn)
    (lambda (x) (and (pair? x) (eq? (car x) 'FORALL) (dk-contains? x fn)))))

(define hb2-nf 'CC-NORMED-FIELD)
(define hb2-carr '(CARR CC-NORMED-FIELD))

;;; (IS-OPEN (NF-METRIC-SPACE CC-NORMED-FIELD) U) from (IS-OPEN CC-MS U).
(define (hb2-nf-open!)
  (fact 'cc-ms-open-iff 'U)
  (dk-have! '(IS-OPEN (NF-METRIC-SPACE CC-NORMED-FIELD) U) (lambda () (prop))))

;;; (SUBSET U CC) -- and, on the way, (SUBSET U (CARR CC-NORMED-FIELD)), which
;;; is what `nf-lam-id-in-fun' asks for -- from the NF reading of the openness.
(define (hb2-u-subset-cc!)
  (fact 'cc-is-normed-field)
  (fact 'nf-open-subset-carr hb2-nf 'U)
  (fact 'cc-nf-carr)
  (dk-have! '(SUBSET U CC)
    (lambda () (subst (list '== 'CC hb2-carr)) (ass))))

;;; (IN U SET) -- the OUTERMOST antecedent of every `nf-lam-*-in-fun', and the
;;; one a reading of those statements by their names would miss.
(define (hb2-u-set!)
  (fact 'cc-is-normed-field)
  (fact 'nf-open-is-set hb2-nf 'U))

;;; the two readings of a FUN class over U: CC and CARR(CC-NORMED-FIELD).
(define (hb2-fun-carr! t)
  (fact 'cc-nf-carr)
  (dk-have! (list 'IN t (list 'FUN 'U hb2-carr))
    (lambda () (subst (list '== hb2-carr 'CC)) (ass))))
(define (hb2-fun-cc! t)
  (fact 'cc-nf-carr)
  (dk-have! (list 'IN t '(FUN U CC))
    (lambda () (subst (list '== 'CC hb2-carr)) (ass))))

;;; =====================================================================
;;; (1) THE POINTWISE TRANSFER FOR IS-DIFF-ON.
;;;
;;; The mirror of `diff-transfer-ptwise-eq' (theorem-library/diff-transfer.scm),
;;; and it works for the same reason: the whole of the Caratheodory factor's
;;; job -- its FUN typing, its continuity at a, its value at a -- is about phi
;;; alone.  Only the last conjunct mentions the function, and there f(x) and
;;; f(a) are rewritten to g(x) and g(a) by two instances of the pointwise
;;; hypothesis.  So the SAME phi witnesses both, and the proof cites nothing.
;;;
;;; The hypothesis (IN f (FUN U (CARR K))) is not redundant, for the reason
;;; diff-transfer.scm:42 gives: pointwise agreement with a function says nothing
;;; about f off U or about f being a set of pairs at all.
;;; =====================================================================

(sp (make-wff
     '(FORALL K (FORALL U (FORALL f (FORALL g (FORALL a (FORALL dl
        (IMPLIES (IN f (FUN U (CARR K)))
        (IMPLIES (IS-DIFF-ON K U g a dl)
        (IMPLIES (FORALL hbx_ (IMPLIES (IN hbx_ U) (== (f hbx_) (g hbx_))))
                 (IS-DIFF-ON K U f a dl))))))))))))
(dk-peel!)
(define hbt-ptw (hb2-find 'pointwise
                  (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                   (dk-contains? x 'f)))))
(define hbt-hyp '(IS-DIFF-ON K U g a dl))
(fact 'diff-on-pt-in 'K 'U 'g 'a 'dl)
(dk-split! (dk-landed-find (lambda () (mac-h 'IS-DIFF-ON hbt-hyp))
                           (lambda (x) (eq? (car x) 'AND))))
(define hbt-phi
  (dk-skolem! (hb2-find 'the-factor
                (lambda (x) (and (pair? x) (eq? (car x) 'FORSOME))))))
(define hbt-id
  (hb2-find 'factorization
    (lambda (x) (and (pair? x) (eq? (car x) 'FORALL) (dk-contains? x hbt-phi)
                     (dk-contains? x 'g)))))
(mac 'IS-DIFF-ON)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (hb2-head (dk-goal)) 'FORSOME))
       (ass)
       (begin
         (ew hbt-phi)
         (dk-conj-close!
          (lambda ()
            (if (not (eq? (hb2-head (dk-goal)) 'FORALL))
                (ass)
                (let ((z (dk-di-var!)))
                  (inst+ hbt-ptw z)
                  (inst+ hbt-ptw 'a)
                  (subst (list '== (list 'f z) (list 'g z)))
                  (subst '(== (f a) (g a)))
                  (inst+ hbt-id z)
                  (ass)))))))))
(qed 'diff-on-transfer-ptwise-eq)
(topic! 'diff-on-transfer-ptwise-eq 'analysis)
(alias! 'diff-on-transfer-ptwise-eq
        "a map agreeing pointwise on U with one differentiable on U is differentiable, same derivative")

;;; =====================================================================
;;; (2) THE SAME, ONE QUANTIFIER UP: HOLOMORPHIC-ON.
;;; =====================================================================

(sp (make-wff
     '(FORALL U (FORALL f (FORALL g
        (IMPLIES (HOLOMORPHIC-ON U g)
        (IMPLIES (IN f (FUN U CC))
        (IMPLIES (FORALL hbx_ (IMPLIES (IN hbx_ U) (== (f hbx_) (g hbx_))))
                 (HOLOMORPHIC-ON U f)))))))))
(dk-peel!)
(define hbh-ptw (hb2-find 'pointwise
                  (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                   (dk-contains? x 'f)))))
(fact 'holomorphic-on-open 'U 'g)
(fact 'holomorphic-on-diff 'U 'g)
(define hbh-univ (hb2-find 'diff-universal
                   (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                    (dk-contains? x 'IS-DIFF-ON)))))
(hb2-fun-carr! 'f)
(mac 'HOLOMORPHIC-ON)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (hb2-head (dk-goal)) 'FORALL))
       (ass)
       (let* ((a  (dk-di-var!))
              (ex (dk-apply! hbh-univ a))
              (lw (dk-skolem! ex)))
         (fact 'diff-on-transfer-ptwise-eq hb2-nf 'U 'f 'g a lw)
         (ew lw)
         (ass)))))
(qed 'holomorphic-transfer-ptwise-eq)
(topic! 'holomorphic-transfer-ptwise-eq 'analysis)
(alias! 'holomorphic-transfer-ptwise-eq
        "a map agreeing pointwise with a holomorphic map is holomorphic")

;;; =====================================================================
;;; (3) THE CONSTANT AND (4) THE IDENTITY.
;;;
;;; One citation each of `diff-on-const' / `diff-on-identity' at
;;; K = CC-NORMED-FIELD, as holomorphic-basics.scm predicted; the rest is the
;;; two readings of openness and of the FUN class.
;;; =====================================================================

(sp (make-wff
     '(FORALL U (IMPLIES (IS-OPEN CC-MS U)
        (FORALL hbc_ (IMPLIES (IN hbc_ CC)
          (HOLOMORPHIC-ON U (VNB-LAMBDA hbx_ U hbc_))))))))
(dk-peel!)
(hb2-nf-open!)
(fact 'cc-is-normed-field)
(fact 'cc-nf-carr)
(dk-have! (list 'IN 'hbc_ hb2-carr)
          (lambda () (subst (list '== hb2-carr 'CC)) (ass)))
(hb2-u-set!)
(fact 'nf-lam-const-in-fun hb2-nf 'U 'hbc_)
(hb2-fun-cc! '(VNB-LAMBDA d2x_ U hbc_))
(mac 'HOLOMORPHIC-ON)
(dk-conj-close!
 (lambda ()
   (let ((gl (dk-goal)))
     (cond ((eq? (hb2-head gl) 'IS-OPEN) (ass))
           ((eq? (hb2-head gl) 'IN) (ass))
           (#t (let ((a (dk-di-var!)))
                 (fact 'diff-on-const hb2-nf 'U 'hbc_ a)
                 (ew (list 'ZERO hb2-nf))
                 (ass)))))))
(qed 'holomorphic-const)
(topic! 'holomorphic-const 'analysis)
(alias! 'holomorphic-const "a constant function is holomorphic on any open set")

(sp (make-wff
     '(FORALL U (IMPLIES (IS-OPEN CC-MS U)
        (HOLOMORPHIC-ON U (VNB-LAMBDA hbx_ U hbx_))))))
(dk-peel!)
(hb2-nf-open!)
(fact 'cc-is-normed-field)
(hb2-u-set!)
(hb2-u-subset-cc!)
(fact 'nf-lam-id-in-fun hb2-nf 'U)
(hb2-fun-cc! '(VNB-LAMBDA d2x_ U d2x_))
(mac 'HOLOMORPHIC-ON)
(dk-conj-close!
 (lambda ()
   (let ((gl (dk-goal)))
     (cond ((eq? (hb2-head gl) 'IS-OPEN) (ass))
           ((eq? (hb2-head gl) 'IN) (ass))
           (#t (let ((a (dk-di-var!)))
                 (fact 'diff-on-identity hb2-nf 'U a)
                 (ew (list 'ONE hb2-nf))
                 (ass)))))))
(qed 'holomorphic-identity)
(topic! 'holomorphic-identity 'analysis)
(alias! 'holomorphic-identity "the identity is holomorphic on any open set")

;;; =====================================================================
;;; (5) SUMS AND (6) PRODUCTS.
;;;
;;; Stated in TRANSFER form -- the combined function is a parameter, tied to
;;; the combination by a pointwise equation in the NUMERIC operations -- so that
;;; no consumer meets a VNB-LAMBDA or the normed field's own ADD / MUL.  The two
;;; proofs differ only in the law cited, the applied slot equation, and the
;;; operator; `hb2-combine!' is that difference made into three arguments.  The
;;; derivative is never written down: it is read off the law's own conclusion
;;; and handed straight to `ew'.
;;; =====================================================================

(define (hb2-combine! law kop applylaw op)
  (let ((ptw (hb2-ptw 'sm)))
    (fact 'cc-is-normed-field)
    (fact 'holomorphic-on-open 'U 'f)
    (fact 'holomorphic-on-in-fun 'U 'f)
    (fact 'holomorphic-on-in-fun 'U 'g)
    (fact 'holomorphic-on-diff 'U 'f)
    (fact 'holomorphic-on-diff 'U 'g)
    (let ((uf (hb2-find 'f-universal
                (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                 (dk-contains? x 'IS-DIFF-ON) (dk-contains? x 'f)))))
          (ug (hb2-find 'g-universal
                (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                 (dk-contains? x 'IS-DIFF-ON) (dk-contains? x 'g))))))
      (hb2-fun-carr! 'sm)
      (mac 'HOLOMORPHIC-ON)
      (dk-conj-close!
       (lambda ()
         (let ((gl (dk-goal)))
           (cond ((eq? (hb2-head gl) 'IS-OPEN) (ass))
                 ((eq? (hb2-head gl) 'IN) (ass))
                 (#t
                  (let* ((a  (dk-di-var!))
                         (lf (dk-skolem! (dk-apply! uf a)))
                         (lg (dk-skolem! (dk-apply! ug a)))
                         (res (dk-fact! law hb2-nf 'U 'f 'g a lf lg))
                         (lam (list-ref res 3))
                         (val (list-ref res 5)))
                    (dk-have!
                     (list 'FORALL 'hbw_ (list 'IMPLIES '(IN hbw_ U)
                       (list '== '(sm hbw_) (list lam 'hbw_))))
                     (lambda ()
                       (di)
                       (fact 'fun-apply-type-c 'f 'U 'CC 'hbw_)
                       (fact 'fun-apply-type-c 'g 'U 'CC 'hbw_)
                       (dk-lam-b!)
                       (fact applylaw '(f hbw_) '(g hbw_))
                       (subst (list '== (list (list kop hb2-nf) '(f hbw_) '(g hbw_))
                                        (list op '(f hbw_) '(g hbw_))))
                       (inst+ ptw 'hbw_)
                       (subst (list '== '(sm hbw_) (list op '(f hbw_) '(g hbw_))))
                       (qrfl)))
                    (fact 'diff-on-transfer-ptwise-eq hb2-nf 'U 'sm lam a val)
                    (ew val)
                    (ass))))))))))

(sp (make-wff
     '(FORALL U (FORALL f (FORALL g (FORALL sm
        (IMPLIES (HOLOMORPHIC-ON U f)
        (IMPLIES (HOLOMORPHIC-ON U g)
        (IMPLIES (IN sm (FUN U CC))
        (IMPLIES (FORALL hbx_ (IMPLIES (IN hbx_ U)
                   (== (sm hbx_) (+ (f hbx_) (g hbx_)))))
                 (HOLOMORPHIC-ON U sm)))))))))))
(dk-peel!)
(hb2-combine! 'diff-on-sum 'ADD 'cc-nf-add-apply '+)
(qed 'holomorphic-sum)
(topic! 'holomorphic-sum 'analysis)
(alias! 'holomorphic-sum "the sum of two holomorphic functions is holomorphic")

(sp (make-wff
     '(FORALL U (FORALL f (FORALL g (FORALL sm
        (IMPLIES (HOLOMORPHIC-ON U f)
        (IMPLIES (HOLOMORPHIC-ON U g)
        (IMPLIES (IN sm (FUN U CC))
        (IMPLIES (FORALL hbx_ (IMPLIES (IN hbx_ U)
                   (== (sm hbx_) (* (f hbx_) (g hbx_)))))
                 (HOLOMORPHIC-ON U sm)))))))))))
(dk-peel!)
(hb2-combine! 'diff-on-product 'MUL 'cc-nf-mul-apply '*)
(qed 'holomorphic-product)
(topic! 'holomorphic-product 'analysis)
(alias! 'holomorphic-product "the product of two holomorphic functions is holomorphic")

;;; =====================================================================
;;; (7) z |-> z^n.
;;;
;;; Induction on n, with n FIRST so that `ni' sees the shape it tests for.
;;; Base: power-zero makes the map the constant 1.  Step: power-succ makes it
;;; the product of the identity with z |-> z^n, and the induction hypothesis is
;;; instantiated at the LAMBDA z |-> z^n -- which is why the statement is in
;;; transfer form and quantifies over the map: an induction that feeds its own
;;; conclusion back into the next rung needs the map to be a parameter.
;;; =====================================================================

(sp (make-wff
     '(FORALL hbn_ (IMPLIES (IN hbn_ NN)
        (FORALL U (IMPLIES (IS-OPEN CC-MS U)
          (FORALL pw_ (IMPLIES (IN pw_ (FUN U CC))
            (IMPLIES (FORALL hbz_ (IMPLIES (IN hbz_ U)
                       (== (pw_ hbz_) (power hbz_ hbn_))))
                     (HOLOMORPHIC-ON U pw_))))))))))
(define hbp-br (use-induction))

;;; ---- base: n = 0.  z^0 = 1 on U, so pw_ agrees pointwise with the constant 1.
(dk-focus! (cdr (assq 'base hbp-br)))
(dk-peel!)
(define hbp-b-ptw (hb2-ptw 'pw_))
(hb2-nf-open!)
(hb2-u-subset-cc!)
(fact 'rr-one-in)
(fact 'rr-subset-cc 1)
(fact 'holomorphic-const 'U 1)
(dk-have! '(FORALL hbw_ (IMPLIES (IN hbw_ U)
             (== (pw_ hbw_) ((VNB-LAMBDA d2x_ U 1) hbw_))))
  (lambda ()
    (di)
    (fact 'subset-mem-fwd 'U 'CC 'hbw_)
    (dk-lam-b!)
    (inst+ hbp-b-ptw 'hbw_)
    (fact 'power-zero 'hbw_)
    (subst '(== (pw_ hbw_) (power hbw_ 0)))
    (subst '(= (power hbw_ 0) 1))
    (qrfl)))
(fact 'holomorphic-transfer-ptwise-eq 'U 'pw_ '(VNB-LAMBDA d2x_ U 1))
(ass)

;;; ---- step: z^(n+1) = z . z^n, the identity times the n-th power.
(dk-focus! (cdr (assq 'step hbp-br)))
(define hbp-ih (cdr (assq 'ih hbp-br)))
(define hbp-n  (cdr (assq 'var hbp-br)))
(dk-peel!)
(define hbp-s-ptw (hb2-ptw 'pw_))
(hb2-nf-open!)
(hb2-u-subset-cc!)
(hb2-u-set!)                       ; `lam-t' owes the SETHOOD of the domain
(define hbp-lam (list 'VNB-LAMBDA 'hbz_ 'U (list 'power 'hbz_ hbp-n)))
(define hbp-idl '(VNB-LAMBDA d2x_ U d2x_))

;;; the n-th power map is a function U -> CC ...
(dk-have! (list 'IN hbp-lam '(FUN U CC))
  (lambda ()
    (dk-lam-t!)
    (let ((z (dk-di-var!)))
      (fact 'subset-mem-fwd 'U 'CC z)
      (have! (list 'AND (list 'IN z 'CC) (list 'IN hbp-n 'NN)))
      (fact 'power-typing-nonneg z hbp-n)
      (ass))))
;;; ... it agrees pointwise with z |-> z^n by beta ...
(dk-have! (list 'FORALL 'hbw_ (list 'IMPLIES '(IN hbw_ U)
            (list '== (list hbp-lam 'hbw_) (list 'power 'hbw_ hbp-n))))
  (lambda ()
    (di)
    (fact 'subset-mem-fwd 'U 'CC 'hbw_)
    (have! (list 'AND '(IN hbw_ CC) (list 'IN hbp-n 'NN)))
    (fact 'power-typing-nonneg 'hbw_ hbp-n)
    (dk-lam-b!)
    (qrfl)))
;;; ... so the induction hypothesis applies to it ...
(dk-apply! hbp-ih 'U hbp-lam)
;;; ... and so does the identity.
(fact 'holomorphic-identity 'U)

;;; the pointwise equation the product rule wants
(dk-have! (list 'FORALL 'hbw_ (list 'IMPLIES '(IN hbw_ U)
            (list '== '(pw_ hbw_) (list '* (list hbp-idl 'hbw_) (list hbp-lam 'hbw_)))))
  (lambda ()
    (di)
    (fact 'subset-mem-fwd 'U 'CC 'hbw_)
    (have! (list 'AND '(IN hbw_ CC) (list 'IN hbp-n 'NN)))
    (fact 'power-typing-nonneg 'hbw_ hbp-n)
    (dk-lam-b!)
    (inst+ hbp-s-ptw 'hbw_)
    (fact 'power-succ 'hbw_ hbp-n)
    (subst (list '== '(pw_ hbw_) (list 'power 'hbw_ (list 'succ hbp-n))))
    (subst (list '= (list 'power 'hbw_ (list 'succ hbp-n))
                    (list '* 'hbw_ (list 'power 'hbw_ hbp-n))))
    (qrfl)))
(fact 'holomorphic-product 'U hbp-idl hbp-lam 'pw_)
(ass)
(qed 'holomorphic-power)
(topic! 'holomorphic-power 'analysis)
(alias! 'holomorphic-power "the monomial z^n is holomorphic on any open set")
