;;; rake-analysis-typing.scm -- BATCH H of the leaf rake (2026-09-17): the four
;;; ANALYSIS typing leaves.  Two are proven as stated; two are UNDERDETERMINED as
;;; stated -- the same defect that made `nth-deriv-v-in-vec' false -- and are
;;; proven here with the guard their scalar twins already carry.
;;;
;;;   (A) embed-in-fun          structure-library/metric-completion.scm:147
;;;                             PROVEN modulo 0, statement unchanged.
;;;   (B) gof-in-fun            theorem-library/vector-taylor-proof.scm:475
;;;                             PROVEN modulo 0, statement unchanged.
;;;   (C) vtaylor-poly-in-vec   theorem-library/vector-taylor-proof.scm:449
;;;   (D) vtaylor-remainder-in-vec  ...:463
;;;                             PROVEN modulo 0 WITH A GUARD -- see below.
;;;
;;; ---------------------------------------------------------------------
;;; THE GUARD FINDING (C) and (D).
;;;
;;; Both statements quantify m, f, a, x, n with the hypotheses "m is a normed
;;; vector space, f : RR -> VEC(m), a, x real, n natural" and conclude that
;;; TAYLOR-POLY-V(m,f,a,x,n) -- resp. the remainder f(x) (-) that polynomial --
;;; is a vector.  TAYLOR-POLY-V's recursion step applies (ACT m) to
;;; (NTH-DERIV-V m f (succ k))(a), and NTH-DERIV-V(m,f,succ k) is
;;; VNB-LAMBDA y in RR. DERIV-V(m, f^(k), y) = IOTA L. IS-DIFF-AT-V(m, f^(k), y, L).
;;; Nothing in the hypotheses says f is differentiable, so for n >= 1 that IOTA
;;; need not denote.  Concretely: take m the one-dimensional real normed space
;;; and f(t) = abs(t), a total element of FUN(RR, VEC(m)); at a = 0, n = 1,
;;; IS-DIFF-AT-V(m, f, 0, L) has NO satisfier, DERIV-V(m,f,0) is undefined, and
;;; TAYLOR-POLY-V(m,f,0,x,1) -- a VADD one of whose arguments is an ACT at an
;;; undefined vector -- is not in VEC(m).  The statements are therefore FALSE
;;; as written, exactly as `nth-deriv-v-in-vec' was (the spliced block of
;;; vector-taylor-proof.scm records that finding and the user's decision:
;;; add the guard, prove the guarded statement).
;;;
;;; The guard is the one that block already defines and already proves things
;;; about -- DFUN-V(m,f,n), "every derivative up to order n is a total map
;;; RR -> VEC(m)" -- added as the INNERMOST antecedent, so the binders and the
;;; body of each statement stay byte-identical to the support site:
;;;
;;;   DFUN-V(m,f,n) := forall j_. j_ in NN and j_ <= n
;;;                              =>  NTH-DERIV-V(m,f,j_) in FUN(RR, VEC m)
;;;
;;; THE CITER CAN DISCHARGE IT.  `vtaylor-remainder-in-vec' has exactly one
;;; citer, vector-taylor-proof.scm:588, and at that line the context holds
;;; TAYLOR-DIFFERENTIABLE-V(m,f,a,x,n), (IN a RR), (IN x RR) and (< a x) -- the
;;; antecedents of `taylor-v-derivs-in-fun', proven in the same file.  So the
;;; citer changes by ONE line:
;;;
;;;   vector-taylor-proof.scm:588
;;;     (quietly (lambda () (fact 'vtaylor-remainder-in-vec 'm 'f 'a 'x 'n)))
;;;     -->
;;;     (quietly (lambda () (fact 'taylor-v-derivs-in-fun 'm 'f 'a 'x 'n)))
;;;     (quietly (lambda () (fact 'vtaylor-remainder-in-vec 'm 'f 'a 'x 'n)))
;;;
;;; `vtaylor-poly-in-vec' has no citer at all.
;;;
;;; ---------------------------------------------------------------------
;;; LOAD WINDOWS.  This file is ONE file for the report; it is TWO placements.
;;;
;;; Section A (embed-in-fun and its five helpers) is STANDALONE:
;;;   window [257, end).  lo = 257 because `metric-self-zero' is proven in
;;;   structure-library/metric-laws (position 256); every other citation is
;;;   lower (metric-completion 74 for the definitions, injection 83 for
;;;   image-membership-iff, pos-rr-bridges 177 for rr-lt-of-pos-rr, and the
;;;   base-library axioms fun-set-iff / nn-is-set / nn-zero-in).  No citer
;;;   forces hi: nothing in the library cites embed-in-fun (the only other
;;;   occurrence of the name is pss-topics.scm's `topic!').
;;;
;;; Sections B, C, D must be SPLICED into theorem-library/vector-taylor-proof.scm,
;;;   after the existing "END spliced block" marker and BEFORE the `(sp ...)' of
;;;   vector-taylor-remainder-bound (line 571) -- the same reason the 2026-09-14
;;;   block is spliced there: they unfold that file's own definitions
;;;   (TAYLOR-POLY-V and its recursion axioms, NTH-DERIV-V) and cite its
;;;   file-local theorems (nth-deriv-v-in-vec, dfun-v-mono), and they are cited
;;;   at :588 and :602 of the same file.
;;;
;;;   ONE LOAD-ORDER MOVE IS REQUIRED.  Section C cites `nvs-act-in-vec', proven
;;;   in theorem-library/nvs-act-laws (position 446) -- AFTER vector-taylor-proof
;;;   (445).  nvs-act-laws' own declared window is (nvs-module-view 441,
;;;   directional-derivative 447), so it can be moved to position 442, directly
;;;   after nvs-module-view and before noetherian-maximal-proof; then the splice
;;;   window is non-empty.  Without that move sections C and D cannot be placed
;;;   at all.
;;;
;;; Other citations of C/D, all well below 445: recip-factorial-in-rr and
;;; factorial-real-pos (taylor-proof 439), power-closed-at (dyadic-weights 391),
;;; nvs-vadd-in-vec (op-typing), fun-apply-type-c (fun-apply-type-proof 163),
;;; rr-sub-in-rr, rr-mul-closed, nn-zero-in / nn-succ-closed / nn-le-succ.
;;; Section B cites fun-apply-type-c (163), the IS-BOUNDED-LINEAR-FUNCTIONAL /
;;; IS-LINEAR-FUNCTIONAL unfolds (linear-functional 64), COMPOSE (compose 18)
;;; and the base axioms fun-codomain-iff / dom-of-fun / rr-is-set.
;;;
;;; SITES TO RETIRE
;;;   structure-library/metric-completion.scm:146-152  (support + warrant! embed-in-fun)
;;;   theorem-library/vector-taylor-proof.scm:474-483  (add-to-pss + warrant! gof-in-fun)
;;;   theorem-library/vector-taylor-proof.scm:448-458  (vtaylor-poly-in-vec)
;;;   theorem-library/vector-taylor-proof.scm:461-472  (vtaylor-remainder-in-vec)
;;;
;;; THE SPLIT IS MECHANICAL.  Section A uses only `rkt-pts-in-set!', defined in
;;; it; sections C and D use only `rkt-imps' / `rkt-alls' / `rkt-dfun-v' /
;;; `rkt-coef' / `rkt-coeff-real!' / `rkt-term-in-vec!', defined at the head of
;;; section C; section B uses none.  So "everything above SECTION B" is the
;;; standalone file and "SECTION B onwards" is the splice, with no helper
;;; crossing the cut and no theorem of one half cited by the other.
;;;
;;; Helper prefix: rkt-.

;;; =====================================================================
;;; SECTION A -- embed-in-fun.
;;;
;;; EMBED(M) = VNB-LAMBDA u in PTS(M). CLASS(CAUCHY-SETOID M, EMBED-SEQ(M,u)),
;;; and the claim is that it lands in PTS(COMPLETION M).  Four things have to
;;; be produced, and none of them needs `cauchy-setoid-is-setoid' or
;;; `class-in-quotient' (both still asserted): the route is through
;;; image-membership-iff and PROJ's beta rule directly, so the whole section
;;; bills `modulo 0'.
;;;
;;;   (A1) PTS(COMPLETION M) == QUOTIENT(CAUCHY-SETOID M), and
;;;        PTS(CAUCHY-SETOID M) == CSEQ(M): COMPLETION and CAUCHY-SETOID are
;;;        def-functoid LISTs, so `slot' has no projection for them and the
;;;        carrier is read off by mac + slot + nth-r (bdd-metric-carrier's
;;;        recipe, as nvs-ms-pts does it in vector-taylor-proof.scm).
;;;   (A2) sethood: CSEQ(M) is a SEP over FUN(NN, PTS M), a set by fun-set-iff;
;;;        CLASS(...) is a SEP over PTS(CAUCHY-SETOID M) = CSEQ(M).  The CLASS
;;;        sethood is what `rfl' needs at the end -- pi-reflexivity! closes
;;;        t = t only for a term the context establishes as DEFINED.
;;;   (A3) the constant sequence is Cauchy: N := 0 and d(u,u) = 0 <= eps.
;;;   (A4) the class of a Cauchy sequence is in the quotient: QUOTIENT is an
;;;        IMAGE, so image-membership-iff plus the beta rule of PROJ.
;;; =====================================================================

;;; (A1) ---------------------------------------------------------------
(sp (make-wff '(FORALL M (== (PTS (COMPLETION M)) (QUOTIENT (CAUCHY-SETOID M))))))
(di) (mac 'COMPLETION) (slot 'PTS) (nth-r) (qrfl)
(qed 'rkt-completion-pts)
(topic! 'rkt-completion-pts 'plumbing)
(gloss! 'rkt-completion-pts
  "The points of the completion are the classes of Cauchy sequences: the carrier
   read off the COMPLETION pair, as a citable equation.")

(sp (make-wff '(FORALL M (== (PTS (CAUCHY-SETOID M)) (CSEQ M)))))
(di) (mac 'CAUCHY-SETOID) (slot 'PTS) (nth-r) (qrfl)
(qed 'rkt-cauchy-setoid-pts)
(topic! 'rkt-cauchy-setoid-pts 'plumbing)
(gloss! 'rkt-cauchy-setoid-pts
  "The points of the Cauchy setoid are the Cauchy sequences.")

;;; (IN (PTS mm) SET) out of IS-METRIC-SPACE(mm) -- in a `have!' LANE, because
;;; `mac-h' REPLACES what it unfolds and every later `fact' wants the predicate.
(define (rkt-pts-in-set! mm)
  (have! (list 'IN (list 'PTS mm) 'SET)
         (lambda ()
           (dk-split-all!
            (dk-landed (lambda () (mac-h 'IS-METRIC-SPACE (list 'IS-METRIC-SPACE mm)))))
           (ass))))

;;; (A2) ---------------------------------------------------------------
(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M) (IN (CSEQ M) SET)))))
(dk-peel!)
(rkt-pts-in-set! 'M)
(fact 'nn-is-set)
(mac 'CSEQ) (sep-set) (mac 'fun-set-iff) (prop)
(qed 'rkt-cseq-is-set)
(topic! 'rkt-cseq-is-set 'plumbing)

(sp (make-wff '(FORALL M (FORALL w_ (IMPLIES (IS-METRIC-SPACE M)
     (IN (CLASS (CAUCHY-SETOID M) w_) SET))))))
(dk-peel!)
(fact 'rkt-cseq-is-set 'M)
(mac 'CLASS) (sep-set) (mac 'rkt-cauchy-setoid-pts) (ass)
(qed 'rkt-class-is-set)
(topic! 'rkt-class-is-set 'plumbing)

;;; (A3) ---------------------------------------------------------------
(sp (make-wff '(FORALL M (FORALL u
   (IMPLIES (IS-METRIC-SPACE M) (IMPLIES (IN u (PTS M))
     (IN (EMBED-SEQ M u) (FUN NN (PTS M)))))))))
(dk-peel!)
(mac 'EMBED-SEQ)
(dk-lam-t!)                             ; pays the (IN NN SET) leaf
(di)
(ass)
(qed 'rkt-embed-seq-in-fun)
(topic! 'rkt-embed-seq-in-fun 'analysis)

;;; The constant sequence is Cauchy.  The three conjuncts of the IS-CAUCHY-SEQ
;;; unfold are split by dk-conj-close!; only the eps-conjunct has content, and
;;; there N := 0 works because d(u,u) = 0 and 0 <= eps for a POS-RR eps.
;;; `(FORALL eps (IMPLIES (POS-RR eps) ...))' is the UNGUARDED shape, so it
;;; takes TWO `di's -- one for the quantifier, one for the antecedent.
(sp (make-wff '(FORALL M (FORALL u
   (IMPLIES (IS-METRIC-SPACE M) (IMPLIES (IN u (PTS M))
     (IS-CAUCHY-SEQ M (EMBED-SEQ M u))))))))
(dk-peel!)
(fact 'rkt-embed-seq-in-fun 'M 'u)
(mac 'IS-CAUCHY-SEQ)
(dk-conj-close!
  (lambda ()
    (if (not (eq? (car (dk-goal)) 'FORALL))
        (ass)
        (begin
          (di) (di)                                     ; eps, POS-RR(eps)
          (fact 'nn-zero-in)
          (ew 0)                                        ; N := 0
          (for-each
           (lambda (rkt-leaf)
             (dk-focus! rkt-leaf)
             (if (eq? (car (dk-goal)) 'IN)
                 (ass)                                  ; 0 in NN
                 (begin (di)                            ; the two NN-typed indices
                        (mac 'EMBED-SEQ)
                        (lam-b)                         ; one beta does BOTH occurrences
                        (di)                            ; the 0 <= m and 0 <= n antecedent
                        (fact 'metric-self-zero 'M 'u)
                        (subst '(= ((DIST M) u u) 0))
                        (fact 'rr-lt-of-pos-rr 'eps)
                        (dk-split! (dk-landed-1 (lambda () (mac-h '< '(< 0 eps)))))
                        (ass))))
           (dk-opened (lambda () (di))))))))
(qed 'rkt-embed-seq-cauchy)
(topic! 'rkt-embed-seq-cauchy 'analysis)
(alias! 'rkt-embed-seq-cauchy "the constant sequence at a point is Cauchy")

(sp (make-wff '(FORALL M (FORALL u
   (IMPLIES (IS-METRIC-SPACE M) (IMPLIES (IN u (PTS M))
     (IN (EMBED-SEQ M u) (CSEQ M))))))))
(dk-peel!)
(mac 'CSEQ)
(for-each (lambda (rkt-leaf)
            (dk-focus! rkt-leaf)
            (if (eq? (car (dk-goal)) 'IN)
                (begin (fact 'rkt-embed-seq-in-fun 'M 'u) (ass))
                (begin (fact 'rkt-embed-seq-cauchy 'M 'u) (ass))))
          (dk-opened (lambda () (sep-mi))))
(qed 'rkt-embed-seq-in-cseq)
(topic! 'rkt-embed-seq-in-cseq 'analysis)

;;; (A4) THE LEAF -------------------------------------------------------
(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
     (IN (EMBED M) (FUN (PTS M) (PTS (COMPLETION M))))))))
(dk-peel!)
(rkt-pts-in-set! 'M)                    ; dk-lam-t! closes the domain-sethood leaf by `ass'
(mac 'rkt-completion-pts)
(mac 'EMBED)
(dk-lam-t!)
(di)
(let ((rkt-v (caddr (caddr (cadr (dk-goal))))))   ; CLASS(s, EMBED-SEQ(M,v)) -> v
  (fact 'rkt-class-is-set 'M (list 'EMBED-SEQ 'M rkt-v))   ; definedness, for `rfl'
  (mac 'QUOTIENT) (mac 'PROJ) (mac 'rkt-cauchy-setoid-pts)
  (mac 'image-membership-iff)
  (ew (list 'EMBED-SEQ 'M rkt-v))
  (for-each
   (lambda (rkt-leaf)
     (dk-focus! rkt-leaf)
     (if (eq? (car (dk-goal)) 'IN)
         (begin (fact 'rkt-embed-seq-in-cseq 'M rkt-v) (ass))
         (begin (lam-b) (rfl))))
   (dk-opened (lambda () (di)))))
(qed 'embed-in-fun)
(topic! 'embed-in-fun 'constructions)
(gloss! 'embed-in-fun
  "The canonical embedding of a metric space in its completion is a total map
   into the completion's carrier: the constant sequence at a point is Cauchy,
   and its class is a member of the quotient.")

;;; =====================================================================
