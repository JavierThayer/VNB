;;; rake-tb-leaves.scm -- the totally-bounded / pigeonhole leaves of the
;;; Cauchy-subsequence and separability arcs.  Two theorems, both modulo 0:
;;;
;;;   cover-block-step             the support, statement unchanged
;;;                                (theorem-library/block-family-combinatorial.scm:64)
;;;   dist-le-implies-in-carrier   NEW: a point at a measurable distance from
;;;                                anything is a point of the space
;;;
;;; LOAD WINDOW [theorem-library/nn-infinite, theorem-library/block-family-
;;; combinatorial-proof).  lo is forced by `inf-subsets-unfold' (nn-infinite,
;;; load.scm:1219), the LATEST citation; `pigeonhole-infinite'
;;; (rake-combinatorics2, load.scm:1216) is one slot above it and every other
;;; citation is far below -- subset-lemmas (827), fun-apply-type-proof (642),
;;; equality-basics (587), block-family-combinatorial (351, for the
;;; IS-FINITE-COVER definition), structure-library/inf-subsets (342),
;;; structure-library/metric-space (122), theorem-library/axioms (107) and
;;; library.scm.  hi is block-family-combinatorial-proof (load.scm:1353), the
;;; only file that cites cover-block-step in a proof.  No late tactic is used
;;; (`prop' and the dk- kit only; no contra / prep / ineq-supply).
;;;
;;; INTEGRATOR: retire the support at theorem-library/block-family-
;;; combinatorial.scm:64 (the `support' + its `warrant!' at :81); the `gloss!'
;;; at :114 and the topic! entries may stay.
;;;
;;; ---------------------------------------------------------------------
;;; THE DEFINITION DEFECT FOUND HERE, AND WHAT WAS DONE ABOUT IT
;;; ---------------------------------------------------------------------
;;; tb-rad-ball-cover and tb-scale-dense-seq were attempted here on 2026-09-19
;;; and found UNDERDETERMINED AS STATED.  The defect was not in either
;;; statement: it was in their common hypothesis, the def-predicate
;;;
;;;   TOTALLY-BOUNDED(s)  (structure-library/metric-topology.scm)
;;;     = IS-METRIC-SPACE(s) and for every r > 0,
;;;         FORSOME F. (IN (CARD F) NN) and IS-R-NET(s, F, PTS(s), r)
;;;
;;; which never said the net F was a SET.  Every CARD axiom in
;;; structure-library/cardinality.scm is guarded on (IN A SET) -- card-in-ord,
;;; card-insert, card-finite-bij, card-union-disjoint -- and so are the proven
;;; consequences (card-subset-nn, card-image-finite).  So for a PROPER CLASS F,
;;; `(IN (CARD F) NN)' was entirely unconstrained: nothing in the theory forbids
;;; a model in which CARD of the universal class is 3.
;;;
;;; THE COUNTEREXAMPLE.  Take s an UNCOUNTABLE DISCRETE metric space (d = 1
;;; between distinct points) in such a model, and F := the universal class.
;;; IS-R-NET(s, F, PTS(s), r) held for every r > 0 (every p is at distance 0
;;; from itself and p in F), and (IN (CARD F) NN) held by assumption, so
;;; TOTALLY-BOUNDED(s) held.  But at rad = 1/2 every BALL(s,c,1/2) is the
;;; singleton {c}, so both leaves' conclusions FAILED.
;;;
;;; THE REPAIR (the user's decision, 2026-09-19) is one conjunct on IS-R-NET,
;;; not on TOTALLY-BOUNDED: `(SUBSET F A)'.  At A = PTS(s) that makes the net a
;;; subclass of the carrier, hence a SET by subclass-of-set-is-set, which is
;;; what `(IN (CARD F) NN)' needed all along.  The definition site records the
;;; decision and the counter-model; the only prover of an r-net,
;;; calculus/finite-ball-subcover-proof.scm, carries the new conjunct free (its
;;; net is CENTRE-SET(s,r,F), whose members chosen-centre-is-centre places in
;;; PTS(s)).  With the repair in place BOTH leaves are PROVEN modulo 0, in
;;; theorem-library/rake-tb-leaves-2.scm.
;;;
;;; The OTHER obstacle those two leaves name -- "the net can be taken INSIDE
;;; the carrier", which the old TOTALLY-BOUNDED and IS-R-NET did not state --
;;; is PROVEN here as `dist-le-implies-in-carrier'.  That half was never a gap
;;; in the mathematics, only in the statement.
;;;
;;; ---------------------------------------------------------------------
;;; Leaf 1 (this file): cover-block-step
;;;   theorem-library/block-family-combinatorial.scm:64 (support + warrant!).
;;;   Stated LITERALLY, copied from that site.
;;;
;;;   Within any infinite index block J subset NN, a FINITE COVER C of V pins
;;;   an infinite sub-block J_ subset J into a single member U of C.  The
;;;   metric-free single pigeonhole step block-family-combinatorial iterates.
;;;
;;;   THE CONSTRUCTION, exactly as the warrant describes it:
;;;
;;;     pi   := (VNB-LAMBDA i_ J. CHOICE { uu in C : f(i_) in uu })
;;;     J_   := { x in J : pi(x) = cc }, cc the member pigeonhole-infinite
;;;             returns with an infinite fibre.
;;;
;;;   pi is a genuine element of FUN(J,C) because the separated set is
;;;   INHABITED at every i_ in J: f(i_) in V (f in FUN(NN,V), i_ in J subset
;;;   NN) and V subset BIG-UNION(C), so `bu-me' produces a member of C that
;;;   contains f(i_).  choice-axiom then puts CHOICE of that set inside it,
;;;   which is BOTH halves of what the proof wants: pi(i_) in C (the typing)
;;;   and f(i_) in pi(i_) (the capture).
;;;
;;;   EMPTY CASES.  V = EMPTY-SET is not a defect here: FUN(NN, EMPTY-SET) is
;;;   empty, so the hypothesis (IN f (FUN NN V)) is unsatisfiable and the
;;;   statement is vacuously true; the proof never needs a point of V.  C
;;;   empty is likewise harmless -- it forces V empty, hence the same lane.
;;;   No inhabitedness guard is wanted and none is added.
;;;
;;; Helper prefix: rtb-.

;;; ---- file-local driver helpers ----------------------------------------

(define (rtb-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-tb-leaves: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (wff-formula (sequent-node-assertion l))))
                    (newline)
                    (for-each (lambda (w)
                                (display "      | ")
                                (display (expression->string (wff-formula w)))
                                (newline))
                              (sequent-node-assumptions l)))
                  (proof-open-goals *ps*))
        (error "rake-tb-leaves: unfinished" name))))

;; close every leaf a branching tactic opened, by `ass'
(define (rtb-close-opened! thunk)
  (for-each (lambda (l) (dk-focus! l) (ass)) (dk-opened thunk)))

(define (rtb-head? h) (lambda (fm) (and (pair? fm) (eq? (car fm) h))))

;;; =====================================================================
;;; cover-block-step -- THE SUPPORT, stated literally
;;; (theorem-library/block-family-combinatorial.scm:64).
;;; =====================================================================

(sp (make-wff
  '(FORALL V
     (IMPLIES (IN V SET)
       (FORALL f
         (IMPLIES (IN f (FUN NN V))
           (FORALL C
             (IMPLIES (IS-FINITE-COVER C V)
               (FORALL J
                 (IMPLIES (IN J (INF-SUBSETS NN))
                   (FORSOME J_
                     (AND (IN J_ (INF-SUBSETS NN))
                     (AND (SUBSET J_ J)
                          (FORSOME U
                            (AND (IN U C)
                                 (FORALL i
                                   (IMPLIES (IN i J_)
                                     (IN (f i) U))))))))))))))))))

(define rtb-c-landed (dk-peel!))

(define rtb-c-V
  (cadr (dk-pick (lambda (fm) (and ((rtb-head? 'IN) fm) (eq? (caddr fm) 'SET)))
                 "the carrier V")))
(define rtb-c-f
  (cadr (dk-pick (lambda (fm) (and ((rtb-head? 'IN) fm)
                                   (pair? (caddr fm)) (eq? (car (caddr fm)) 'FUN)))
                 "the sequence f")))
(define rtb-c-C
  (cadr (dk-pick (rtb-head? 'IS-FINITE-COVER) "the finite cover C")))
(define rtb-c-J
  (cadr (dk-pick (lambda (fm) (and ((rtb-head? 'IN) fm)
                                   (pair? (caddr fm))
                                   (eq? (car (caddr fm)) 'INF-SUBSETS)))
                 "the index block J")))

;;; ---- unfold the finite cover: C in SET, CARD C in NN, V subset union C ----
(dk-split-all!
 (dk-landed (lambda () (mac-h 'IS-FINITE-COVER (list 'IS-FINITE-COVER rtb-c-C rtb-c-V)))))

(define rtb-c-cov (dk-pick (rtb-head? 'SUBSET) "the coverage inclusion"))
(define rtb-c-BU (caddr rtb-c-cov))

;;; ---- unfold the block: J in SET, J elementwise in NN, J infinite ---------
(define rtb-c-Jsep
  (dk-landed-1 (lambda () (mac-h 'inf-subsets-unfold
                                 (list 'IN rtb-c-J '(INF-SUBSETS NN))))))
(dk-landed (lambda () (sep-me rtb-c-Jsep)))
(define rtb-c-Jinf
  (dk-pick (lambda (fm) (and ((rtb-head? 'NOT) fm)
                             ((rtb-head? 'IN) (cadr fm))
                             ((rtb-head? 'CARD) (cadr (cadr fm)))))
           "the infinitude of J"))
(dk-split-all!
 (dk-landed (lambda () (mac-h 'power-set-membership
                              (list 'IN rtb-c-J '(POWER NN))))))
(define rtb-c-Jset (list 'IN rtb-c-J 'SET))
(define rtb-c-JinNN
  (dk-pick (lambda (fm) (and ((rtb-head? 'FORALL) fm)
                             (dk-contains? fm rtb-c-J)))
           "the elementwise NN typing of J"))

;;; ---- the classifier ------------------------------------------------------

(define (rtb-c-sep i) (list 'SEP 'uu rtb-c-C (list 'IN (list rtb-c-f i) 'uu)))
(define (rtb-c-val i) (list 'CHOICE (rtb-c-sep i)))
(define rtb-c-pi (list 'VNB-LAMBDA 'i_ rtb-c-J (rtb-c-val 'i_)))

;; With (IN i J) in the context, land BOTH halves of the classifier's value:
;;   (IN (CHOICE {uu in C : f(i) in uu}) C)      -- pi(i) is a member of C
;;   (IN (f i) (CHOICE {uu in C : f(i) in uu}))  -- and it contains f(i).
(define (rtb-c-choose! i)
  (dk-apply! rtb-c-JinNN i)                                   ; (IN i NN)
  (fact 'fun-apply-type-c rtb-c-f 'NN rtb-c-V i)              ; (IN (f i) V)
  (fact 'subset-mem-fwd rtb-c-V rtb-c-BU (list rtb-c-f i))    ; (IN (f i) union C)
  (let* ((new (dk-landed (lambda () (bu-me (list 'IN (list rtb-c-f i) rtb-c-BU)))))
         (wit (cadr (or (any-pred (lambda (fm) (and ((rtb-head? 'IN) fm)
                                                    (eq? (caddr fm) rtb-c-C)))
                                  new)
                        (error "rtb-c-choose!: bu-me landed no member of C"
                               (map expression->string new))))))
    (choose! (rtb-c-sep i) wit
             (lambda () (rtb-close-opened! (lambda () (sep-mi)))))))

;;; ---- pi : J -> C ---------------------------------------------------------

(have! (list 'IN rtb-c-pi (list 'FUN rtb-c-J rtb-c-C))
  (lambda ()
    (for-each
     (lambda (l)
       (dk-focus! l)
       (let ((g (dk-goal)))
         (if (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET))
             (ass)                                   ; (IN J SET), already known
             (let ((iv (dk-di-var!)))
               (rtb-c-choose! iv)
               (ass)))))
     (dk-opened (lambda () (lam-t))))))

;;; ---- the infinite pigeonhole --------------------------------------------

(have! (list 'AND rtb-c-Jset rtb-c-Jinf))
(have! (list 'AND (list 'IN rtb-c-C 'SET) (list 'IN (list 'CARD rtb-c-C) 'NN)))

(define rtb-c-ex (dk-fact! 'pigeonhole-infinite rtb-c-J rtb-c-C rtb-c-pi))
(define rtb-c-cc (dk-skolem! rtb-c-ex))
(define rtb-c-fibf
  (dk-pick (lambda (fm) (and ((rtb-head? 'NOT) fm)
                             ((rtb-head? 'IN) (cadr fm))
                             ((rtb-head? 'CARD) (cadr (cadr fm)))
                             ((rtb-head? 'SEP) (cadr (cadr (cadr fm))))))
           "the infinite fibre"))
(define rtb-c-FIB (cadr (cadr (cadr rtb-c-fibf))))

;;; ---- exhibit J_ := the fibre --------------------------------------------

(ew rtb-c-FIB)

;; peel one element out of the fibre: `di' the guarded universal, read the
;; eigenvariable off the landed (IN z FIB), split that membership into
;; (IN z J) and (= (pi z) cc), and return the pair (z . landed-formulas).
(define (rtb-c-open-fibre!)
  (let* ((memb (dk-landed-1 (lambda () (di))))
         (zv   (cadr memb))
         (new  (dk-landed (lambda () (sep-me memb)))))
    (cons zv new)))

(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond

       ;; ---- (IN FIB (INF-SUBSETS NN)) ---------------------------------
       ((and ((rtb-head? 'IN) g) (pair? (caddr g))
             (eq? (car (caddr g)) 'INF-SUBSETS))
        (mac 'INF-SUBSETS)
        (for-each
         (lambda (l)
           (dk-focus! l)
           (if ((rtb-head? 'NOT) (dk-goal))
               (ass)                                    ; FIB is infinite
               (begin                                   ; (IN FIB (POWER NN))
                 (mac 'power-set-membership)
                 (for-each
                  (lambda (m)
                    (dk-focus! m)
                    (if ((rtb-head? 'FORALL) (dk-goal))
                        (let ((p (rtb-c-open-fibre!)))  ; z in FIB
                          (dk-apply! rtb-c-JinNN (car p))
                          (ass))
                        (begin (sep-set) (ass))))       ; (IN FIB SET)
                  (dk-opened (lambda () (di)))))))
         (dk-opened (lambda () (sep-mi)))))

       ;; ---- (SUBSET FIB J) --------------------------------------------
       (((rtb-head? 'SUBSET) g)
        (mac 'subset-def)
        (rtb-c-open-fibre!)
        (ass))

       ;; ---- (FORSOME U. U in C and f(i) in U for every i in FIB) -------
       (((rtb-head? 'FORSOME) g)
        (ew rtb-c-cc)
        (dk-conj-close!
         (lambda ()
           (if ((rtb-head? 'FORALL) (dk-goal))
               (let* ((p   (rtb-c-open-fibre!))         ; i in FIB
                      (iv  (car p))
                      (eqf (or (any-pred (rtb-head? '=) (cdr p))
                               (error "cover-block-step: no fibre equation"
                                      (map expression->string (cdr p))))))
                 (rtb-c-choose! iv)
                 ;; (= ((VNB-LAMBDA i_ J ...) i) cc)  ->  (= (CHOICE ...) cc)
                 (let* ((red (or (any-pred (rtb-head? '=)
                                           (dk-landed (lambda () (lam-b-h eqf))))
                                 (error "cover-block-step: lam-b-h landed no equation")))
                        (lhs (cadr red)) (rhs (caddr red)))
                   (fact 'eq-sym lhs rhs)               ; (= cc (CHOICE ...))
                   (subst (list '= rhs lhs))
                   (ass)))
               (ass)))))

       (#t (ass))))))

(rtb-qed! 'cover-block-step)
(topic! 'cover-block-step 'combinatorial)

;;; =====================================================================
;;; dist-le-implies-in-carrier -- a point at a MEASURABLE distance from
;;; anything is a point of the space.
;;;
;;;     IS-METRIC-SPACE(s),  d(s)(c,p) <= r   =>   c in PTS(s)
;;;
;;; This is conversion (a) of tb-scale-dense-seq's warrant
;;; (structure-library/separable.scm:60) and the step clause (ii) of
;;; tb-rad-ball-cover needs: "a member that serves any point at all lies in
;;; PTS(s), since DIST(s) is a function on PTS(s) x PTS(s)".  (The warrant's
;;; surrounding claim -- that this makes the whole net a subset of PTS(s) --
;;; is FALSE, and is the defect recorded in the header; since 2026-09-19
;;; IS-R-NET states the inclusion outright.)  The warrant calls the step
;;; bookkeeping; it is in fact the one
;;; place in the metric library where the LUTINS definedness rule does
;;; mathematical work, and no lemma of the shape "x <= y implies x in RR"
;;; exists (every order axiom in number-systems.scm is guarded the other way).
;;;
;;; THE ROUTE, and the one move in it that is not obvious.  `<=' is an
;;; uninterpreted predicate, so the hypothesis gives no typing; what it gives
;;; is DEFINEDNESS.  pi--strict-hyp-certifies? certifies a term occurring
;;; outside binders in a true IN / = / <= / < hypothesis, so `rfl' alone proves
;;;
;;;     d(s)(c,p) = d(s)(c,p)
;;;
;;; -- the definedness predicate of VNB's partial equality.  From there the
;;; chain is apply-tupling-2 (to the tupled application DIST(s) eats),
;;; fun-codomain-iff + fun-domain-apply-def (a member of FUN(A) is defined
;;; EXACTLY on A), and the kernel rule `ce'.
;;;
;;; NOTHING IS EVER INSTANTIATED AT THE TUPLED APPLICATION.  pi--defined?
;;; refuses an untyped application, so `fact' at DIST(s)([c,p]) would post the
;;; owed leaf (= DIST(s)([c,p]) DIST(s)([c,p])) -- which is the very claim being
;;; established, and the lane closes on itself.  The definedness is therefore
;;; carried on the LEFT OF AN IMPLICATION, where `subst' may rewrite it by the
;;; quasi-equation and `di' then lands it as a HYPOTHESIS.  That shape is the
;;; transferable part of this proof.
;;; =====================================================================

(sp (make-wff
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL cc_
         (FORALL pp_
           (FORALL rr_
             (IMPLIES (<= ((DIST s) cc_ pp_) rr_)
               (IN cc_ (PTS s))))))))))

(dk-peel!)

;; (1) the `<=' hypothesis alone certifies the distance DEFINED
(have! '(= ((DIST s) cc_ pp_) ((DIST s) cc_ pp_)) (lambda () (rfl)))

;; (2) the DIST typing conjunct -- unconditional in the IS-METRIC-SPACE iff --
;;     and its FUN(A) half
(mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s))
(dk-split-all!)
(dk-split-all!
 (dk-landed (lambda () (mac-h 'fun-codomain-iff
                              '(IN (DIST s) (FUN (CARTESIAN (PTS s) (PTS s)) RR))))))

;; (3) the tupling bridge, as a quasi-equation in the context
(fact 'apply-tupling-2 '(DIST s) 'cc_ 'pp_)

;; (4) "defined => in the carrier", with the definedness on the LEFT
(define rtb-d-cart '(CARTESIAN (PTS s) (PTS s)))
(define rtb-d-pair '(LIST cc_ pp_))
(define rtb-d-imp
  '(IMPLIES (= ((DIST s) cc_ pp_) ((DIST s) cc_ pp_)) (IN cc_ (PTS s))))

(have! rtb-d-imp
  (lambda ()
    (subst '(== ((DIST s) cc_ pp_) ((DIST s) (LIST cc_ pp_))))
    (let* ((defd (dk-landed-1 (lambda () (di))))
           (iff  (dk-fact! 'fun-domain-apply-def rtb-d-cart '(DIST s) rtb-d-pair)))
      (have! (list 'IN rtb-d-pair rtb-d-cart)
             (lambda () (dk-only! iff defd) (prop)))
      (ce (list 'IN rtb-d-pair rtb-d-cart) 1)
      (ass))))

(dk-apply! rtb-d-imp)
(ass)

(rtb-qed! 'dist-le-implies-in-carrier)
(gloss! 'dist-le-implies-in-carrier
  "If the distance from c to p in the metric space s satisfies any inequality
   d(s)(c,p) <= r, then c is a point of s.  DIST(s) is a function on
   PTS(s) x PTS(s), so a true inequality about d(s)(c,p) makes that term
   denote, which puts the pair in DIST(s)'s domain.  The fact that lets an
   r-net be restricted to the carrier.")
(topic! 'dist-le-implies-in-carrier 'topology)
