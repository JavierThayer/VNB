;;; theorem-library/finsum-type-proof.scm -- the FINSUM typing floor, PROVEN.
;;;
;;;     group-carrier-closed-opr   (NEW)  (OPR s)(a,b) in CARR(s) for a group s
;;;     sum-ag-type-ind            (NEW)  sum-ag-type with the induction variable OUTERMOST
;;;     sum-ag-type                       formerly an UNWARRANTED axiom (structure-library/sequences.scm)
;;;     enum-fam-in-fun                   formerly an `informal' support (theorem-library/enum-fam-in-fun.scm)
;;;     finsum-type                       formerly an `informal' support (theorem-library/finsum-type.scm)
;;;     sum-ag-all-id-ind          (NEW)  the induction form of finsum-all-id
;;;     finsum-all-id                     formerly a `well-known' support (theorem-library/finsum-additive.scm)
;;;
;;; WHY sum-ag-type FIRST.  finsum-type is one `bc*' away from sum-ag-type, and
;;; sum-ag-type was installed by `theory-add-axiom!' with no `warrant!' at all --
;;; i.e. `trust: none', the weakest tier there is -- so proving finsum-type on top of
;;; it would have bought nothing.  Its own proof is the induction sequences.scm's
;;; comment has described since the file was written and nobody ran.
;;;
;;; THE INDUCTION VARIABLE HAS TO COME FIRST, and that is why sum-ag-type-ind exists.
;;; `ni' tests the goal's SHAPE -- literally (FORALL n (IMPLIES (IN n NN) body)) at the
;;; top -- while sum-ag-type is stated with ag and f outermost, and `di' is GREEDY: one
;;; call takes the whole leading FORALL/IMPLIES prefix, n included.  So there is no way
;;; to peel down to the n-universal and then induct.  sum-ag-type-ind states the same
;;; fact with n outermost, is proved by `ni', and sum-ag-type is then one `fact' of it.
;;; (Same shape as sum-ag-segment-congruence in finsum-insert.scm.)
;;;
;;; THE STEP NEEDS OPR CLOSURE, WHICH DID NOT EXIST FOR A GROUP.  sum-ag-succ turns
;;; SUM-AG(ag,f,succ n) into (OPR ag)(SUM-AG(ag,f,n), f n), and closing that in the
;;; carrier wants "(OPR s) maps CARR x CARR into CARR" in APPLIED form.  The tree had
;;; that for a RING (ring-add-closed, ring-carrier-closed-mul, ... -- theorem-library/
;;; op-typing.scm) and for a MONOID only as `monoid-carrier-closed-opr', an axiom with
;;; NO warrant.  `group-carrier-closed-opr' is the group's, proved by op-typing's own
;;; driver: unfold IS-GROUP, take the (op OPR (CARTESIAN CARR CARR) CARR) conjunct,
;;; bridge the TUPLING with apply-tupling-2 (a `==', which `subst' takes), then
;;; pair-in-cartesian + fun-apply-type-c.  The driver is re-stated here rather than
;;; borrowed: `ot-prove!' is file-local to op-typing.scm, as CLAUDE.md requires.
;;;
;;; FINSUM-ALL-ID GOES THE SAME WAY, and NOT the way its warrant proposed.  That warrant
;;; says "induction on |S| via finsum-insert" -- an induction over finite SETS, for which
;;; the tree has no principle.  FINSUM is DEFINED as a SUM-AG over an enumeration, so the
;;; induction that IS available -- `ni' on the fold length -- does the whole job
;;; (sum-ag-all-id-ind), and the peeled summand comes out of the agreement hypothesis at
;;; the index n instead of out of an insertion lemma.  No enumeration-independence is
;;; needed either, so the bill is `modulo 0' where finsum-insert-ag's is not.
;;;
;;; BILL (probe on the band): ALL SEVEN `proven modulo 0'.
;;;
;;; CITATIONS, with the file that installs each:
;;;   structure-library/group (definitional):        is-group   (the IS-GROUP iff)
;;;   structure-library/bijection (definitional):    bijection-membership-iff
;;;   structure-library/sequences (definitional):    sum-ag-zero, sum-ag-succ
;;;   structure-library/finsum (functoid unfold):    FINSUM
;;;   theorem-library/axioms (primitive):            apply-tupling-2
;;;   theorem-library/fun-apply-type-proof:          fun-apply-type-c        (proven)
;;;   theorem-library/pair-tuple-sethood:            pair-in-cartesian       (proven)
;;;   theorem-library/finsum-insert:                 fin-enum-is-bijection   (proven)
;;;   structure-library/subtype-laws:                abelian-group-is-group,
;;;                                                  group-identity-in       (proven)
;;;   theorem-library/ord-segment-nn-succ-proof:     ord-segment-nn-succ     (proven)
;;;   theorem-library/ord-segment-nn-subset-proof:   ord-segment-nn-subset   (proven)
;;;   number-systems (primitive):                   nn-is-set
;;;   structure-library/finsum (functoid unfolds):   ENUM-FAM, FIN-ENUM
;;;
;;; RETIRES (the integrator removes these; this file does not touch them):
;;;   structure-library/sequences.scm:115   (theory-add-axiom! ... 'sum-ag-type ...)  -- no warrant!
;;;   theorem-library/finsum-type.scm:9,15  (support / warrant!) -- the whole file, load.scm:417
;;;   theorem-library/enum-fam-in-fun.scm:9,16 (support / warrant!) -- the whole file, load.scm:411
;;;   theorem-library/finsum-additive.scm:214,221  (support / warrant! 'finsum-all-id)
;;;   theorem-library/founder-warrants.scm:35,111  duplicate warrant! for finsum-type and
;;;       enum-fam-in-fun (that file only re-warrants; it cites nothing)
;;;
;;; LOAD WINDOW, by FILE NAME:
;;;   lo -- after structure-library/subtype-laws and theorem-library/op-typing (the
;;;         latest files cited; subtype-laws is what supplies abelian-group-is-group
;;;         and group-identity-in).  op-typing is not cited, but this file sits beside
;;;         it: same driver, same reason for the position.
;;;   hi -- BEFORE theorem-library/cancellation.  That file runs the UNRESTRICTED
;;;         (view-as-auto-specialize! 'RING-ADDITIVE-AG), which is what builds
;;;         `finsum-type-ring-additive-ag' -- cited by name in
;;;         theorem-library/mat-typing-bundle.  A proven theorem installed AFTER that
;;;         call is invisible to it and the companion silently disappears (CLAUDE.md,
;;;         "Proving a fact that used to be an axiom moves it past the view
;;;         specializer").  So: between op-typing and cancellation.
;;;
;;; Helper prefix: ftp-.

;;; ---------------------------------------------------------------------------
;;; helpers

(define (ftp-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; ftp: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "ftp: proof not complete" name))))

;; Among LEAVES (as dk-opened returns them), the unique one whose GOAL satisfies PRED.
(define (ftp-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "ftp-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "ftp-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

(define (ftp-pick-head head what) (dk-pick (dk-head? head) what))

;; the NN-typed eigenvariable in context: (IN v NN) with v a symbol.
(define (ftp-nn-var)
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                  (eq? (caddr f) 'NN)))
                 "n in NN")))

;;; ---------------------------------------------------------------------------
;;; group-carrier-closed-opr:  IS-GROUP(s), a,b in CARR(s)  =>  (OPR s)(a,b) in CARR(s).
;;;
;;; op-typing.scm's driver, for the group's OPR.  The gap between the IS-GROUP
;;; op-clause -- (IN (OPR s) (FUN (CARTESIAN (CARR s) (CARR s)) (CARR s))) -- and the
;;; applied form is the TUPLING: a structure operation eats one pair, the parser emits
;;; the curried (f a b).

(sp (make-wff
     '(FORALL s (IMPLIES (IS-GROUP s)
        (FORALL a (IMPLIES (IN a (CARR s))
        (FORALL b (IMPLIES (IN b (CARR s))
          (IN ((OPR s) a b) (CARR s))))))))))
(dk-peel!)
(mac-h 'is-group '(IS-GROUP s))
(dk-split-all!)
(fact 'apply-tupling-2 '(OPR s) 'a 'b)
(subst '(== ((OPR s) a b) ((OPR s) (LIST a b))))      ; == rewrites as = does
(fact 'pair-in-cartesian '(CARR s) '(CARR s) 'a 'b)
(fact 'fun-apply-type-c '(OPR s) '(CARTESIAN (CARR s) (CARR s)) '(CARR s) '(LIST a b))
(ass)
(ftp-check! 'group-carrier-closed-opr)
(qed 'group-carrier-closed-opr)
(topic! 'group-carrier-closed-opr 'algebra)

;;; ---------------------------------------------------------------------------
;;; sum-ag-type-ind:  the induction form of sum-ag-type -- n OUTERMOST.
;;;
;;;   n in NN => forall ag. IS-ABELIAN-GROUP ag => forall f in FUN(NN, CARR ag).
;;;                SUM-AG(ag,f,n) in CARR(ag)
;;;
;;; base: SUM-AG(ag,f,0) = IDEN(ag)          (sum-ag-zero), in the carrier by
;;;       group-identity-in through abelian-group-is-group.
;;; step: SUM-AG(ag,f,succ n) = (OPR ag)(SUM-AG(ag,f,n), f n)   (sum-ag-succ); the left
;;;       factor is the IH, the right is fun-apply-type-c on f, and the product is in
;;;       the carrier by group-carrier-closed-opr.

(define ftp-ind-stmt
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL f (IMPLIES (IN f (FUN NN (CARR ag)))
       (IN (SUM-AG ag f n) (CARR ag)))))))))

(sp (make-wff ftp-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (ftp-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (ftp-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base: the empty sum is the identity -------------------------------
  (dk-focus! base)
  (dk-peel!)
  (let ((agv (cadr (ftp-pick-head 'IS-ABELIAN-GROUP "IS-ABELIAN-GROUP ag"))))
    (mac 'sum-ag-zero)                                  ; goal (IN (IDEN ag) (CARR ag))
    (dk-fact! 'abelian-group-is-group agv)
    (dk-fact! 'group-identity-in agv)
    (ass))
  ;; ---- step --------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)                                            ; n, the IH, ag, IS-AG, f, FUN
  (let* ((nv  (ftp-nn-var))
         (gl  (dk-goal))                                ; (IN (SUM-AG ag f (succ n)) (CARR ag))
         (agv (cadr (cadr gl)))
         (fv  (caddr (cadr gl)))
         (ih  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL))) "the IH")))
    (mac 'sum-ag-succ)                                  ; (IN ((OPR ag) (SUM-AG ag f n) (f n)) ...)
    (dk-apply! ih agv fv)                               ; (IN (SUM-AG ag f n) (CARR ag))
    (dk-fact! 'fun-apply-type-c fv 'NN (list 'CARR agv) nv)   ; (IN (f n) (CARR ag))
    (dk-fact! 'abelian-group-is-group agv)
    (dk-fact! 'group-carrier-closed-opr agv (list 'SUM-AG agv fv nv) (list fv nv))
    (ass)))
(ftp-check! 'sum-ag-type-ind)
(qed 'sum-ag-type-ind)
(topic! 'sum-ag-type-ind 'algebra)

;;; ---------------------------------------------------------------------------
;;; sum-ag-type -- the statement as structure-library/sequences.scm spells it.

(sp (make-wff
     '(FORALL ag
        (IMPLIES (IS-ABELIAN-GROUP ag)
                 (FORALL f
                   (IMPLIES (IN f (FUN NN (CARR ag)))
                            (FORALL n
                              (IMPLIES (IN n NN)
                                       (IN (SUM-AG ag f n) (CARR ag))))))))))
(dk-peel!)
(let* ((nv  (ftp-nn-var))
       (gl  (dk-goal))
       (agv (cadr (cadr gl)))
       (fv  (caddr (cadr gl))))
  (dk-fact! 'sum-ag-type-ind nv agv fv)
  (ass))
(ftp-check! 'sum-ag-type)
(qed 'sum-ag-type)
(topic! 'sum-ag-type 'algebra)

;;; ---------------------------------------------------------------------------
;;; enum-fam-in-fun:  ENUM-FAM(ag,f,phi,n) is a TOTAL function NN -> CARR(ag).
;;;
;;; The last asserted leaf under finsum-type, and the reason this file proves it too:
;;; with sum-ag-type proven, finsum-type's whole bill was {enum-fam-in-fun}.
;;;
;;; ENUM-FAM's IF guard fills the indices OUTSIDE ORD-SEGMENT(n) with IDEN(ag), which is
;;; what makes the family total even though phi is only defined on the segment.  So:
;;; unfold, `lam-t' (which opens the pointwise typing AND the sethood of the lambda's
;;; domain NN -- two leaves, not one), then an excluded-middle split on the guard.  In
;;; the then-branch phi(i) lands in S and f of it in CARR(ag), two fun-apply-type-c
;;; citations; in the else-branch the value IS the identity, in the carrier by
;;; group-identity-in.  The archived script (archive/proven-theorems-archive.scm:1984)
;;; is the same argument spelled out over ~120 lines of hand-built excluded middle and
;;; `inst' chains, against `fun-apply-type' with its AND antecedent.

(sp (make-wff
     '(FORALL n (IMPLIES (IN n NN)
        (FORALL ag (IMPLIES (IS-GROUP ag)
        (FORALL S (FORALL phi (IMPLIES (IN phi (FUN (ORD-SEGMENT n) S))
        (FORALL f (IMPLIES (IN f (FUN S (CARR ag)))
          (IN (ENUM-FAM ag f phi n) (FUN NN (CARR ag))))))))))))))
(dk-peel!)
(let* ((nv    (ftp-nn-var))
       (agv   (cadr (ftp-pick-head 'IS-GROUP "IS-GROUP ag")))
       (phi-h (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                        (pair? (caddr a)) (eq? (car (caddr a)) 'FUN)
                                        (pair? (cadr (caddr a)))
                                        (eq? (car (cadr (caddr a))) 'ORD-SEGMENT)))
                       "phi in FUN(ORD-SEGMENT n, S)"))
       (phiv  (cadr phi-h))
       (sv    (caddr (caddr phi-h)))
       (fv    (cadr (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                              (pair? (caddr a)) (eq? (car (caddr a)) 'FUN)
                                              (equal? (cadr (caddr a)) sv)))
                             "f in FUN(S, CARR ag)"))))
  (mac 'ENUM-FAM)
  (let* ((ls   (dk-opened (lambda () (lam-t))))
         (setl (ftp-leaf ls (lambda (g) (equal? g '(IN NN SET))) "NN in SET"))
         (ptw  (ftp-leaf ls (lambda (g) (and (pair? g) (eq? (car g) 'FORALL))) "pointwise typing")))
    (dk-focus! setl)
    (fact 'nn-is-set)
    (ass)
    (dk-focus! ptw)
    (let* ((iv  (dk-di-var!))
           (pp  `(IN ,iv (ORD-SEGMENT ,nv)))
           (ift `(IF ,pp (,fv (,phiv ,iv)) (IDEN ,agv))))
      (use-em pp
        (lambda ()                                     ; i_ in the segment: then-branch
          (let* ((l (dk-opened (lambda () (if-true ift))))
                 (c (ftp-leaf l (lambda (g) (equal? g pp)) "if-true condition"))
                 (m (ftp-leaf l (lambda (g) (not (equal? g pp))) "if-true main")))
            (dk-focus! c) (ass)
            (dk-focus! m)
            (subst (list '= ift (list fv (list phiv iv))))
            (dk-fact! 'fun-apply-type-c phiv (list 'ORD-SEGMENT nv) sv iv)
            (dk-fact! 'fun-apply-type-c fv sv (list 'CARR agv) (list phiv iv))
            (ass)))
        (lambda ()                                     ; i_ outside: the value is IDEN(ag)
          (let* ((l (dk-opened (lambda () (if-false ift))))
                 (c (ftp-leaf l (dk-head? 'NOT) "if-false condition"))
                 (m (ftp-leaf l (lambda (g) (not ((dk-head? 'NOT) g))) "if-false main")))
            (dk-focus! c) (ass)
            (dk-focus! m)
            (subst (list '= ift (list 'IDEN agv)))
            (dk-fact! 'group-identity-in agv)
            (ass)))))))
(ftp-check! 'enum-fam-in-fun)
(qed 'enum-fam-in-fun)
(topic! 'enum-fam-in-fun 'plumbing)

;;; ---------------------------------------------------------------------------
;;; finsum-type -- the statement as theorem-library/finsum-type.scm spells it.
;;;
;;; FINSUM(ag,f,S) is DEFINED as SUM-AG(ag, ENUM-FAM(ag,f,FIN-ENUM S,|S|), |S|), so the
;;; typing is sum-ag-type applied to that family.  enum-fam-in-fun gives the family's
;;; FUN(NN, CARR ag) typing from a FUN(OS |S|, S) enumeration; FIN-ENUM S is a
;;; BIJECTION (fin-enum-is-bijection) and the FUN typing is its first conjunct.
;;;
;;; The projection is taken INLINE, by unfolding the definitional
;;; `bijection-membership-iff' on the hypothesis, rather than by citing
;;; `bijection-in-fun': that theorem is proved in structure-library/bijection-derived,
;;; which loads LONG after this file's upper bound (cancellation, see the header).
;;; The iff is definitional, so the inline unfold costs the bill nothing.

(sp (make-wff
     '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
        (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
        (FORALL f (IMPLIES (IN f (FUN S (CARR ag)))
          (IN (FINSUM ag f S) (CARR ag)))))))))))
(dk-peel!)
(let* ((agv (cadr (ftp-pick-head 'IS-ABELIAN-GROUP "IS-ABELIAN-GROUP ag")))
       (sv  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'SET)))
                           "S in SET")))
       (fv  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                            (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)
                                            (equal? (cadr (caddr f)) sv)))
                           "f in FUN(S, CARR ag)")))
       (fam (list 'ENUM-FAM agv fv (list 'FIN-ENUM sv) (list 'CARD sv))))
  (mac 'FINSUM)
  (dk-fact! 'abelian-group-is-group agv)
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (dk-fact! 'enum-fam-in-fun (list 'CARD sv) agv sv (list 'FIN-ENUM sv) fv)
  (dk-fact! 'sum-ag-type agv fam (list 'CARD sv))
  (ass))
(ftp-check! 'finsum-type)
(qed 'finsum-type)
(topic! 'finsum-type 'plumbing)

;;; ---------------------------------------------------------------------------
;;; sum-ag-all-id-ind:  a fold of identities is the identity.
;;;
;;;   n in NN => forall ag. IS-ABELIAN-GROUP ag => forall g_.
;;;                (forall i_ in ORD-SEGMENT n. g_(i_) = IDEN ag)
;;;                => SUM-AG(ag, g_, n) = IDEN ag
;;;
;;; The induction form of finsum-all-id.  The warrant retired below proposed an
;;; induction on |S| via finsum-insert; that route needs a finite-SET induction
;;; principle, which the tree does not have.  FINSUM is DEFINED as a SUM-AG, so the
;;; induction that is available -- `ni' on the fold length -- does the whole job, and
;;; the peeled summand comes out of the agreement hypothesis at the index n rather
;;; than out of an insertion lemma.  Base: sum-ag-zero, the empty fold IS the seed.
;;; Step: sum-ag-succ, then the top summand is IDEN by the hypothesis at n, the rest
;;; is IDEN by the IH, and IDEN*IDEN = IDEN by group-left-id.
;;;
;;; NOTE the `rfl' at the base: `=' is the DEFINEDNESS predicate, so (IDEN ag) = (IDEN ag)
;;; is closable only with a context witness that (IDEN ag) denotes -- pi-reflexivity!
;;; looks for exactly that (`asm-establishes-defined?').  group-identity-in supplies it.

(define ftp-allid-stmt
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL g_ (IMPLIES (FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n)) (= (g_ i_) (IDEN ag))))
       (= (SUM-AG ag g_ n) (IDEN ag)))))))))

;; the agreement hypothesis: the FORALL whose antecedent is an ORD-SEGMENT membership.
;; Discriminated on the ANTECEDENT, never on the head: the IH is a FORALL too.
(define (ftp-agreement? f)
  (and (pair? f) (eq? (car f) 'FORALL)
       (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
       (pair? (cadr (caddr f))) (eq? (car (cadr (caddr f))) 'IN)
       (pair? (caddr (cadr (caddr f))))
       (eq? (car (caddr (cadr (caddr f)))) 'ORD-SEGMENT)))

(sp (make-wff ftp-allid-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (ftp-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (ftp-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base: the empty fold is the seed ----------------------------------
  (dk-focus! base)
  (dk-peel!)
  (let ((agv (cadr (ftp-pick-head 'IS-ABELIAN-GROUP "IS-ABELIAN-GROUP ag"))))
    (mac 'sum-ag-zero)                                  ; goal (= (IDEN ag) (IDEN ag))
    (dk-fact! 'abelian-group-is-group agv)
    (dk-fact! 'group-identity-in agv)                   ; the definedness witness rfl wants
    (rfl))
  ;; ---- step --------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv    (ftp-nn-var))
         (gl    (dk-goal))                              ; (= (SUM-AG ag g_ (succ n)) (IDEN ag))
         (agv   (cadr (cadr gl)))
         (gv    (caddr (cadr gl)))
         (agree (dk-pick ftp-agreement? "the agreement hypothesis on OS(succ n)"))
         (ih    (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                          (not (ftp-agreement? f))))
                         "the IH")))
    (mac 'sum-ag-succ)                                  ; (= ((OPR ag) (SUM-AG ag g_ n) (g_ n)) (IDEN ag))
    (dk-fact! 'abelian-group-is-group agv)
    (dk-fact! 'group-identity-in agv)
    ;; the top summand: the hypothesis at the index n
    (have! `(IN ,nv (ORD-SEGMENT (succ ,nv)))
           (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (dk-apply! agree nv)
    (subst `(= (,gv ,nv) (IDEN ,agv)))
    ;; the rest: the IH, whose own guard is the hypothesis restricted to OS(n)
    (have! `(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT ,nv)) (= (,gv i_) (IDEN ,agv))))
           (lambda ()
             (let ((iv (dk-di-var!)))
               (have! `(IN ,iv (ORD-SEGMENT (succ ,nv)))
                      (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
               (dk-apply! agree iv)
               (ass))))
    (dk-apply! ih agv gv)
    (subst `(= (SUM-AG ,agv ,gv ,nv) (IDEN ,agv)))      ; (= ((OPR ag) (IDEN ag) (IDEN ag)) (IDEN ag))
    (dk-fact! 'group-left-id agv (list 'IDEN agv))
    (ass)))
(ftp-check! 'sum-ag-all-id-ind)
(qed 'sum-ag-all-id-ind)
(topic! 'sum-ag-all-id-ind 'algebra)

;;; ---------------------------------------------------------------------------
;;; finsum-all-id -- the statement as theorem-library/finsum-additive.scm spells it
;;; (its `tf' / `tfin' builders expanded).
;;;
;;; FINSUM(ag,f,S) is SUM-AG over the ENUM-FAM of the chosen enumeration, so the whole
;;; content is that the family is identically IDEN on ORD-SEGMENT(|S|): at an index i_
;;; there, ENUM-FAM beta-reduces through its IF (i_ IS in the segment) to f(FIN-ENUM(S)(i_)),
;;; and FIN-ENUM(S)(i_) lies in S, where f is IDEN by hypothesis.  Then sum-ag-all-id-ind.
;;; `lam-b' needs its argument TYPED FIRST (CLAUDE.md), which is what the
;;; ord-segment-nn-subset citation is for: i_ in ORD-SEGMENT(|S|) gives i_ in NN, the
;;; lambda's own domain.

(define ftp-finsum-all-id-stmt
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (CARR ag)))
       (IMPLIES (FORALL z (IMPLIES (IN z S) (= (f z) (IDEN ag))))
                (= (FINSUM ag f S) (IDEN ag)))))))))))

(sp (make-wff ftp-finsum-all-id-stmt))
(dk-peel!)
(let* ((agv (cadr (ftp-pick-head 'IS-ABELIAN-GROUP "IS-ABELIAN-GROUP ag")))
       (sv  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'SET)))
                           "S in SET")))
       (fv  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                            (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)
                                            (equal? (cadr (caddr f)) sv)))
                           "f in FUN(S, CARR ag)")))
       (agree (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                        (equal? (caddr (cadr (caddr f))) sv)))
                       "forall z in S. f z = IDEN ag"))
       (fam (list 'ENUM-FAM agv fv (list 'FIN-ENUM sv) (list 'CARD sv))))
  (mac 'FINSUM)
  (dk-fact! 'abelian-group-is-group agv)
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (have! `(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT (CARD ,sv)))
                              (= ,(list fam 'i_) (IDEN ,agv))))
         (lambda ()
           (let* ((iv  (dk-di-var!))
                  (ift `(IF (IN ,iv (ORD-SEGMENT (CARD ,sv)))
                            (,fv ((FIN-ENUM ,sv) ,iv))
                            (IDEN ,agv))))
             (dk-fact! 'ord-segment-nn-subset (list 'CARD sv) iv)   ; (IN i_ NN): type BEFORE the beta
             (mac 'ENUM-FAM)
             (lam-b)
             (let* ((ls   (dk-opened (lambda () (if-true ift))))
                    (cond-leaf (ftp-leaf ls (lambda (g) (and (pair? g) (eq? (car g) 'IN))) "if-true condition"))
                    (main (ftp-leaf ls (lambda (g) (and (pair? g) (eq? (car g) '=))) "if-true main")))
               (dk-focus! cond-leaf) (ass)
               (dk-focus! main)
               (subst (list '= ift (list fv (list (list 'FIN-ENUM sv) iv))))
               (dk-fact! 'fun-apply-type-c (list 'FIN-ENUM sv)
                         (list 'ORD-SEGMENT (list 'CARD sv)) sv iv)
               (dk-apply! agree (list (list 'FIN-ENUM sv) iv))
               (ass)))))
  (dk-fact! 'sum-ag-all-id-ind (list 'CARD sv) agv fam)
  (ass))
(ftp-check! 'finsum-all-id)
(qed 'finsum-all-id)
(topic! 'finsum-all-id 'algebra)
