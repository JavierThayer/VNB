;;; meta-cr.scm -- CONTEXTUAL REWRITING (CR) over the encoded core: the one-step rewrite relation
;;; with its local contexts, the equivalence it is to be proved inside, and the kernel relations of
;;; the seven rewriting rules, transcribed.
;;; (docs/meta-k2-admissibility-2026-10-08.md, sections 4.5 and 6, phase 3.)
;;; DEFINITIONS ONLY; the laws are in theorem-library/meta-cr-laws.scm.
;;; Agent META-3, 2026-10-09.  Builds on structure-library/meta-syntax.scm and meta-core.scm, which it
;;; does not edit.  Every binder and parameter here is an mr*_ name used by no other body in the tree.
;;;
;;; 1. POSITIONS ARE NOT A DATATYPE HERE; THE RELATION IS.  A position p of G with subterm s is
;;;    represented by a DERIVATION of the one-step relation REWR below: each clause descends ONE
;;;    level, names the child it enters and the local-context increment of that child, and the
;;;    clause TOP closes the descent at the position itself.  The triple [kk, g, G, G'] is in REWR
;;;    exactly when G' is G with one subexpression replaced, the replacement justified in the local
;;;    context g u Delta(p) by the TOP clause.  SUB-AT and REPLACE-AT as functions were considered
;;;    and not built, for three reasons:
;;;      (i)   a function by recursion on a position LIST bills the two asserted generation axioms of
;;;            structure-library/list-recursion.scm (every list induction does), so no law about it
;;;            could be `modulo 0';
;;;      (ii)  by recursion on the depth instead, SUB-AT is a def-by-nn-recursion with parameters, but
;;;            REPLACE-AT rebuilds bottom-up and needs NN subtraction in every equation;
;;;      (iii) Delta(p) depends on the siblings along the path (the other conjunct, the antecedent):
;;;            as a function it is a third recursion over (G, p), and CR's induction would have to
;;;            relate all three; as clauses it is one formula per clause.
;;;    WF preservation is built into the clauses: every clause demands that both sides of its
;;;    conclusion be sentences (CLF) or closed terms (CLT) of the clause's kind, and the TOP clauses
;;;    demand it of s and t.  The kind kk (2 = formula, 1 = term, the WKS codes) is the first entry
;;;    of the tuple, so that a clause entering a term child of an atom names the child's kind
;;;    syntactically.
;;;
;;; 2. BINDERS: COFINITE QUANTIFICATION (Aydemir et al. 2008).  A clause descending into the body b
;;;    of a binder of one variable requires the rewrite of the OPENED bodies OPEN(b, 0, FVAR y),
;;;    OPEN(b2, 0, FVAR y) for EVERY name y outside some finite set L of names.  This is the
;;;    kernel's licence "for an arbitrary value of the bound variable"; the finite exception set is
;;;    what lets the CR proof pick, at the use, a y fresh for everything else (the context, the
;;;    other side) without a renaming lemma for derivations.  The kernel drops from the local
;;;    context every assumption mentioning the bound variable's NAME (rkw--drop-shadowed): in the
;;;    locally nameless encoding no context formula can mention the bound variable (it is an index),
;;;    and a context formula about an outer variable spelled like the binder is about a different
;;;    FVAR; keeping it is sound.  So the clauses below pass the context g unchanged under a binder.
;;;
;;; 3. THE LOCAL CONTEXTS (the increments), transcribed from the macete checker's walk
;;;    (rkw--descend, rule-checkers-rewrite.scm 471-554; md5 8d9c0c63... on worker-01, 2026-10-09):
;;;      IMPLIES (503-505): the consequent gains the antecedent; the antecedent gains nothing.
;;;      AND     (506-509): the RIGHT conjunct gains the left, the LEFT conjunct gains the right.
;;;      OR      (510-513): each disjunct gains the negation of the other.
;;;      FORALL FORSOME IOTA COMP (514-521), SEP BIG-UNION (522-532), VNB-LAMBDA (533-540): the body
;;;              loses every assumption mentioning the bound variable; the domain (SEP, BIG-UNION,
;;;              VNB-LAMBDA) is walked in the ambient context.
;;;      everything else (541-546: NOT, IFF, the atoms, the term heads, IF): no increment.
;;;    The rewriter's own increments (lc-extend, macetes.scm 334-353) differ in one clause: the LEFT
;;;    conjunct gains nothing.  The checker is what is verified, so AND-L carries the right conjunct.
;;;    Each clause is sound for ONE position.  The checker applies them to SEVERAL positions in one
;;;    inference with every context read off the CONCLUSION, and for OR (both: rewriter and checker)
;;;    and AND (checker) that is not sound: see scratchpad/triage/META-3-REPORT.md, section 0.
;;;
;;; 4. THE EQUIVALENCE.  EQV(T) is the set of tuples [2, g, e, e2] with e, e2 sentences and
;;;    [g, e IFF e2] derivable, and [1, g, e, e2] with e, e2 closed terms and [g, e == e2] derivable.
;;;    REWR(J, k) is the least set closed under the clauses of stage <= k, J the set of tuples TOP
;;;    admits.  CR is the theorem: J SUBSET EQV(T) implies REWR(J, k) SUBSET EQV(T), from which
;;;    [g, G'] derivable implies [g, G] derivable is one iff-elim.  With J = EQV(T) this is CR as the
;;;    design note states it (the local equivalence derivable in g u Delta(p)); with J the local redex
;;;    pairs of a kernel rule it is that rule's one-position admissibility (section 6).
;;;
;;; 5. THE STAGES.  REWR(T, k) is the least set closed under the clauses of stage <= k:
;;;      1  the connectives and the atoms               (the brief's (a))
;;;      2  FORALL / FORSOME                            (b)
;;;      3  IF                                          (f)
;;;      4  the term heads: an application of a predicate or a term constant   (c)
;;;      5  the DOMAIN of SEP / BIG-UNION / VNB-LAMBDA  (d, the part outside the binder)
;;;      6  the BODY of SEP / BIG-UNION / VNB-LAMBDA    (d, the part inside the binder)
;;;      7  the body of COMP / IOTA                     (e)
;;;    IF is numbered before the term heads because its clauses need no hole in a list, so that the
;;;    stages proven form a prefix.  A stage whose closure is not proved leaves REWR(T, k) for the
;;;    smaller k as the result.
;;;
;;; Dependencies: structure-library/meta-syntax, structure-library/meta-core (CLF, CLT, CTX-SET,
;;; CTX-ADD, DERIVABLE, the ENC- constructors), cardinality (CARD).  No proof is cited.

;;; -----------------------------------------------------------------------
;;; Scheme helpers (meta-core.scm's mc--ex / mc--and live in that file's own environment).

(define (mr--ex vars body)
  (if (null? vars) body `(FORSOME ,(car vars) ,(mr--ex (cdr vars) body))))
(define (mr--and . fs)
  (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(apply mr--and (cdr fs)))))
(define (mr--or . fs)
  (if (null? (cdr fs)) (car fs) `(OR ,(car fs) ,(apply mr--or (cdr fs)))))
;; "for every name y outside a finite set of names": BODY mentions mry_
(define (mr--cof body)
  `(FORSOME mrfs_ (AND (IN mrfs_ SET) (AND (SUBSET mrfs_ NN) (AND (IN (CARD mrfs_) NN)
      (FORALL mry_ (IMPLIES (IN mry_ NN) (IMPLIES (NOT (IN mry_ mrfs_)) ,body))))))))

;;; -----------------------------------------------------------------------
;;; 1. The universe of rewrite tuples, and the equivalence.

(def-constant 'RW-UNIV '(rw-univ-def (== RW-UNIV (CARTESIAN NN CTX-SET EXPR-SET EXPR-SET))))
(notation! 'RW-UNIV 'kind 'constant 'arity 0 'english "the rewrite tuples [kind, context, expression, expression]")

(def-predicate 'EQV-OK '(mrt_ mrx_)
  (mr--ex '(mrg_ mre_ mrf_)
    (mr--or (mr--and '(= mrx_ (LIST 2 mrg_ mre_ mrf_)) '(IN mre_ CLF) '(IN mrf_ CLF)
                     '(IN (LIST mrg_ (ENC-IFF mre_ mrf_)) (DERIVABLE mrt_)))
            (mr--and '(= mrx_ (LIST 1 mrg_ mre_ mrf_)) '(IN mre_ CLT) '(IN mrf_ CLT)
                     '(IN (LIST mrg_ (ENC-QEQ mre_ mrf_)) (DERIVABLE mrt_))))))
(notation! 'EQV-OK 'kind 'predicate 'arity 2
           'english "$2 relates two sentences equivalent, or two closed terms quasi-equal, over $1 in its context")

(def-functoid 'EQV '(mrt_) '(SEP mrx_ RW-UNIV (EQV-OK mrt_ mrx_)))
(notation! 'EQV 'kind 'functoid 'arity 1 'english "the derivable equivalences over $1")

;;; -----------------------------------------------------------------------
;;; 2. The clauses RW-<NAME>(J, S, x): x is concluded by the clause from premises in S, J the
;;;    justification set of TOP (below).
;;;    (mr--rw! NAME STAGE NOTE BODY) also records the stage.

(define mr--rw-clauses '())
(define (mr--rw! name stage note body)
  (def-predicate name '(mrt_ mrs_ mrx_) body)
  (notation! name 'kind 'predicate 'arity 3 'english note)
  (set! mr--rw-clauses (append mr--rw-clauses (list (cons name stage)))))

;;; Stage 1: TOP, the connectives, the atoms.
;; TOP: the rewrite at the position itself.  The first parameter of every clause, of RW-RULE,
;; RW-CLOSED and REWR is the JUSTIFICATION SET J: the tuples [kk, g, s, t] that may stand at a position,
;; g the local context there.  CR is proved for every J inside EQV(T) (cr-k); J = EQV(T) itself is the
;; rewrite by any derivable local equivalence, and the J of each rewriting rule (section 4) is the set
;; of its local redex pairs.  Only TOP reads J.
(mr--rw! 'RW-TOP 1 "the rewrite clause TOP relates $2 to $3" '(IN mrx_ mrt_))
;; NOT (rule-checkers-rewrite.scm 541-546: no increment).
(mr--rw! 'RW-NOT 1 "the rewrite clause NOT relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (ENC-NOT mra_) (ENC-NOT mrb_))) '(IN (LIST 2 mrg_ mra_ mrb_) mrs_))))
;; AND (506-509): the left conjunct gains the right one, the right conjunct the left one.
(mr--rw! 'RW-AND-L 1 "the rewrite clause AND-left relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (ENC-AND mra_ mrc_) (ENC-AND mrb_ mrc_))) '(IN mrc_ CLF)
             '(IN (LIST 2 (CTX-ADD mrg_ mrc_) mra_ mrb_) mrs_))))
(mr--rw! 'RW-AND-R 1 "the rewrite clause AND-right relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (ENC-AND mrc_ mra_) (ENC-AND mrc_ mrb_))) '(IN mrc_ CLF)
             '(IN (LIST 2 (CTX-ADD mrg_ mrc_) mra_ mrb_) mrs_))))
;; OR (510-513): each disjunct gains the negation of the other.
(mr--rw! 'RW-OR-L 1 "the rewrite clause OR-left relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (ENC-OR mra_ mrc_) (ENC-OR mrb_ mrc_))) '(IN mrc_ CLF)
             '(IN (LIST 2 (CTX-ADD mrg_ (ENC-NOT mrc_)) mra_ mrb_) mrs_))))
(mr--rw! 'RW-OR-R 1 "the rewrite clause OR-right relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (ENC-OR mrc_ mra_) (ENC-OR mrc_ mrb_))) '(IN mrc_ CLF)
             '(IN (LIST 2 (CTX-ADD mrg_ (ENC-NOT mrc_)) mra_ mrb_) mrs_))))
;; IMPLIES (503-505): the consequent gains the antecedent.
(mr--rw! 'RW-IMP-L 1 "the rewrite clause IMPLIES-left relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (ENC-IMP mra_ mrc_) (ENC-IMP mrb_ mrc_))) '(IN mrc_ CLF)
             '(IN (LIST 2 mrg_ mra_ mrb_) mrs_))))
(mr--rw! 'RW-IMP-R 1 "the rewrite clause IMPLIES-right relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (ENC-IMP mrc_ mra_) (ENC-IMP mrc_ mrb_))) '(IN mrc_ CLF)
             '(IN (LIST 2 (CTX-ADD mrg_ mrc_) mra_ mrb_) mrs_))))
;; IFF: no increment.
(mr--rw! 'RW-IFF-L 1 "the rewrite clause IFF-left relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (ENC-IFF mra_ mrc_) (ENC-IFF mrb_ mrc_))) '(IN mrc_ CLF)
             '(IN (LIST 2 mrg_ mra_ mrb_) mrs_))))
(mr--rw! 'RW-IFF-R 1 "the rewrite clause IFF-right relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (ENC-IFF mrc_ mra_) (ENC-IFF mrc_ mrb_))) '(IN mrc_ CLF)
             '(IN (LIST 2 mrg_ mra_ mrb_) mrs_))))
;; The atoms IN, =, == (heads 7, 8, 9): a TERM child rewritten, no increment.
(mr--rw! 'RW-REL-L 1 "the rewrite clause ATOM-left relates $2 to $3"
  (mr--ex '(mrg_ mrh_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (EAPP mrh_ (LIST mra_ mrc_)) (EAPP mrh_ (LIST mrb_ mrc_))))
             '(IN mrh_ NN) '(<= 7 mrh_) '(<= mrh_ 9) '(IN mrc_ CLT)
             '(IN (LIST 1 mrg_ mra_ mrb_) mrs_))))
(mr--rw! 'RW-REL-R 1 "the rewrite clause ATOM-right relates $2 to $3"
  (mr--ex '(mrg_ mrh_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (EAPP mrh_ (LIST mrc_ mra_)) (EAPP mrh_ (LIST mrc_ mrb_))))
             '(IN mrh_ NN) '(<= 7 mrh_) '(<= mrh_ 9) '(IN mrc_ CLT)
             '(IN (LIST 1 mrg_ mra_ mrb_) mrs_))))

;;; Stage 2: the quantifiers, by cofinite quantification over the opening name.
(mr--rw! 'RW-ALL 2 "the rewrite clause FORALL relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (ENC-ALL mra_) (ENC-ALL mrb_))) '(IN (ENC-ALL mra_) CLF) '(IN (ENC-ALL mrb_) CLF)
             (mr--cof '(IN (LIST 2 mrg_ (EXPR-OPEN mra_ 0 (EFVAR mry_)) (EXPR-OPEN mrb_ 0 (EFVAR mry_))) mrs_)))))
(mr--rw! 'RW-EX 2 "the rewrite clause FORSOME relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_)
    (mr--and '(= mrx_ (LIST 2 mrg_ (ENC-EX mra_) (ENC-EX mrb_))) '(IN (ENC-EX mra_) CLF) '(IN (ENC-EX mrb_) CLF)
             (mr--cof '(IN (LIST 2 mrg_ (EXPR-OPEN mra_ 0 (EFVAR mry_)) (EXPR-OPEN mrb_ 0 (EFVAR mry_))) mrs_)))))

;;; Stage 4 (the brief's (c)): an application of a predicate (head 10, a formula) or a term constant (head >= 11, a
;;; term), ONE term argument rewritten: l2 agrees with l off the index i.
(define (mr--app-clause kk cls h-cond)
  (mr--ex '(mrg_ mrh_ mra_ mrb_ mri_)
    (mr--and `(= mrx_ (LIST ,kk mrg_ (EAPP mrh_ mra_) (EAPP mrh_ mrb_))) '(IN mrh_ NN) h-cond
             `(IN (EAPP mrh_ mra_) ,cls) `(IN (EAPP mrh_ mrb_) ,cls)
             '(IN mra_ (TUPLES EXPR-SET)) '(IN mrb_ (TUPLES EXPR-SET)) '(= (LENGTH mrb_) (LENGTH mra_))
             '(IN mri_ NN) '(<= 1 mri_) '(<= mri_ (LENGTH mra_))
             '(FORALL mrj_ (IMPLIES (IN mrj_ NN) (IMPLIES (<= 1 mrj_) (IMPLIES (<= mrj_ (LENGTH mra_))
                (IMPLIES (NOT (= mrj_ mri_)) (= (NTH mrj_ mrb_) (NTH mrj_ mra_)))))))
             '(IN (LIST 1 mrg_ (NTH mri_ mra_) (NTH mri_ mrb_)) mrs_))))
(mr--rw! 'RW-PRED 4 "the rewrite clause PREDICATE-argument relates $2 to $3"
  (mr--app-clause 2 'CLF '(= mrh_ 10)))
(mr--rw! 'RW-TAPP 4 "the rewrite clause TERM-argument relates $2 to $3"
  (mr--app-clause 1 'CLT '(<= 11 mrh_)))

;;; Stages 5 and 6 (the brief's (d)): SEP (22, body a formula), BIG-UNION (24) and VNB-LAMBDA (26)
;;; (body a term): the outside argument (stage 5), and the body by cofinite quantification (stage 6).
(mr--rw! 'RW-BIND-DOM 5 "the rewrite clause BINDER-domain relates $2 to $3"
  (mr--ex '(mrg_ mrh_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 1 mrg_ (EBIND mrh_ 1 (LIST mra_) mrc_) (EBIND mrh_ 1 (LIST mrb_) mrc_)))
             '(OR (= mrh_ 22) (OR (= mrh_ 24) (= mrh_ 26)))
             '(IN (EBIND mrh_ 1 (LIST mra_) mrc_) CLT) '(IN (EBIND mrh_ 1 (LIST mrb_) mrc_) CLT)
             '(IN (LIST 1 mrg_ mra_ mrb_) mrs_))))
(mr--rw! 'RW-SEP-BODY 6 "the rewrite clause SEP-body relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 1 mrg_ (ENC-SEP mrc_ mra_) (ENC-SEP mrc_ mrb_)))
             '(IN (ENC-SEP mrc_ mra_) CLT) '(IN (ENC-SEP mrc_ mrb_) CLT)
             (mr--cof '(IN (LIST 2 mrg_ (EXPR-OPEN mra_ 0 (EFVAR mry_)) (EXPR-OPEN mrb_ 0 (EFVAR mry_))) mrs_)))))
(mr--rw! 'RW-TBIND-BODY 6 "the rewrite clause BIG-UNION / LAMBDA-body relates $2 to $3"
  (mr--ex '(mrg_ mrh_ mra_ mrb_ mrc_)
    (mr--and '(= mrx_ (LIST 1 mrg_ (EBIND mrh_ 1 (LIST mrc_) mra_) (EBIND mrh_ 1 (LIST mrc_) mrb_)))
             '(OR (= mrh_ 24) (= mrh_ 26))
             '(IN (EBIND mrh_ 1 (LIST mrc_) mra_) CLT) '(IN (EBIND mrh_ 1 (LIST mrc_) mrb_) CLT)
             (mr--cof '(IN (LIST 1 mrg_ (EXPR-OPEN mra_ 0 (EFVAR mry_)) (EXPR-OPEN mrb_ 0 (EFVAR mry_))) mrs_)))))

;;; Stage 7 (the brief's (e)): COMP (23) and IOTA (25), the body (a formula) by cofinite quantification.
(mr--rw! 'RW-DESC-BODY 7 "the rewrite clause COMP / IOTA-body relates $2 to $3"
  (mr--ex '(mrg_ mrh_ mra_ mrb_)
    (mr--and '(= mrx_ (LIST 1 mrg_ (EBIND mrh_ 1 (LIST) mra_) (EBIND mrh_ 1 (LIST) mrb_)))
             '(OR (= mrh_ 23) (= mrh_ 25))
             '(IN (EBIND mrh_ 1 (LIST) mra_) CLT) '(IN (EBIND mrh_ 1 (LIST) mrb_) CLT)
             (mr--cof '(IN (LIST 2 mrg_ (EXPR-OPEN mra_ 0 (EFVAR mry_)) (EXPR-OPEN mrb_ 0 (EFVAR mry_))) mrs_)))))

;;; Stage 3 (the brief's (f)): IF (27, a binder of no variable): the condition (the body) and the two branches (the
;;; outside list).  No increment (541-546: IF is an `else' head of the walk).
(mr--rw! 'RW-IF-COND 3 "the rewrite clause IF-condition relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_ mrd_)
    (mr--and '(= mrx_ (LIST 1 mrg_ (ENC-IF mra_ mrc_ mrd_) (ENC-IF mrb_ mrc_ mrd_)))
             '(IN (ENC-IF mra_ mrc_ mrd_) CLT) '(IN (ENC-IF mrb_ mrc_ mrd_) CLT)
             '(IN mrc_ CLT) '(IN mrd_ CLT) '(IN (LIST 2 mrg_ mra_ mrb_) mrs_))))
(mr--rw! 'RW-IF-THEN 3 "the rewrite clause IF-then relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_ mrd_)
    (mr--and '(= mrx_ (LIST 1 mrg_ (ENC-IF mrc_ mra_ mrd_) (ENC-IF mrc_ mrb_ mrd_)))
             '(IN (ENC-IF mrc_ mra_ mrd_) CLT) '(IN (ENC-IF mrc_ mrb_ mrd_) CLT)
             '(IN mrc_ CLF) '(IN mrd_ CLT) '(IN (LIST 1 mrg_ mra_ mrb_) mrs_))))
(mr--rw! 'RW-IF-ELSE 3 "the rewrite clause IF-else relates $2 to $3"
  (mr--ex '(mrg_ mra_ mrb_ mrc_ mrd_)
    (mr--and '(= mrx_ (LIST 1 mrg_ (ENC-IF mrc_ mrd_ mra_) (ENC-IF mrc_ mrd_ mrb_)))
             '(IN (ENC-IF mrc_ mrd_ mra_) CLT) '(IN (ENC-IF mrc_ mrd_ mrb_) CLT)
             '(IN mrc_ CLF) '(IN mrd_ CLT) '(IN (LIST 1 mrg_ mra_ mrb_) mrs_))))

;;; -----------------------------------------------------------------------
;;; 3. RW-RULE, RW-CLOSED, REWR.

(def-predicate 'RW-RULE '(mrt_ mrk_ mrs_ mrx_)
  (let loop ((cs mr--rw-clauses))
    (let ((this `(AND (<= ,(cdar cs) mrk_) (,(caar cs) mrt_ mrs_ mrx_))))
      (if (null? (cdr cs)) this `(OR ,this ,(loop (cdr cs)))))))
(notation! 'RW-RULE 'kind 'predicate 'arity 4 'english "some rewrite clause of stage at most $2, justified by $1, concludes $4 from $3")

(def-predicate 'RW-CLOSED '(mrt_ mrk_ mrs_)
  '(FORALL mrx_ (IMPLIES (RW-RULE mrt_ mrk_ mrs_ mrx_) (IMPLIES (IN mrx_ RW-UNIV) (IN mrx_ mrs_)))))
(notation! 'RW-CLOSED 'kind 'predicate 'arity 3 'english "$3 is closed under the rewrite clauses of stage at most $2 justified by $1")

(def-functoid 'REWR '(mrt_ mrk_)
  '(SEP mrx_ RW-UNIV (FORALL mrs_ (IMPLIES (IN mrs_ (POWER RW-UNIV)) (IMPLIES (RW-CLOSED mrt_ mrk_ mrs_) (IN mrx_ mrs_))))))
(notation! 'REWR 'kind 'functoid 'arity 2 'english "the one-position rewrites justified by $1, of stage at most $2")

;;; -----------------------------------------------------------------------
;;; 4. THE REWRITING RULES OF THE KERNEL, TRANSCRIBED, AND THEIR ONE-POSITION FORMS.
;;;
;;; THE KERNEL'S RELATIONS (read on worker-01, 2026-10-09; rule-checkers-logic.scm md5 099320f4...,
;;; rule-checkers-schema.scm 76723230..., rule-checkers-rewrite.scm 8d9c0c63...).  Each is stated here
;;; in words beside its lines; the encoded REL-<NAME>-1 below is the ONE-POSITION relation that is
;;; admissible over the core, and the difference between the two is reported as a finding.
;;;
;;;  nth-reduce (rule-checkers-logic.scm 1297-1317).  One hypothesis, the conclusion's context; the
;;;    hypothesis goal is the conclusion goal with SOME redexes (NTH k (LIST a1..an)), k a numeral,
;;;    1 <= k <= n, contracted to a_k, at ANY depth (chk-contracts-d?, 344-357: a structural descent
;;;    into every list, binders included, with no context), contractions inside a contractum allowed.
;;;    NO condition: the list need not denote.
;;;  length-reduce (1319-1331).  The same with (LENGTH (LIST a1..an)) -> n.
;;;  functoid-beta (1333-1351).  The same with (apply-functoid <lambdoid> v1..vn) -> body[x_i := v_i],
;;;    a parallel substitution; no condition on the v_i.
;;;  lambda-beta (rule-checkers-schema.scm 899-968).  The hypothesis goal is the conclusion goal with
;;;    redexes ((VNB-LAMBDA x A b) u) contracted innermost first; each contracted redex is LICENSED by
;;;    u in A held in the conclusion's context, or by the binders it sits under (rcs--rx-scope: inside
;;;    VNB-LAMBDA x A, x in A), or OWED as an obligation hypothesis Gamma |- (IN u A) that mentions no
;;;    variable bound where the redex sits; and the value must be certified a set or owed (IN v SET).
;;;  lambda-beta-hyp (970-1034).  The same contraction on ONE assumption.
;;;  macete (rule-checkers-rewrite.scm 710-762, with the walk 445-554, the explainer 676-708 and the
;;;    discharge 390-399).  The tag names an installed theorem read as (conditions, L, R); the first
;;;    hypothesis is the conclusion with SOME instances sigma(L) replaced by sigma(R), the walk
;;;    comparing conclusion and hypothesis in PARALLEL, every position's local context computed from
;;;    the CONCLUSION (Monk's increments, section 3 of the header); each sigma(C) is in that local
;;;    context (up to numeral collapse), a true ground arithmetic sentence, or the goal of a minor
;;;    hypothesis Gamma |- C.  No condition on sigma's values.
;;;  macete-hyp (764-840).  The same on ONE assumption H, the local context seeded with all of Gamma.
;;;
;;; AS TRANSCRIBED, the macete relations are FALSE (three counterexamples on the band, report section
;;; 0): several positions with contexts read off the conclusion (OR, and the checker's AND); a minor
;;; premise naming a variable bound on the path; an instantiation at an undefined term.  The four
;;; reduction relations rewrite under every binder, where CR is not derivable over the present core
;;; (stages 6 and 7), and nth-reduce / length-reduce do not ask the list to denote (the core's nth-eq /
;;; length-eq do: META-2 finding 4.5).
;;;
;;; THE ONE-POSITION FORMS.  REL-REWRITE-1(J, hs, c): one hypothesis, the goal rewritten at ONE
;;; position of stage <= 5 (connectives, atoms, quantifiers, IF, the arguments of a predicate or term
;;; constant, the domain of a term binder), justified at the position by a tuple of J.  REL-REWRITE-HYP-1(J, hs, c): the same on one
;;; assumption H, replaced (H removed, H' added: the kernel's macete-hyp / lambda-beta-hyp shape).
;;; Each rule's justification set J-<RULE>(T) holds its LOCAL redex pairs with their side conditions
;;; DERIVED in the local context: the list denotes (nth, length), the argument is in the domain
;;; (lambda), the condition holds and the instantiating term denotes (macete).
;;; The forms at a position of ANY stage (binder bodies included), REL-REWRITE-7 and REL-<RULE>-7, are section 5
;;; (agent K2-END, 2026-10-22): their admissibility needs CR at stage 7, hence AX-CLASS-EXT in T.

(def-predicate 'REL-REWRITE-1 '(mrt_ mrhs_ mrc_)
  (mr--and '(IN mrc_ SEQ-SET)
    (mr--ex '(mrg_ mra_ mrb_)
      (mr--and '(= mrc_ (LIST mrg_ mra_)) '(= mrhs_ (LIST (LIST mrg_ mrb_)))
               '(IN (LIST 2 mrg_ mra_ mrb_) (REWR mrt_ 5))))))
(notation! 'REL-REWRITE-1 'kind 'predicate 'arity 3 'english "$2 is $3 with its goal rewritten at one position justified by $1")
(def-predicate 'REL-REWRITE-HYP-1 '(mrt_ mrhs_ mrc_)
  (mr--and '(IN mrc_ SEQ-SET)
    (mr--ex '(mrg_ mrf_ mra_ mrb_)
      (mr--and '(= mrc_ (LIST mrg_ mrf_)) '(IN mra_ mrg_)
               '(= mrhs_ (LIST (LIST (CTX-ADD (DIFFERENCE mrg_ (PAIR mra_ mra_)) mrb_) mrf_)))
               '(IN (LIST 2 mrg_ mra_ mrb_) (REWR mrt_ 5))))))
(notation! 'REL-REWRITE-HYP-1 'kind 'predicate 'arity 3 'english "$2 is $3 with one assumption rewritten at one position justified by $1")

;; nth-reduce: NTH(k, [l]) -> l_k, the list denoting in the local context.
(def-functoid 'J-NTH '(mrt_)
  `(SEP mrx_ RW-UNIV
     ,(mr--ex '(mrg_ mrl_ mrk_)
        (mr--and '(= mrx_ (LIST 1 mrg_ (ENC-NTH (ENC-NUM mrk_) (ENC-LIST mrl_)) (NTH mrk_ mrl_)))
                 '(IN mrk_ NN) '(<= 1 mrk_) '(<= mrk_ (LENGTH mrl_))
                 '(IN (ENC-NTH (ENC-NUM mrk_) (ENC-LIST mrl_)) CLT) '(IN (NTH mrk_ mrl_) CLT)
                 '(IN (LIST mrg_ (ENC-EQ (ENC-LIST mrl_) (ENC-LIST mrl_))) (DERIVABLE mrt_))))))
;; length-reduce: LENGTH([l]) -> |l|, the list denoting in the local context.
(def-functoid 'J-LEN '(mrt_)
  `(SEP mrx_ RW-UNIV
     ,(mr--ex '(mrg_ mrl_)
        (mr--and '(= mrx_ (LIST 1 mrg_ (ENC-LENGTH (ENC-LIST mrl_)) (ENC-NUM (LENGTH mrl_))))
                 '(IN (ENC-LENGTH (ENC-LIST mrl_)) CLT) '(IN (ENC-NUM (LENGTH mrl_)) CLT)
                 '(IN (LIST mrg_ (ENC-EQ (ENC-LIST mrl_) (ENC-LIST mrl_))) (DERIVABLE mrt_))))))
;; lambda-beta: (VNB-LAMBDA A b)(u) -> b[u], u in A derivable in the local context.
(def-functoid 'J-LB '(mrt_)
  `(SEP mrx_ RW-UNIV
     ,(mr--ex '(mrg_ mra_ mrb_ mre_)
        (mr--and '(= mrx_ (LIST 1 mrg_ (ENC-APPLY (ENC-LAM mra_ mrb_) mre_) (EXPR-OPEN mrb_ 0 mre_)))
                 '(IN (ENC-APPLY (ENC-LAM mra_ mrb_) mre_) CLT) '(IN (EXPR-OPEN mrb_ 0 mre_) CLT)
                 '(IN (LIST mrg_ (ENC-IN mre_ mra_)) (DERIVABLE mrt_))))))
;; macete: a member of T of ONE schema variable and one condition, ALL(c IMP (l == r)) (a term
;; macete) or ALL(c IMP (l IFF r)) (a formula macete), a sentence (theorem-assumption concludes a
;; sequent), instantiated at a term e that DENOTES in the local context, with the condition c[e]
;; derivable there.  A macete with no condition has c = TRUTH.
(def-functoid 'J-MAC '(mrt_)
  `(SEP mrx_ RW-UNIV
     ,(mr--ex '(mrg_ mrc_ mra_ mrb_ mre_)
        (mr--and '(IN mre_ CLT)
                 '(IN (LIST mrg_ (EXPR-OPEN mrc_ 0 mre_)) (DERIVABLE mrt_))
                 '(IN (LIST mrg_ (ENC-EQ mre_ mre_)) (DERIVABLE mrt_))
                 (mr--or (mr--and '(= mrx_ (LIST 1 mrg_ (EXPR-OPEN mra_ 0 mre_) (EXPR-OPEN mrb_ 0 mre_)))
                                  '(IN (ENC-ALL (ENC-IMP mrc_ (ENC-QEQ mra_ mrb_))) mrt_)
                                  '(IN (ENC-ALL (ENC-IMP mrc_ (ENC-QEQ mra_ mrb_))) CLF)
                                  '(IN (EXPR-OPEN mra_ 0 mre_) CLT) '(IN (EXPR-OPEN mrb_ 0 mre_) CLT))
                         (mr--and '(= mrx_ (LIST 2 mrg_ (EXPR-OPEN mra_ 0 mre_) (EXPR-OPEN mrb_ 0 mre_)))
                                  '(IN (ENC-ALL (ENC-IMP mrc_ (ENC-IFF mra_ mrb_))) mrt_)
                                  '(IN (ENC-ALL (ENC-IMP mrc_ (ENC-IFF mra_ mrb_))) CLF)
                                  '(IN (EXPR-OPEN mra_ 0 mre_) CLF) '(IN (EXPR-OPEN mrb_ 0 mre_) CLF)))))))
(for-each (lambda (e) (notation! (car e) 'kind 'functoid 'arity 1 'english (cadr e)))
  '((J-NTH "the local NTH-of-a-list redexes over $1, the list denoting")
    (J-LEN "the local LENGTH-of-a-list redexes over $1, the list denoting")
    (J-LB "the local lambda redexes over $1, the argument in the domain")
    (J-MAC "the local instances of the one-variable macetes of $1, the condition derivable and the instance denoting")))

;; functoid-beta (agent META-FUN, 2026-10-21; the user's decision B1): F(l) -> b[l] for a row (F, |l|, b) of
;; the functoid table FUN-DEF (structure-library/meta-core.scm 4.10), at ANY argument list: no side condition,
;; as the kernel's functoid-beta (an anonymous record, lambda-lifted into a row) and the unfold macete of a
;; def-functoid (kind functoid, which owes nothing) have none.  The parameter T is unused (the J sets of the
;; other rules read DERIVABLE(T)); it keeps the shape REL-REWRITE-1 and mr-adm! take.
(def-functoid 'J-FB '(mrt_)
  `(SEP mrx_ RW-UNIV
     ,(mr--ex '(mrg_ mrh_ mrl_ mrb_)
        (mr--and '(= mrx_ (LIST 1 mrg_ (EAPP mrh_ mrl_) (OPENL mrb_ mrl_ (LENGTH mrl_))))
                 '(FUN-DEF mrh_ (LENGTH mrl_) mrb_)
                 '(IN (EAPP mrh_ mrl_) CLT) '(IN (OPENL mrb_ mrl_ (LENGTH mrl_)) CLT)))))
(notation! 'J-FB 'kind 'functoid 'arity 1 'english "the local functoid redexes over $1, at any arguments")

;; The one-position kernel relations.  functoid-beta, under META-2's recommendation 4.4 (a functoid's
;; definition an encoded == equation of T), is the unconditional case of REL-MACETE-1 (c = TRUTH):
;; see the report, section 4, for why that recommendation is not adopted as it stands.  It is
;; REL-FUNCTOID-BETA-1 below, over the functoid table (META-FUN, 2026-10-21).
(def-predicate 'REL-NTH-REDUCE-1 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-1 (J-NTH mrt_) mrhs_ mrc_))
(def-predicate 'REL-LENGTH-REDUCE-1 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-1 (J-LEN mrt_) mrhs_ mrc_))
(def-predicate 'REL-LAMBDA-BETA-1 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-1 (J-LB mrt_) mrhs_ mrc_))
(def-predicate 'REL-LAMBDA-BETA-HYP-1 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-HYP-1 (J-LB mrt_) mrhs_ mrc_))
(def-predicate 'REL-MACETE-1 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-1 (J-MAC mrt_) mrhs_ mrc_))
(def-predicate 'REL-MACETE-HYP-1 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-HYP-1 (J-MAC mrt_) mrhs_ mrc_))
(def-predicate 'REL-FUNCTOID-BETA-1 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-1 (J-FB mrt_) mrhs_ mrc_))
(for-each (lambda (n) (notation! n 'kind 'predicate 'arity 3 'english "the kernel rule, at one position, relates $2 to $3"))
  '(REL-NTH-REDUCE-1 REL-LENGTH-REDUCE-1 REL-LAMBDA-BETA-1 REL-LAMBDA-BETA-HYP-1 REL-MACETE-1 REL-MACETE-HYP-1
    REL-FUNCTOID-BETA-1))

;;; -----------------------------------------------------------------------
;;; 5. THE ONE-POSITION FORMS AT EVERY STAGE (agent K2-END, 2026-10-22).  Since cr-closed-7
;;; (theorem-library/meta-ind-laws.scm, section M) CR is closed at every position, binder bodies included, for
;;; every T of sentences containing the encoded class-extensionality AX-CLASS-EXT.  REL-REWRITE-7 and
;;; REL-REWRITE-HYP-7 are REL-REWRITE-1 and REL-REWRITE-HYP-1 with the position of ANY stage (REWR(J, 7) for
;;; REWR(J, 5)): the bodies of SEP, BIG-UNION and VNB-LAMBDA (stage 6) and of COMP and IOTA (stage 7), where the
;;; kernel's reduction rules and macetes also rewrite (section 4: "at ANY depth ... binders included").  The
;;; justification sets J-<RULE> are section 4's; at a position under a binder the clause passes the context g
;;; unchanged (section 2 of the header), so a justification is derived in the AMBIENT context: a kernel step
;;; that reads the binder's own hypothesis (lambda-beta licensed by x in A inside VNB-LAMBDA x A) is outside the
;;; relation, as at stage 5.  The stage-<= 5 forms are kept: their admissibility needs no hypothesis on T.
;;; Admissibility: theorem-library/meta-ind-laws.scm, section N (adm-rewrite-7, adm-rewrite-hyp-7, adm-<rule>-7).
(def-predicate 'REL-REWRITE-7 '(mrt_ mrhs_ mrc_)
  (mr--and '(IN mrc_ SEQ-SET)
    (mr--ex '(mrg_ mra_ mrb_)
      (mr--and '(= mrc_ (LIST mrg_ mra_)) '(= mrhs_ (LIST (LIST mrg_ mrb_)))
               '(IN (LIST 2 mrg_ mra_ mrb_) (REWR mrt_ 7))))))
(notation! 'REL-REWRITE-7 'kind 'predicate 'arity 3 'english "$2 is $3 with its goal rewritten at one position of any stage justified by $1")
(def-predicate 'REL-REWRITE-HYP-7 '(mrt_ mrhs_ mrc_)
  (mr--and '(IN mrc_ SEQ-SET)
    (mr--ex '(mrg_ mrf_ mra_ mrb_)
      (mr--and '(= mrc_ (LIST mrg_ mrf_)) '(IN mra_ mrg_)
               '(= mrhs_ (LIST (LIST (CTX-ADD (DIFFERENCE mrg_ (PAIR mra_ mra_)) mrb_) mrf_)))
               '(IN (LIST 2 mrg_ mra_ mrb_) (REWR mrt_ 7))))))
(notation! 'REL-REWRITE-HYP-7 'kind 'predicate 'arity 3 'english "$2 is $3 with one assumption rewritten at one position of any stage justified by $1")
(def-predicate 'REL-NTH-REDUCE-7 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-7 (J-NTH mrt_) mrhs_ mrc_))
(def-predicate 'REL-LENGTH-REDUCE-7 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-7 (J-LEN mrt_) mrhs_ mrc_))
(def-predicate 'REL-LAMBDA-BETA-7 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-7 (J-LB mrt_) mrhs_ mrc_))
(def-predicate 'REL-LAMBDA-BETA-HYP-7 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-HYP-7 (J-LB mrt_) mrhs_ mrc_))
(def-predicate 'REL-MACETE-7 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-7 (J-MAC mrt_) mrhs_ mrc_))
(def-predicate 'REL-MACETE-HYP-7 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-HYP-7 (J-MAC mrt_) mrhs_ mrc_))
(def-predicate 'REL-FUNCTOID-BETA-7 '(mrt_ mrhs_ mrc_) '(REL-REWRITE-7 (J-FB mrt_) mrhs_ mrc_))
(for-each (lambda (n) (notation! n 'kind 'predicate 'arity 3 'english "the kernel rule, at one position of any stage, relates $2 to $3"))
  '(REL-NTH-REDUCE-7 REL-LENGTH-REDUCE-7 REL-LAMBDA-BETA-7 REL-LAMBDA-BETA-HYP-7 REL-MACETE-7 REL-MACETE-HYP-7
    REL-FUNCTOID-BETA-7))
