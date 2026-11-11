;;; meta-ind.scm -- K2 PHASE 4: the kernel relations of the induction rules, the set-formation rules
;;; and the structural rules, TRANSCRIBED from their checkers (rule-checkers-logic.scm,
;;; rule-checkers-schema.scm, rule-checkers-rewrite.scm of tree 95bf8fe, 2026-10-12), and the
;;; encoded catalog axioms the induction rules are derived from.
;;; (docs/meta-k2-admissibility-2026-10-08.md, sections 4.3, 4.6, 4.8 and 6, phase 4.)
;;; DEFINITIONS ONLY; the laws are in theorem-library/meta-ind-laws.scm.  Agent META-4, 2026-10-12.
;;; Builds on structure-library/meta-syntax.scm, meta-core.scm (phases 1-2), which it does not edit.
;;; Every binder and parameter here is an mi*_ name.
;;;
;;; CONVENTIONS (as meta-core.scm, section 6).  A kernel sequent is well formed by construction
;;; (make-wff), which is the conjunct (IN c SEQ-SET).  Contexts are compared as SETS (the checkers'
;;; convention 1), so "the hypothesis context is the conclusion's minus f plus a, b" is an equation
;;; of sets, written with DIFFERENCE and CTX-ADD.  The named substitution p[x := t] of a checker is,
;;; in the locally nameless encoding, EXPR-OPEN(p, 0, t) with p the binder's body (index 0 the bound
;;; variable) and t locally closed (it sits in a sentence).  A capture condition of a checker on a
;;; BOUND variable is vacuous here: a bound variable is an index, and no expression outside the
;;; binder can mention it.  An EIGENVARIABLE (a free variable of the conclusion side) is a name
;;; EFVAR(e), and its condition is a condition on EXPR-FV.
;;;
;;; CODES ADDED TO THE HEAD TABLE (meta-core.scm, section 1; the translator of K3 must mirror them):
;;;   CONST 3 = NN, CONST 5 = ORD (odd codes are named constants; 1 = SET is meta-core's);
;;;   CONST 7 = the predicate name ORD-LT, CONST 9 = the predicate name LIMIT-ORD (the first argument
;;;   of a head-10 predicate application names the predicate);
;;;   term head 30 = succ, term head 31 = succ_ORD.

;;; -----------------------------------------------------------------------
;;; 0. Small helpers (as meta-core's mc--ex / mc--and, renamed).

(define (mi--ex vars body)
  (if (null? vars) body `(FORSOME ,(car vars) ,(mi--ex (cdr vars) body))))
(define (mi--and . fs)
  (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(apply mi--and (cdr fs)))))
(define (mi--rel! name note body)
  (def-predicate name '(mit_ mihs_ mic_) (mi--and '(IN mic_ SEQ-SET) body))
  (notation! name 'kind 'predicate 'arity 3 'english note))

;;; -----------------------------------------------------------------------
;;; 1. SET FORMATION (rule-checkers-schema.scm 1026-1033 register; the procedures 107-307).
;;; NBGSEP (agent METACORE, 2026-10-29): every relation of this section carries the conjunct NBG-OK(p) on the
;;; SEP / COMP condition or the BIG-UNION body (meta-core.scm 4.3a): since 2026-10-24 each of these checkers
;;; refuses an impredicative binder term (rcs--binder-nbg?, rcs--comp-nbg?, rule-checkers-schema.scm of
;;; a320cb6f).

;; 107-118 (rcs-sep-sethood): goal (IN (SEP x A p) SET); one hypothesis, the same context, (IN A SET).
;; In the encoding this IS the core relation CR-SEP-SETHOOD.
(mi--rel! 'REL-SEP-SETHOOD "the kernel's sep-sethood relates $2 to $3"
  (mi--ex '(mig_ mia_ mip_)
    (mi--and '(= mic_ (LIST mig_ (ENC-IN (ENC-SEP mia_ mip_) ENC-SETC))) '(NBG-OK mip_)
             '(= mihs_ (LIST (LIST mig_ (ENC-IN mia_ ENC-SETC)))))))

;; 160-164 (rcs-sep-mem-intro, through rcs--mem-intro-check 120-136): goal (IN y (SEP x A p)); two
;; hypotheses, the same context: (IN y A) and p[x := y].
(mi--rel! 'REL-SEP-MEM-INTRO "the kernel's sep-mem-intro relates $2 to $3"
  (mi--ex '(mig_ mia_ mip_ miy_)
    (mi--and '(= mic_ (LIST mig_ (ENC-IN miy_ (ENC-SEP mia_ mip_)))) '(NBG-OK mip_)
             '(= mihs_ (LIST (LIST mig_ (ENC-IN miy_ mia_)) (LIST mig_ (EXPR-OPEN mip_ 0 miy_)))))))

;; 167-172 (rcs-sep-mem-elim, through rcs--mem-elim-check 140-157): some (IN y (SEP x A p)) in the
;; conclusion context; one hypothesis, the same goal, the context with that membership REMOVED and
;; (IN y A), p[x := y] added.
(mi--rel! 'REL-SEP-MEM-ELIM "the kernel's sep-mem-elim relates $2 to $3"
  (mi--ex '(mig_ mif_ mia_ mip_ miy_)
    (mi--and '(= mic_ (LIST mig_ mif_)) '(IN (ENC-IN miy_ (ENC-SEP mia_ mip_)) mig_) '(NBG-OK mip_)
             '(= mihs_ (LIST (LIST (CTX-ADD (CTX-ADD (DIFFERENCE mig_ (PAIR (ENC-IN miy_ (ENC-SEP mia_ mip_))
                                                                        (ENC-IN miy_ (ENC-SEP mia_ mip_))))
                                                     (ENC-IN miy_ mia_))
                                            (EXPR-OPEN mip_ 0 miy_))
                                   mif_))))))

;; 177-180 (rcs-comp-mem-intro): goal (IN y (COMP x p)); two hypotheses, the same context:
;; (IN y SET) and p[x := y].
(mi--rel! 'REL-COMP-MEM-INTRO "the kernel's comp-mem-intro relates $2 to $3"
  (mi--ex '(mig_ mip_ miy_)
    (mi--and '(= mic_ (LIST mig_ (ENC-IN miy_ (ENC-COMP mip_)))) '(NBG-OK mip_)
             '(= mihs_ (LIST (LIST mig_ (ENC-IN miy_ ENC-SETC)) (LIST mig_ (EXPR-OPEN mip_ 0 miy_)))))))

;; 182-186 (rcs-comp-mem-elim): some (IN y (COMP x p)) in the conclusion context; one hypothesis, the
;; same goal, the membership removed, (IN y SET) and p[x := y] added.
(mi--rel! 'REL-COMP-MEM-ELIM "the kernel's comp-mem-elim relates $2 to $3"
  (mi--ex '(mig_ mif_ mip_ miy_)
    (mi--and '(= mic_ (LIST mig_ mif_)) '(IN (ENC-IN miy_ (ENC-COMP mip_)) mig_) '(NBG-OK mip_)
             '(= mihs_ (LIST (LIST (CTX-ADD (CTX-ADD (DIFFERENCE mig_ (PAIR (ENC-IN miy_ (ENC-COMP mip_))
                                                                        (ENC-IN miy_ (ENC-COMP mip_))))
                                                     (ENC-IN miy_ ENC-SETC))
                                            (EXPR-OPEN mip_ 0 miy_))
                                   mif_))))))

;; 194-240 (rcs-big-union-sethood): goal (IN (BIG-UNION z A b) SET); two hypotheses, the same context:
;; (IN A SET) and (FORALL v (IMPLIES (IN v A) (IN b[z := v] SET))), v not captured by A nor by b (the
;; 2026-09-24 gap 2).  In the encoding the universal's body is (ENC-IMP (ENC-IN (EBVAR 0) A) (ENC-IN b
;; ENC-SETC)): b[z := v] under the new binder is b itself (its index 0 is now v), A is locally closed,
;; and the two capture conditions are vacuous.  So this IS the core relation CR-BIG-UNION-SETHOOD.
(mi--rel! 'REL-BIG-UNION-SETHOOD "the kernel's big-union-sethood relates $2 to $3"
  (mi--ex '(mig_ mia_ mib_)
    (mi--and '(= mic_ (LIST mig_ (ENC-IN (ENC-BU mia_ mib_) ENC-SETC))) '(NBG-OK mib_)
             '(= mihs_ (LIST (LIST mig_ (ENC-IN mia_ ENC-SETC))
                             (LIST mig_ (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) mia_) (ENC-IN mib_ ENC-SETC)))))))))

;; 243-266 (rcs-big-union-mem-intro): goal (IN x (BIG-UNION z A b)); two hypotheses, the same context:
;; (IN w A) for a witness w read off it, and (IN x b[z := w]).
(mi--rel! 'REL-BIG-UNION-MEM-INTRO "the kernel's big-union-mem-intro relates $2 to $3"
  (mi--ex '(mig_ mia_ mib_ mix_ miw_)
    (mi--and '(= mic_ (LIST mig_ (ENC-IN mix_ (ENC-BU mia_ mib_)))) '(NBG-OK mib_)
             '(= mihs_ (LIST (LIST mig_ (ENC-IN miw_ mia_)) (LIST mig_ (ENC-IN mix_ (EXPR-OPEN mib_ 0 miw_))))))))

;; 269-307 (rcs-big-union-mem-elim): some (IN x (BIG-UNION z A b)) in the conclusion context; one
;; hypothesis, the same goal, the membership removed and (IN e A), (IN x b[z := e]) added for an
;; EIGENVARIABLE e free in nothing else: not in the surviving context, the goal, A, b or x.  Since
;; the free names of the membership are those of x, A and b, that is: e is free neither in the
;; conclusion's context nor in its goal -- the core forsome-elim's condition.
(mi--rel! 'REL-BIG-UNION-MEM-ELIM "the kernel's big-union-mem-elim relates $2 to $3"
  (mi--ex '(mig_ mif_ mia_ mib_ mix_ mie_)
    (mi--and '(= mic_ (LIST mig_ mif_)) '(IN (ENC-IN mix_ (ENC-BU mia_ mib_)) mig_) '(NBG-OK mib_)
             '(IN mie_ NN) '(NOT (IN mie_ (UNION (CTX-FV mig_) (EXPR-FV mif_))))
             '(= mihs_ (LIST (LIST (CTX-ADD (CTX-ADD (DIFFERENCE mig_ (PAIR (ENC-IN mix_ (ENC-BU mia_ mib_))
                                                                        (ENC-IN mix_ (ENC-BU mia_ mib_))))
                                                     (ENC-IN (EFVAR mie_) mia_))
                                            (ENC-IN mix_ (EXPR-OPEN mib_ 0 (EFVAR mie_))))
                                   mif_))))))

;;; -----------------------------------------------------------------------
;;; 2. THE INDUCTION RULES (rule-checkers-logic.scm 1408-1522) and the catalog axioms they come from.

(def-constant 'ENC-NNC  '(enc-nnc-def  (== ENC-NNC  (ECONST 3))))
(def-constant 'ENC-ORDC '(enc-ordc-def (== ENC-ORDC (ECONST 5))))
(def-functoid 'ENC-SUCC  '(mip_) '(EAPP 30 (LIST mip_)))
(def-functoid 'ENC-SUCCO '(mip_) '(EAPP 31 (LIST mip_)))
(def-functoid 'ENC-ORDLT '(mip_ miq_) '(EAPP 10 (LIST (ECONST 7) mip_ miq_)))
(def-functoid 'ENC-LIMIT '(mip_) '(EAPP 10 (LIST (ECONST 9) mip_)))
(notation! 'ENC-NNC 'kind 'constant 'arity 0 'english "the encoded class NN")
(notation! 'ENC-ORDC 'kind 'constant 'arity 0 'english "the encoded class ORD")
(for-each (lambda (e) (notation! (car e) 'kind 'functoid 'arity (cadr e) 'english (caddr e)))
  '((ENC-SUCC 1 "the encoded successor of $1") (ENC-SUCCO 1 "the encoded ordinal successor of $1")
    (ENC-ORDLT 2 "the encoded ordinal order $1 < $2") (ENC-LIMIT 1 "the encoded LIMIT-ORD($1)")))

;; The catalog's class-form axioms, ENCODED (the class variable C is the outer binder; under the
;; inner binder C is the index 1, the inner variable the index 0).
;;  nn-induction (number-systems.scm 179-183):
;;    forall C. (0 in C and forall n. (n in NN and n in C) => succ n in C) => forall n. n in NN => n in C
(def-constant 'AX-NN-IND
  '(ax-nn-ind-def
     (== AX-NN-IND
         (ENC-ALL (ENC-IMP (ENC-AND (ENC-IN (ENC-NUM 0) (EBVAR 0))
                                    (ENC-ALL (ENC-IMP (ENC-AND (ENC-IN (EBVAR 0) ENC-NNC) (ENC-IN (EBVAR 0) (EBVAR 1)))
                                                      (ENC-IN (ENC-SUCC (EBVAR 0)) (EBVAR 1)))))
                           (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) ENC-NNC) (ENC-IN (EBVAR 0) (EBVAR 1)))))))))
;;  transfinite-induction (structure-library/ordinals.scm 226-235):
;;    forall C. (forall a. (a in ORD and forall b. ORD-LT(b, a) => b in C) => a in C) => forall a. a in ORD => a in C
(def-constant 'AX-TFI
  '(ax-tfi-def
     (== AX-TFI
         (ENC-ALL (ENC-IMP (ENC-ALL (ENC-IMP (ENC-AND (ENC-IN (EBVAR 0) ENC-ORDC)
                                                      (ENC-ALL (ENC-IMP (ENC-ORDLT (EBVAR 0) (EBVAR 1)) (ENC-IN (EBVAR 0) (EBVAR 2)))))
                                             (ENC-IN (EBVAR 0) (EBVAR 1))))
                           (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) ENC-ORDC) (ENC-IN (EBVAR 0) (EBVAR 1)))))))))
;;  membership-implies-sethood (library.scm 288):  forall x. forall C. x in C => x in SET
(def-constant 'AX-MEM-SET
  '(ax-mem-set-def
     (== AX-MEM-SET (ENC-ALL (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 1) (EBVAR 0)) (ENC-IN (EBVAR 1) ENC-SETC)))))))
(notation! 'AX-NN-IND 'kind 'constant 'arity 0 'english "the encoded axiom nn-induction")
(notation! 'AX-TFI 'kind 'constant 'arity 0 'english "the encoded axiom transfinite-induction")
(notation! 'AX-MEM-SET 'kind 'constant 'arity 0 'english "the encoded axiom membership-implies-sethood")
;;  class-extensionality (library.scm 309):  forall A. forall B. (forall x. x in A iff x in B) => A = B
;;  (A = index 2, B = index 1, x = index 0 under the innermost binder; A = index 1, B = index 0 outside it).
;;  Added 2026-10-21 (agent META-FUN): the COMP half of the stage-7 rewrite clause is derived from it
;;  (theorem-library/meta-ind-laws.scm, section M, der-comp-cr).
(def-constant 'AX-CLASS-EXT
  '(ax-class-ext-def
     (== AX-CLASS-EXT (ENC-ALL (ENC-ALL (ENC-IMP (ENC-ALL (ENC-IFF (ENC-IN (EBVAR 0) (EBVAR 2)) (ENC-IN (EBVAR 0) (EBVAR 1))))
                                                 (ENC-EQ (EBVAR 1) (EBVAR 0))))))))
(notation! 'AX-CLASS-EXT 'kind 'constant 'arity 0 'english "the encoded axiom class-extensionality")

;; 1408-1436 (nn-induction): the goal (FORALL n (IMPLIES (IN n NN) body)) with n outermost; two
;; hypotheses, the same context: the BASE body[n := 0] and the STEP
;; (FORALL n (IMPLIES (IN n NN) (IMPLIES body body[n := (succ n)]))).
;; The step substitutes a term that mentions the bound variable, which the locally nameless OPEN
;; does not express (OPEN replaces an index by a CLOSED term).  The step is therefore stated by its
;; openings, COFINITELY (Aydemir et al. 2008; phase 3's binder clauses): its body s opened at any
;; name y outside a finite set L is  y in NN => (body[y] => body[succ y]).  The kernel relation
;; implies this one with L = the free names of body (the names at which the opening of the named
;; step is the instance); nothing else is asserted.
(mi--rel! 'REL-NN-INDUCTION "the kernel's nn-induction relates $2 to $3"
  (mi--ex '(mig_ mip_ mis_ mifs_)
    (mi--and '(= mic_ (LIST mig_ (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) ENC-NNC) mip_))))
             '(= mihs_ (LIST (LIST mig_ (EXPR-OPEN mip_ 0 (ENC-NUM 0))) (LIST mig_ (ENC-ALL mis_))))
             '(IN mifs_ SET) '(SUBSET mifs_ NN) '(IN (CARD mifs_) NN)
             '(FORALL miy_ (IMPLIES (IN miy_ NN) (IMPLIES (NOT (IN miy_ mifs_))
                 (= (EXPR-OPEN mis_ 0 (EFVAR miy_))
                    (ENC-IMP (ENC-IN (EFVAR miy_) ENC-NNC)
                             (ENC-IMP (EXPR-OPEN mip_ 0 (EFVAR miy_)) (EXPR-OPEN mip_ 0 (ENC-SUCC (EFVAR miy_))))))))))))

;; 1468-1495 (transfinite-induction, with chk-tfi-beta / chk-tfi-goal-parts / chk-tfi-beta-ok?
;; 1443-1466): the goal (FORALL a (IMPLIES (IN a ORD) P)); one hypothesis, the same context:
;; (FORALL a (IMPLIES (AND (IN a ORD) (FORALL b (IMPLIES (ORD-LT b a) P[a := b]))) P)), b fresh for
;; P, the goal and the context.  In the encoding P[a := b] under the inner binder is P itself (its
;; index 0 is now b, and P mentions no outer index), ORD-LT(b, a) is ORD-LT(index 0, index 1), and
;; the freshness of b is vacuous: b is an index.
(mi--rel! 'REL-TRANSFINITE-INDUCTION "the kernel's transfinite-induction relates $2 to $3"
  (mi--ex '(mig_ mip_)
    (mi--and '(= mic_ (LIST mig_ (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) ENC-ORDC) mip_))))
             '(= mihs_ (LIST (LIST mig_ (ENC-ALL (ENC-IMP (ENC-AND (ENC-IN (EBVAR 0) ENC-ORDC)
                                                                  (ENC-ALL (ENC-IMP (ENC-ORDLT (EBVAR 0) (EBVAR 1)) mip_)))
                                                         mip_))))))))

;; 1497-1522 (transfinite-induction-3cases): the same goal; three hypotheses, the same context: the
;; BASE P[a := 0]; the SUCCESSOR case (FORALL a (IMPLIES (AND (IN a ORD) P) P[a := succ_ORD a]))
;; (cofinite, as nn-induction's step); the LIMIT case
;; (FORALL a (IMPLIES (AND (LIMIT-ORD a) (FORALL b (IMPLIES (ORD-LT b a) P[a := b]))) P)).
(mi--rel! 'REL-TFI-3CASES "the kernel's transfinite-induction-3cases relates $2 to $3"
  (mi--ex '(mig_ mip_ mis_ mifs_)
    (mi--and '(= mic_ (LIST mig_ (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) ENC-ORDC) mip_))))
             '(= mihs_ (LIST (LIST mig_ (EXPR-OPEN mip_ 0 (ENC-NUM 0)))
                             (LIST mig_ (ENC-ALL mis_))
                             (LIST mig_ (ENC-ALL (ENC-IMP (ENC-AND (ENC-LIMIT (EBVAR 0))
                                                                  (ENC-ALL (ENC-IMP (ENC-ORDLT (EBVAR 0) (EBVAR 1)) mip_)))
                                                         mip_)))))
             '(IN mifs_ SET) '(SUBSET mifs_ NN) '(IN (CARD mifs_) NN)
             '(FORALL miy_ (IMPLIES (IN miy_ NN) (IMPLIES (NOT (IN miy_ mifs_))
                 (= (EXPR-OPEN mis_ 0 (EFVAR miy_))
                    (ENC-IMP (ENC-AND (ENC-IN (EFVAR miy_) ENC-ORDC) (EXPR-OPEN mip_ 0 (EFVAR miy_)))
                             (EXPR-OPEN mip_ 0 (ENC-SUCCO (EFVAR miy_)))))))))))

;;; THE PREDICATIVE INDUCTIONS (agent METACORE, 2026-10-29).  The three kernel relations above transcribe
;;; checkers that accept ANY body P: rule-checkers-logic.scm (a320cb6f) puts no predicativity condition on
;;; nn-induction, transfinite-induction or transfinite-induction-3cases.  Over the NBG core (meta-core.scm
;;; 4.3a) an induction is derived through the comprehension of its body (CR-DEF-COMP, CR-COMP-MEM), so it is
;;; admissible for a PREDICATIVE body only.  The three relations below are the kernel's with the conjunct
;;; NBG-OK(P) added; the admissibility theorems (meta-ind-laws.scm F, K; meta-def-laws.scm s.4) are stated
;;; for them.  The induction steps the kernel takes at an impredicative body are outside the encoded core:
;;; METACORE report, finding 2.
(mi--rel! 'REL-NN-INDUCTION-NBG "the kernel's nn-induction at a predicative body relates $2 to $3"
  (mi--ex '(mig_ mip_ mis_ mifs_)
    (mi--and '(= mic_ (LIST mig_ (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) ENC-NNC) mip_)))) '(NBG-OK mip_)
             '(= mihs_ (LIST (LIST mig_ (EXPR-OPEN mip_ 0 (ENC-NUM 0))) (LIST mig_ (ENC-ALL mis_))))
             '(IN mifs_ SET) '(SUBSET mifs_ NN) '(IN (CARD mifs_) NN)
             '(FORALL miy_ (IMPLIES (IN miy_ NN) (IMPLIES (NOT (IN miy_ mifs_))
                 (= (EXPR-OPEN mis_ 0 (EFVAR miy_))
                    (ENC-IMP (ENC-IN (EFVAR miy_) ENC-NNC)
                             (ENC-IMP (EXPR-OPEN mip_ 0 (EFVAR miy_)) (EXPR-OPEN mip_ 0 (ENC-SUCC (EFVAR miy_))))))))))))
(mi--rel! 'REL-TRANSFINITE-INDUCTION-NBG "the kernel's transfinite-induction at a predicative body relates $2 to $3"
  (mi--ex '(mig_ mip_)
    (mi--and '(= mic_ (LIST mig_ (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) ENC-ORDC) mip_)))) '(NBG-OK mip_)
             '(= mihs_ (LIST (LIST mig_ (ENC-ALL (ENC-IMP (ENC-AND (ENC-IN (EBVAR 0) ENC-ORDC)
                                                                  (ENC-ALL (ENC-IMP (ENC-ORDLT (EBVAR 0) (EBVAR 1)) mip_)))
                                                         mip_))))))))
(mi--rel! 'REL-TFI-3CASES-NBG "the kernel's transfinite-induction-3cases at a predicative body relates $2 to $3"
  (mi--ex '(mig_ mip_ mis_ mifs_)
    (mi--and '(= mic_ (LIST mig_ (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) ENC-ORDC) mip_)))) '(NBG-OK mip_)
             '(= mihs_ (LIST (LIST mig_ (EXPR-OPEN mip_ 0 (ENC-NUM 0)))
                             (LIST mig_ (ENC-ALL mis_))
                             (LIST mig_ (ENC-ALL (ENC-IMP (ENC-AND (ENC-LIMIT (EBVAR 0))
                                                                  (ENC-ALL (ENC-IMP (ENC-ORDLT (EBVAR 0) (EBVAR 1)) mip_)))
                                                         mip_)))))
             '(IN mifs_ SET) '(SUBSET mifs_ NN) '(IN (CARD mifs_) NN)
             '(FORALL miy_ (IMPLIES (IN miy_ NN) (IMPLIES (NOT (IN miy_ mifs_))
                 (= (EXPR-OPEN mis_ 0 (EFVAR miy_))
                    (ENC-IMP (ENC-AND (ENC-IN (EFVAR miy_) ENC-ORDC) (EXPR-OPEN mip_ 0 (EFVAR miy_)))
                             (EXPR-OPEN mip_ 0 (ENC-SUCCO (EFVAR miy_)))))))))))

;;; -----------------------------------------------------------------------
;;; 3. THE STRUCTURAL RULES NOT YET TRANSCRIBED (union, intersection and tuples intro / elim are
;;; meta-core.scm's, section 6, with their admissibility theorems in meta-core-laws.scm, section J).
;;; A kernel CARTESIAN has at least one argument: make-wff refuses an application with no argument
;;; (wff.scm, walk-term), which is the conjunct (<= 1 (LENGTH a)).

;; rule-checkers-logic.scm 1160-1182 (cartesian-intro): the goal (IN (LIST e1 .. en) (CARTESIAN A1 ..
;; An)), the two lists of one length; one hypothesis per component, the same context, (IN e_i A_i).
(mi--rel! 'REL-CARTESIAN-INTRO "the kernel's cartesian-intro relates $2 to $3"
  (mi--ex '(mig_ mie_ mia_)
    (mi--and '(= mic_ (LIST mig_ (ENC-IN (ENC-LIST mie_) (ENC-CART mia_))))
             '(= (LENGTH mie_) (LENGTH mia_)) '(<= 1 (LENGTH mia_))
             '(= (LENGTH mihs_) (LENGTH mie_))
             '(FORALL mii_ (IMPLIES (IN mii_ NN) (IMPLIES (<= 1 mii_) (IMPLIES (<= mii_ (LENGTH mie_))
                 (= (NTH mii_ mihs_) (LIST mig_ (ENC-IN (NTH mii_ mie_) (NTH mii_ mia_)))))))))))

;; 1184-1210 (cartesian-elim k): some (IN (LIST e1 .. en) (CARTESIAN A1 .. An)) in the conclusion
;; context, the lists of one length, 1 <= k <= n; one hypothesis, the same goal, the context gains
;; (IN e_k A_k) (the membership stays).
(mi--rel! 'REL-CARTESIAN-ELIM "the kernel's cartesian-elim relates $2 to $3"
  (mi--ex '(mig_ mif_ mie_ mia_ mik_)
    (mi--and '(= mic_ (LIST mig_ mif_)) '(IN (ENC-IN (ENC-LIST mie_) (ENC-CART mia_)) mig_)
             '(= (LENGTH mie_) (LENGTH mia_)) '(IN mik_ NN) '(<= 1 mik_) '(<= mik_ (LENGTH mie_))
             '(= mihs_ (LIST (LIST (CTX-ADD mig_ (ENC-IN (NTH mik_ mie_) (NTH mik_ mia_))) mif_))))))

;; The two DECOMPOSES (rule-checkers-rewrite.scm 910-1013, registered 1020-1021) are rewrites at SOME
;; positions of the goal, through the macete walk rkw--walk (rule-checkers-rewrite.scm, the same
;; walk as `macete', with the local contexts it computes; neither explainer reads the context).  They
;; are encoded, as phase 3 encoded the reduction rules, in ONE-POSITION form: REL-REWRITE-1
;; (meta-cr.scm, section 4) over a set of justification tuples [2, g, A, B].  The kernel relation at
;; several positions is the one-position relation iterated (both explainers are context-free, so the
;; simultaneous and the sequential readings agree: META-3 report 6.4).
;;
;; cartesian-decompose (910-981): A = (IN x (CARTESIAN A1 .. An)), n >= 1, B = the chain
;;   (FORSOME v1 (AND (IN v1 A1) .. (FORSOME vn (AND (IN vn An) (= x (LIST v1 .. vn))))..))
;; with the v_i distinct and free in neither x nor any A_j.  In the encoding the v_i are indices:
;; under the k-th binder v_j is the index k - j, so the innermost list is [n-1, .., 0] of EBVARs; x and
;; the A_j are locally closed, so they need no shift, and the freshness condition is vacuous.
(def-functoid 'IDX-LIST '(min_)
  '(IOTA mir_ (AND (IN mir_ (TUPLES SET))
                   (AND (= (LENGTH mir_) min_)
                        (FORALL mii_ (IMPLIES (IN mii_ NN) (IMPLIES (<= 1 mii_) (IMPLIES (<= mii_ min_)
                                     (= (NTH mii_ mir_) (EBVAR (- min_ mii_)))))))))))
(notation! 'IDX-LIST 'kind 'functoid 'arity 1 'english "the list of the indices $1 - 1, .., 0")
;; ENC-CCH(x, a, n, k): the chain over the LAST k of the n entries of a (built from the inside out).
(def-by-nn-recursion 'ENC-CCH '(mix_ mia_ min_) '(ENC-EQ mix_ (ENC-LIST (IDX-LIST min_))) '(mik_ miv_)
  '(ENC-EX (ENC-AND (ENC-IN (EBVAR 0) (NTH (- min_ mik_) mia_)) miv_)))
(notation! 'ENC-CCH 'kind 'functoid 'arity 4 'english "the existential chain of $1 in the last $4 of the $3 entries of $2")
;; NBGSEP (2026-10-25): miz_ and mia_ bounded by (IN v SET) -- components of the tuple
;; equated to mix_ (through the ENC-IN / ENC-CART codes), sets by the list doctrine; mig_
;; is bounded by CTX-SET.  The meaning is unchanged and the separation is predicative.
(def-functoid 'J-CART '(mit_)
  '(SEP mix_ RW-UNIV
     (FORSOME mig_ (FORSOME miz_ (FORSOME mia_
       (AND (IN miz_ SET) (AND (IN mia_ SET)
       (AND (= mix_ (LIST 2 mig_ (ENC-IN miz_ (ENC-CART mia_)) (ENC-CCH miz_ mia_ (LENGTH mia_) (LENGTH mia_))))
            (AND (IN mig_ CTX-SET) (<= 1 (LENGTH mia_)))))))))))
(notation! 'J-CART 'kind 'functoid 'arity 1 'english "the local instances of cartesian-decompose")
;; ROW 57, STATUS (agent W2B, 2026-11-10; the user's decision of 2026-11-10, the core-schema route).  The fact the
;; core lacked for the forward direction, tuple eta, is admitted as the core schema CR-TUPLE-ETA
;; (structure-library/meta-core.scm 4.11).  The admissibility of this relation -- J-CART(T) inside EQV(T), as
;; j-teq-sub for row 58 -- is NOT yet proven: both directions read the chain ENC-CCH under its binders, and the
;; core-side calculus for that (EXPR-OPEN of ENC-CCH and of IDX-LIST, the denotation of IDX-LIST, the n-fold
;; forsome-intro at the projections and the n-fold forsome-elim at fresh names) is not written.  W2B report.
(def-predicate 'REL-CARTESIAN-DECOMPOSE-1 '(mit_ mihs_ mic_) '(REL-REWRITE-1 (J-CART mit_) mihs_ mic_))
(notation! 'REL-CARTESIAN-DECOMPOSE-1 'kind 'predicate 'arity 3 'english "the kernel's cartesian-decompose, at one position, relates $2 to $3")

;; tuple-equality-decompose, RE-TRANSCRIBED 2026-10-29 (agent METACORE) against rule-checkers-rewrite.scm of a320cb6f
;; (rkw--tuple-explainer, the LIST DEFINEDNESS paragraph above it; repair R4 of 2026-10-12): A = (= (LIST a1 .. an)
;; (LIST b1 .. bn)), both LIST forms of one length; B = the RIGHT-nested conjunction of the a_i = b_i (n = 0: TRUTH;
;; n = 1: (= a1 b1)); and BOTH LISTS DENOTE in the local context -- certified there, or owed as a hypothesis
;; Gamma => L = L.  (The two sides are sentences: the kernel's formulas are well formed by construction, make-wff,
;; the conjuncts CLF as in J-UDEC.)  The transcription of 2026-10-12 (META-4) read "NO definedness condition on either list" and was
;; FALSE (META-4 report s.5.4): [SET] = [SET] is false while SET = SET is true.  The two premises are the two
;; DERIVABLE conjuncts of J-TEQ (the local context's sequents, as J-NTH reads its list's definedness).  The right
;; fold is the least set TF-SET(a, b) of pairs [j, f], f the right fold of the equations a_(j+1) = b_(j+1) ..
;; a_n = b_n (the base [n - 1, a_n = b_n], the step from [j + 1, f] to [j, (a_(j+1) = b_(j+1)) and f]), as RF-SET
;; (meta-def.scm 10) folds memberships; the kernel's B is the f of [0, f], or TRUTH when n = 0.  (It replaces the
;; recursion ENC-TCJ of 2026-10-12, which counted from the end by subtraction; nothing cited either.)
(def-predicate 'TF-CLOSED '(mitfa_ mitfb_ mitfs_)
  '(AND (FORALL mitfj_ (IMPLIES (IN mitfj_ NN) (IMPLIES (= (succ mitfj_) (LENGTH mitfa_))
           (IN (LIST mitfj_ (ENC-EQ (NTH (succ mitfj_) mitfa_) (NTH (succ mitfj_) mitfb_))) mitfs_))))
        (FORALL mitfk_ (FORALL mitff_ (IMPLIES (IN mitfk_ NN) (IMPLIES (IN (LIST (succ mitfk_) mitff_) mitfs_)
           (IN (LIST mitfk_ (ENC-AND (ENC-EQ (NTH (succ mitfk_) mitfa_) (NTH (succ mitfk_) mitfb_)) mitff_)) mitfs_)))))))
(notation! 'TF-CLOSED 'kind 'predicate 'arity 3 'english "$3 is closed under the right folds of the component equations of $1 and $2")
(def-functoid 'TF-SET '(mitfa_ mitfb_)
  '(SEP mitfp_ (CARTESIAN NN EXPR-SET) (FORALL mitfw_ (IMPLIES (IN mitfw_ (POWER (CARTESIAN NN EXPR-SET)))
      (IMPLIES (TF-CLOSED mitfa_ mitfb_ mitfw_) (IN mitfp_ mitfw_))))))
(notation! 'TF-SET 'kind 'functoid 'arity 2 'english "the right folds of the component equations of $1 and $2 from an index on")
(def-functoid 'J-TEQ '(mit_)
  '(SEP mix_ RW-UNIV
     (FORSOME mig_ (FORSOME mia_ (FORSOME mib_ (FORSOME mif_
       (AND (IN mia_ SET) (AND (IN mib_ SET) (AND (IN mif_ SET)
       (AND (= mix_ (LIST 2 mig_ (ENC-EQ (ENC-LIST mia_) (ENC-LIST mib_)) mif_))
            (AND (IN mig_ CTX-SET) (AND (= (LENGTH mia_) (LENGTH mib_))
            (AND (IN (ENC-EQ (ENC-LIST mia_) (ENC-LIST mib_)) CLF) (AND (IN mif_ CLF)
            (AND (OR (AND (= (LENGTH mia_) 0) (= mif_ ENC-TRUTH)) (IN (LIST 0 mif_) (TF-SET mia_ mib_)))
            (AND (IN (LIST mig_ (ENC-EQ (ENC-LIST mia_) (ENC-LIST mia_))) (DERIVABLE mit_))
                 (IN (LIST mig_ (ENC-EQ (ENC-LIST mib_) (ENC-LIST mib_))) (DERIVABLE mit_))))))))))))))))))
(notation! 'J-TEQ 'kind 'functoid 'arity 1 'english "the local instances of tuple-equality-decompose, both lists denoting")
(def-predicate 'REL-TUPLE-EQ-DECOMPOSE-1 '(mit_ mihs_ mic_) '(REL-REWRITE-1 (J-TEQ mit_) mihs_ mic_))
(notation! 'REL-TUPLE-EQ-DECOMPOSE-1 'kind 'predicate 'arity 3 'english "the kernel's tuple-equality-decompose, at one position, relates $2 to $3")
(def-predicate 'REL-TUPLE-EQ-DECOMPOSE-7 '(mit_ mihs_ mic_) '(REL-REWRITE-7 (J-TEQ mit_) mihs_ mic_))
(notation! 'REL-TUPLE-EQ-DECOMPOSE-7 'kind 'predicate 'arity 3 'english "the kernel's tuple-equality-decompose, at one position at any stage, relates $2 to $3")

;;; -----------------------------------------------------------------------
;;; 4. TWO DEFINEDNESS CLAUSES (design note 4.7, phase 5), stated as closure properties of DERIVABLE.
;;; The core certifies no compound term as defined: reflexivity fires on a name or a constant only,
;;; and forall-elim / forsome-intro owe  Gamma |- t = t.  The kernel's certificate pi--defined?
;;; accepts a comprehension unconditionally (primitive-inferences.scm, the COMP clause) and a term
;;; occurring in a true strict atom of the context (the strictness clause).  Phase 5 is to add these
;;; clauses to the core as rules DEF-k; until then a phase-4 theorem that needs one carries it as a
;;; hypothesis on T, by name:
;;;   DEF-COMP-CLOSED(T):  every comprehension that is a closed term is derivably defined, in every context;
;;;   DEF-IN-CLOSED(T):    a term derivably a member of something is derivably defined (strictness of IN).
;;   (2026-10-29, agent METACORE: DEF-COMP-CLOSED speaks of a PREDICATIVE comprehension only, NBG-OK(q),
;;   as CR-DEF-COMP does since that day.)
(def-predicate 'DEF-COMP-CLOSED '(mit_)
  '(FORALL mig_ (FORALL miq_ (IMPLIES (IN mig_ CTX-SET) (IMPLIES (IN (ENC-COMP miq_) CLT) (IMPLIES (NBG-OK miq_)
     (IN (LIST mig_ (ENC-EQ (ENC-COMP miq_) (ENC-COMP miq_))) (DERIVABLE mit_))))))))
(notation! 'DEF-COMP-CLOSED 'kind 'predicate 'arity 1 'english "every closed predicative comprehension is derivably defined over $1")
(def-predicate 'DEF-IN-CLOSED '(mit_)
  '(FORALL mig_ (FORALL miw_ (FORALL mia_ (IMPLIES (IN (LIST mig_ (ENC-IN miw_ mia_)) (DERIVABLE mit_))
     (IN (LIST mig_ (ENC-EQ miw_ miw_)) (DERIVABLE mit_)))))))
(notation! 'DEF-IN-CLOSED 'kind 'predicate 'arity 1 'english "a derivable member is derivably defined over $1")

;;; -----------------------------------------------------------------------
;;; 5. Two more catalog axioms, encoded, for nn-induction's derivation:
;;;  nn-zero-in (number-systems.scm 128):     0 in NN
;;;  nn-succ-closed (number-systems.scm 130): forall n. n in NN => succ n in NN
(def-constant 'AX-ZERO-NN '(ax-zero-nn-def (== AX-ZERO-NN (ENC-IN (ENC-NUM 0) ENC-NNC))))
(def-constant 'AX-SUCC-NN
  '(ax-succ-nn-def (== AX-SUCC-NN (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) ENC-NNC) (ENC-IN (ENC-SUCC (EBVAR 0)) ENC-NNC))))))
(notation! 'AX-ZERO-NN 'kind 'constant 'arity 0 'english "the encoded axiom nn-zero-in")
(notation! 'AX-SUCC-NN 'kind 'constant 'arity 0 'english "the encoded axiom nn-succ-closed")

;;; -----------------------------------------------------------------------
;;; 6. (META-5, 2026-10-12) Two more catalog axioms, encoded, for transfinite-induction-3cases:
;;;  limit-ord-iff (ordinals.scm 124):   forall l. LIMIT-ORD(l) iff (l in ORD and l /= 0 and
;;;                                        not exists a. (a in ORD and l = succ_ORD(a)))
;;;  ord-succ-above (ordinals.scm 92):   forall a. a in ORD => ORD-LT(a, succ_ORD(a))
(def-constant 'AX-LIMIT-IFF
  '(ax-limit-iff-def
     (== AX-LIMIT-IFF
         (ENC-ALL (ENC-IFF (ENC-LIMIT (EBVAR 0))
                           (ENC-AND (ENC-IN (EBVAR 0) ENC-ORDC)
                                    (ENC-AND (ENC-NOT (ENC-EQ (EBVAR 0) (ENC-NUM 0)))
                                             (ENC-NOT (ENC-EX (ENC-AND (ENC-IN (EBVAR 0) ENC-ORDC)
                                                                       (ENC-EQ (EBVAR 1) (ENC-SUCCO (EBVAR 0)))))))))))))
(def-constant 'AX-ORD-SUCC-ABOVE
  '(ax-ord-succ-above-def
     (== AX-ORD-SUCC-ABOVE (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) ENC-ORDC) (ENC-ORDLT (EBVAR 0) (ENC-SUCCO (EBVAR 0))))))))
(notation! 'AX-LIMIT-IFF 'kind 'constant 'arity 0 'english "the encoded axiom limit-ord-iff")
(notation! 'AX-ORD-SUCC-ABOVE 'kind 'constant 'arity 0 'english "the encoded axiom ord-succ-above")
