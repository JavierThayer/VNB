;;; meta-nbg.scm -- K2, agent METACORE (2026-10-29): the kernel forms of the ten C+ rows of the K2 ledger
;;; (scratchpad/K2-LEDGER.md of ~/prover-mf, section 1, rows 8, 10, 11, 13, 14, 15, 24, 26, 27, 51), TRANSCRIBED
;;; from their checkers of a320cb6f.  DEFINITIONS ONLY; the laws (the BRIDGES: each kernel form admissible over the
;;; core) are in theorem-library/meta-nbg-laws.scm, with the NBG controls of meta-core.scm 4.3a and the
;;; admissibility of the rules of rows 49 and 58.
;;; Conventions as structure-library/meta-ind.scm: a kernel sequent is well formed by construction, the conjunct
;;; (IN c SEQ-SET); contexts are compared as SETS, so "the context with f replaced by a, b" is the set equation
;;; CTX-ADD(CTX-ADD(DIFFERENCE(g, {f}), a), b); a named substitution p[x := t] is EXPR-OPEN(p, 0, t).
;;; THE DEFINEDNESS A CHECKER READS OFF THE CONTEXT (pi--defined?, chk-elim-certified?) is encoded as the
;;; CONTEXT CERTIFICATE: some member h of the context is in CERT-SET(T, g, t) (meta-def.scm section 8), the least
;;; set of sentences that certify t (a strict atom, a sentence made true, an opened existential, a predicate or
;;; class hypothesis through its definition).  The clauses of the certificate that read no context formula (a total
;;; constructor on certified arguments, a list of sets, a binder over a certified domain, ...) are the DEF rows of
;;; the K2 ledger's table 2, each admissible on its own; they are not restated here.
;;; Binders: mnk*_.

(define (mnk--ex vars body)
  (if (null? vars) body `(FORSOME ,(car vars) ,(mnk--ex (cdr vars) body))))
(define (mnk--and . fs)
  (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(apply mnk--and (cdr fs)))))
(define (mnk--rel! name note body)
  (def-predicate name '(mnkt_ mnkhs_ mnkc_) (mnk--and '(IN mnkc_ SEQ-SET) body))
  (notation! name 'kind 'predicate 'arity 3 'english note))
;; the context g with the formula f removed
(define (mnk--minus f) `(DIFFERENCE mnkg_ (PAIR ,f ,f)))

;; ROW 10. rule-checkers-logic.scm (and-elim): some (AND a b) in the context REPLACED by a and b; the same goal.
(mnk--rel! 'REL-AND-ELIM-K "the kernel's and-elim relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnka_ mnkb_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (ENC-AND mnka_ mnkb_) mnkg_)
              `(= mnkhs_ (LIST (LIST (CTX-ADD (CTX-ADD ,(mnk--minus '(ENC-AND mnka_ mnkb_)) mnka_) mnkb_) mnkf_))))))

;; ROW 11. (or-elim): some (OR a b) in the context replaced, in two branches, by a and by b; the same goal.
(mnk--rel! 'REL-OR-ELIM-K "the kernel's or-elim relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnka_ mnkb_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (ENC-OR mnka_ mnkb_) mnkg_)
              `(= mnkhs_ (LIST (LIST (CTX-ADD ,(mnk--minus '(ENC-OR mnka_ mnkb_)) mnka_) mnkf_)
                               (LIST (CTX-ADD ,(mnk--minus '(ENC-OR mnka_ mnkb_)) mnkb_) mnkf_))))))

;; ROW 13. (iff-elim): some (IFF a b) in the context replaced by (IMPLIES a b) and (IMPLIES b a).
(mnk--rel! 'REL-IFF-ELIM-K "the kernel's iff-elim relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnka_ mnkb_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (ENC-IFF mnka_ mnkb_) mnkg_)
              `(= mnkhs_ (LIST (LIST (CTX-ADD (CTX-ADD ,(mnk--minus '(ENC-IFF mnka_ mnkb_)) (ENC-IMP mnka_ mnkb_))
                                              (ENC-IMP mnkb_ mnka_))
                                     mnkf_))))))

;; ROW 14. (forsome-elim): some (FORSOME x p) in the context REPLACED by p[x := y], y an eigenvariable free in
;; nothing else: not in the rest of the context, not in the goal, not in the existential itself.
(mnk--rel! 'REL-FORSOME-ELIM-K "the kernel's forsome-elim relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkb_ mnky_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (ENC-EX mnkb_) mnkg_) '(IN mnky_ NN)
              `(NOT (IN mnky_ (UNION (CTX-FV ,(mnk--minus '(ENC-EX mnkb_))) (UNION (EXPR-FV mnkf_) (EXPR-FV (ENC-EX mnkb_))))))
              `(= mnkhs_ (LIST (LIST (CTX-ADD ,(mnk--minus '(ENC-EX mnkb_)) (EXPR-OPEN mnkb_ 0 (EFVAR mnky_))) mnkf_))))))

;; ROW 8. (forsome-intro, chk-instance-certifies?): the goal (FORSOME x p); one hypothesis, the same context,
;; p[x := t]; NO definedness sequent, the witness certified -- by the instance itself (a sentence it makes true
;; is a strict atom certifying t: TRUE-REACH, STRICT-ATOM of meta-def.scm 5; the kernel reads the top-level
;; conjuncts, a subset) or by the context (the context certificate).
(mnk--rel! 'REL-FORSOME-INTRO-K "the kernel's forsome-intro with a certified witness relates $2 to $3"
  (mnk--ex '(mnkg_ mnkb_ mnktm_)
    (mnk--and '(= mnkc_ (LIST mnkg_ (ENC-EX mnkb_))) '(IN mnktm_ CLT)
              '(= mnkhs_ (LIST (LIST mnkg_ (EXPR-OPEN mnkb_ 0 mnktm_))))
              '(OR (FORSOME mnkf2_ (AND (IN mnkf2_ (TRUE-REACH (EXPR-OPEN mnkb_ 0 mnktm_))) (STRICT-ATOM mnkf2_ mnktm_)))
                   (FORSOME mnkh_ (AND (IN mnkh_ mnkg_) (IN mnkh_ (CERT-SET mnkt_ mnkg_ mnktm_))))))))

;; ROW 15. (forall-elim, chk-elim-certified?): some (FORALL x p) in the context; one hypothesis, the same goal,
;; the context gaining p[x := t]; NO definedness sequent, t certified by the context.
(mnk--rel! 'REL-FORALL-ELIM-K "the kernel's forall-elim at a certified term relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkb_ mnktm_ mnkh_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (ENC-ALL mnkb_) mnkg_) '(IN mnktm_ CLT)
              '(IN mnkh_ mnkg_) '(IN mnkh_ (CERT-SET mnkt_ mnkg_ mnktm_))
              '(= mnkhs_ (LIST (LIST (CTX-ADD mnkg_ (EXPR-OPEN mnkb_ 0 mnktm_)) mnkf_))))))

;; ROW 24. (reflexivity): the goal t = t, no hypothesis, t certified by the context.
(mnk--rel! 'REL-REFLEXIVITY-K "the kernel's reflexivity at a certified term relates $2 to $3"
  (mnk--ex '(mnkg_ mnktm_ mnkh_)
    (mnk--and '(= mnkc_ (LIST mnkg_ (ENC-EQ mnktm_ mnktm_))) '(IN mnktm_ CLT)
              '(IN mnkh_ mnkg_) '(IN mnkh_ (CERT-SET mnkt_ mnkg_ mnktm_)) '(= mnkhs_ (LIST)))))

;; ROWS 26, 27. (if-true / if-false through pi--if-equation, primitive-inferences.scm): two hypotheses, the
;; condition (its negation) and the main branch gaining the STRICT equation (IF p a b) = a (= b), the branch a
;; (b) certified by the context.  (When it is not certified the kernel hands over the quasi-equation, which is
;; CR-IF-TRUE / CR-IF-FALSE itself.)
(mnk--rel! 'REL-IF-TRUE-K "the kernel's if-true at a certified branch relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkp_ mnka_ mnkb_ mnkh_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN mnkh_ mnkg_) '(IN mnkh_ (CERT-SET mnkt_ mnkg_ mnka_))
              '(IN (ENC-IF mnkp_ mnka_ mnkb_) CLT) '(IN mnka_ CLT) '(IN mnkb_ CLT)
              '(= mnkhs_ (LIST (LIST mnkg_ mnkp_)
                               (LIST (CTX-ADD mnkg_ (ENC-EQ (ENC-IF mnkp_ mnka_ mnkb_) mnka_)) mnkf_))))))
(mnk--rel! 'REL-IF-FALSE-K "the kernel's if-false at a certified branch relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkp_ mnka_ mnkb_ mnkh_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN mnkh_ mnkg_) '(IN mnkh_ (CERT-SET mnkt_ mnkg_ mnkb_))
              '(IN (ENC-IF mnkp_ mnka_ mnkb_) CLT) '(IN mnka_ CLT) '(IN mnkb_ CLT)
              '(= mnkhs_ (LIST (LIST mnkg_ (ENC-NOT mnkp_))
                               (LIST (CTX-ADD mnkg_ (ENC-EQ (ENC-IF mnkp_ mnka_ mnkb_) mnkb_)) mnkf_))))))

;; ROW 51. rule-checkers-schema.scm (rcs-iota-in-elim, rcs--context-defines?): one hypothesis, the same goal, the
;; context gaining p[x := IOTA x. p]; the context establishes that the description denotes: a membership
;; (IN (IOTA x p) A) or an equation naming it, (= (IOTA x p) u) or (= u (IOTA x p)), is in the context.
(mnk--rel! 'REL-IOTA-IN-ELIM-K "the kernel's iota-in-elim relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkp_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_))
              '(OR (FORSOME mnka_ (IN (ENC-IN (ENC-IOTA mnkp_) mnka_) mnkg_))
                   (FORSOME mnku_ (OR (IN (ENC-EQ (ENC-IOTA mnkp_) mnku_) mnkg_) (IN (ENC-EQ mnku_ (ENC-IOTA mnkp_)) mnkg_))))
              '(= mnkhs_ (LIST (LIST (CTX-ADD mnkg_ (EXPR-OPEN mnkp_ 0 (ENC-IOTA mnkp_))) mnkf_))))))
