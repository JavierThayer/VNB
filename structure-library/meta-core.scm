;;; meta-core.scm -- THE CORE OF K2: well-formedness, sequents, the core rule relations,
;;; DERIVABLE, and the eight kernel relations transcribed (three in phase 2, five by META-KIT).
;;; (docs/meta-k2-admissibility-2026-10-08.md, sections 3, 4 and 5, phase 2.)
;;; DEFINITIONS ONLY; the laws are in theorem-library/meta-core-laws.scm.
;;; Agent META-2, 2026-10-08.  Builds on structure-library/meta-syntax.scm (phase 1), which it
;;; does not edit.  Every binder and parameter here is an mc*_ name.
;;;
;;; 1. THE HEAD TABLE.  Head codes are NUMERALS, not def-constants: two codes are told apart
;;;    by `arith' (3 /= 5), with no table of distinctness laws, exactly as phase 1 told the node
;;;    tags apart.  A def-constant per head would cost one unfold theorem and one distinctness
;;;    fact per pair.  The table (the translator of K3 must mirror it):
;;;
;;;      APP heads (node [3, h, l]):                   BIND heads (node [4, h, nb, a, b]):
;;;        0 TRUTH        arity 0  -> formula            20 FORALL      nb 1, a = []     body formula -> formula
;;;        1 FALSITY      arity 0  -> formula            21 FORSOME     nb 1, a = []     body formula -> formula
;;;        2 NOT          1 formula -> formula           22 SEP         nb 1, a = [A]    body formula -> term
;;;        3 AND  4 OR  5 IMPLIES  6 IFF                 23 COMP        nb 1, a = []     body formula -> term
;;;                       2 formulas -> formula          24 BIG-UNION   nb 1, a = [A]    body term    -> term
;;;        7 IN  8 =  9 ==  2 terms -> formula           25 IOTA        nb 1, a = []     body formula -> term
;;;       10 a PREDICATE application: any arity,         26 VNB-LAMBDA  nb 1, a = [A]    body term    -> term
;;;          terms -> formula (the first argument        27 IF          nb 0, a = [t1, t2] body formula -> term
;;;          a CONST naming the predicate)                  (IF p t1 t2 is a binder of NO variable:
;;;      >= 11 TERM heads, any arity, terms -> term:          its two branches are the outside list,
;;;         11 UNION 12 INTERSECTION 13 CARTESIAN             its condition the body, so the one
;;;         14 TUPLES 15 NTH 16 LENGTH 17 LIST                position of mixed kind is the body)
;;;         18 APPLY (set-function application f(a ..))
;;;         19 FUN; 30 and above: the named term constants (PAIR, succ, +, a functoid name ...)
;;;    CONST codes (node [2, c]): an EVEN code 2k is the numeral k (ENC-NUM); an ODD code is a
;;;    named constant, 1 = SET (ENC-SETC); the others (NN, RR, EMPTY-SET ...) are the
;;;    translator's to assign.  An odd code is either a TERM constant or a PREDICATE NAME (the
;;;    first argument of a head-10 atom); PRED-CODE (section 4.7, (8)) lists the predicate names:
;;;    7 ORD-LT, 9 LIMIT-ORD (meta-ind.scm), 11 <=, 13 < (meta-def.scm).  (META-10, 2026-10-17.)
;;;    The arity of the term heads >= 11 is NOT checked (TUPLES with three arguments is WF): the
;;;    schemas of the core name each head at its intended arity, so a mis-arity term is an
;;;    uninterpreted term no rule speaks of.  The connectives and relations are checked exactly.
;;;
;;; 2. WELL-FORMEDNESS (the phase-1 device: a map per stage with the KEEP clause, read at the
;;;    shared EXPR-RANK).  The value is a SET OF KINDS, 1 = term, 2 = formula, so that the APP and
;;;    BIND cases are SEPs over NN whose conditions name the children through MAKE-SET (the shape
;;;    of LCD, whose congruence driver applies unchanged):
;;;      WKS(FVAR n) = WKS(BVAR k) = WKS(CONST c) = {1}
;;;      WKS(APP h l)        = { kk | kk = HD-RES(h), APP-AR-OK(h, |l|), every child has kind HD-ARGK(h) }
;;;      WKS(BIND h nb a b)  = { kk | kk = HD-BRES(h), BIND-SIG(h, nb, |a|), every outside child has
;;;                                   kind 1, the body has kind HD-BODY(h) }
;;;    WF-TERM(e) is 1 in WKS(e), WF-FML(e) is 2 in WKS(e).  A node has at most one kind.
;;;    CLF (the sentences of the object language) = the WF formulas that are LOCALLY CLOSED (free
;;;    names allowed, no dangling index); CLT likewise for terms.
;;;
;;; 3. SEQUENTS.  CTX-SET = the FINITE subsets of CLF (carved out of POWER(CLF), so a SET);
;;;    SEQ-SET = CTX-SET x CLF; a sequent is the 2-list [Gamma, G]; Gamma + A is CTX-ADD(Gamma, A) =
;;;    Gamma u {A}; CTX-FV(Gamma) is the union of the free names of its members.
;;;
;;; 4. THE CORE RELATIONS CR-<NAME>(T, hs, c): T a set of formulas, hs a LIST of sequents, c a
;;;    sequent.  The core is the design note's (4.1-4.6), NOT the kernel checkers'; where the
;;;    note's wording is unsound or unencodable the relation below departs from it and the
;;;    departure is marked DEPARTS.  The elimination rules are stated KEEPING the eliminated
;;;    formula (the kernel's "replace" forms follow by weakening).  The well-formedness of the
;;;    conclusion is required once, in CORE-CLOSED (c in SEQ-SET), not in each relation.
;;;
;;; 5. CORE-RULE(T, hs, c) is the DISJUNCTION of the relations: a disjunction because a closure
;;;    theorem per relation is then one `prop' step from the relation to CORE-RULE (a tagged form
;;;    [tag, hs, c] would need a tag equation per relation and buys nothing here).
;;;    CORE-CLOSED(T, S): every instance with its hypotheses in S and its conclusion in SEQ-SET has its
;;;    conclusion in S.  DERIVABLE(T) is the intersection of the CORE-CLOSED subsets of SEQ-SET
;;;    (SUBTERM-REL's device, strand-messages.scm).
;;;
;;; Dependencies: structure-library/meta-syntax (EXPR-SET, the constructors, EXPR-FV, EXPR-SUBST,
;;; EXPR-OPEN, EXPR-LC, EXPR-RANK, EXPR-STAGE), structure-library/ordinals (def-by-nn-recursion),
;;; list-recursion (MAKE-SET), cardinality (CARD).  No proof is cited.

;;; -----------------------------------------------------------------------
;;; 1. The head table.

(def-functoid 'HD-RES   '(mch_) '(IF (<= mch_ 10) 2 1))
(notation! 'HD-RES 'kind 'functoid 'arity 1 'english "the kind of an application of the head $1")
(def-functoid 'HD-ARGK  '(mch_) '(IF (<= mch_ 6) 2 1))
(notation! 'HD-ARGK 'kind 'functoid 'arity 1 'english "the kind of the arguments of the head $1")
(def-predicate 'APP-AR-OK '(mch_ mcn_)
  '(OR (<= 10 mch_)
       (OR (AND (<= mch_ 1) (= mcn_ 0))
           (OR (AND (= mch_ 2) (= mcn_ 1))
               (AND (<= 3 mch_) (= mcn_ 2))))))
(notation! 'APP-AR-OK 'kind 'predicate 'arity 2 'english "$2 is an arity allowed for the head $1")

(def-functoid 'HD-BRES  '(mch_) '(IF (<= mch_ 21) 2 1))
(notation! 'HD-BRES 'kind 'functoid 'arity 1 'english "the kind of a binder of head $1")
(def-functoid 'HD-BODY  '(mch_) '(IF (OR (= mch_ 24) (= mch_ 26)) 1 2))
(notation! 'HD-BODY 'kind 'functoid 'arity 1 'english "the kind of the body of a binder of head $1")
(def-predicate 'BIND-SIG '(mch_ mcnb_ mcn_)
  '(OR (AND (<= 20 mch_) (AND (<= mch_ 21) (AND (= mcnb_ 1) (= mcn_ 0))))
       (OR (AND (OR (= mch_ 22) (OR (= mch_ 24) (= mch_ 26))) (AND (= mcnb_ 1) (= mcn_ 1)))
           (OR (AND (OR (= mch_ 23) (= mch_ 25)) (AND (= mcnb_ 1) (= mcn_ 0)))
               (AND (= mch_ 27) (AND (= mcnb_ 0) (= mcn_ 2)))))))
(notation! 'BIND-SIG 'kind 'predicate 'arity 3
           'english "the head $1 binds $2 variables over $3 outside arguments")

;;; -----------------------------------------------------------------------
;;; 2. Well-formedness.

(def-by-nn-recursion 'WKS-STAGE '()
  '(VNB-LAMBDA mce_ (EXPR-STAGE 0) (PAIR 1 1))
  '(mcn_ mcv_)
  '(VNB-LAMBDA mce_ (EXPR-STAGE (succ mcn_))
     (IF (IN mce_ (EXPR-STAGE mcn_))
         (mcv_ mce_)
         (IF (= (NTH 1 mce_) 3)
             (SEP mckk_ NN (AND (= mckk_ (HD-RES (NTH 2 mce_)))
                           (AND (APP-AR-OK (NTH 2 mce_) (LENGTH (NTH 3 mce_)))
                                (FORALL mcw_ (IMPLIES (IN mcw_ (MAKE-SET (NTH 3 mce_)))
                                                      (IN (HD-ARGK (NTH 2 mce_)) (mcv_ mcw_)))))))
             (SEP mckk_ NN (AND (= mckk_ (HD-BRES (NTH 2 mce_)))
                           (AND (BIND-SIG (NTH 2 mce_) (NTH 3 mce_) (LENGTH (NTH 4 mce_)))
                           (AND (FORALL mcw_ (IMPLIES (IN mcw_ (MAKE-SET (NTH 4 mce_)))
                                                      (IN 1 (mcv_ mcw_))))
                                (IN (HD-BODY (NTH 2 mce_)) (mcv_ (NTH 5 mce_)))))))))))
(notation! 'WKS-STAGE 'kind 'functoid 'arity 1 'english "the kind map on the stage $1")

(def-functoid 'EXPR-WKS '(mce_) '((WKS-STAGE (EXPR-RANK mce_)) mce_))
(notation! 'EXPR-WKS 'kind 'functoid 'arity 1 'english "the kinds of the expression $1")

(def-predicate 'WF-TERM '(mce_) '(IN 1 (EXPR-WKS mce_)))
(notation! 'WF-TERM 'kind 'predicate 'arity 1 'english "$1 is a well-formed term")
(def-predicate 'WF-FML '(mce_) '(IN 2 (EXPR-WKS mce_)))
(notation! 'WF-FML 'kind 'predicate 'arity 1 'english "$1 is a well-formed formula")

(def-constant 'CLF '(clf-def (== CLF (SEP mce_ EXPR-SET (AND (WF-FML mce_) (EXPR-LC mce_))))))
(notation! 'CLF 'kind 'constant 'arity 0 'english "the sentences (locally closed well-formed formulas)")
(def-constant 'CLT '(clt-def (== CLT (SEP mce_ EXPR-SET (AND (WF-TERM mce_) (EXPR-LC mce_))))))
(notation! 'CLT 'kind 'constant 'arity 0 'english "the locally closed well-formed terms")

;;; -----------------------------------------------------------------------
;;; The encoded constructors of the heads the core names.

(def-constant 'ENC-TRUTH   '(enc-truth-def   (== ENC-TRUTH (EAPP 0 (LIST)))))
(def-constant 'ENC-FALSITY '(enc-falsity-def (== ENC-FALSITY (EAPP 1 (LIST)))))
(def-functoid 'ENC-NOT '(mcp_)      '(EAPP 2 (LIST mcp_)))
(def-functoid 'ENC-AND '(mcp_ mcq_) '(EAPP 3 (LIST mcp_ mcq_)))
(def-functoid 'ENC-OR  '(mcp_ mcq_) '(EAPP 4 (LIST mcp_ mcq_)))
(def-functoid 'ENC-IMP '(mcp_ mcq_) '(EAPP 5 (LIST mcp_ mcq_)))
(def-functoid 'ENC-IFF '(mcp_ mcq_) '(EAPP 6 (LIST mcp_ mcq_)))
(def-functoid 'ENC-IN  '(mcp_ mcq_) '(EAPP 7 (LIST mcp_ mcq_)))
(def-functoid 'ENC-EQ  '(mcp_ mcq_) '(EAPP 8 (LIST mcp_ mcq_)))
(def-functoid 'ENC-QEQ '(mcp_ mcq_) '(EAPP 9 (LIST mcp_ mcq_)))
(def-functoid 'ENC-UNION '(mcl_)    '(EAPP 11 mcl_))
(def-functoid 'ENC-INTER '(mcl_)    '(EAPP 12 mcl_))
(def-functoid 'ENC-CART  '(mcl_)    '(EAPP 13 mcl_))
(def-functoid 'ENC-TUPLES '(mcp_)   '(EAPP 14 (LIST mcp_)))
(def-functoid 'ENC-NTH '(mcp_ mcq_) '(EAPP 15 (LIST mcp_ mcq_)))
(def-functoid 'ENC-LENGTH '(mcp_)   '(EAPP 16 (LIST mcp_)))
(def-functoid 'ENC-LIST '(mcl_)     '(EAPP 17 mcl_))
(def-functoid 'ENC-APPLY '(mcp_ mcq_) '(EAPP 18 (LIST mcp_ mcq_)))
(def-functoid 'ENC-FUN '(mcp_ mcq_) '(EAPP 19 (LIST mcp_ mcq_)))
(def-functoid 'ENC-ALL '(mcb_)      '(EBIND 20 1 (LIST) mcb_))
(def-functoid 'ENC-EX  '(mcb_)      '(EBIND 21 1 (LIST) mcb_))
(def-functoid 'ENC-SEP '(mca_ mcb_) '(EBIND 22 1 (LIST mca_) mcb_))
(def-functoid 'ENC-COMP '(mcb_)     '(EBIND 23 1 (LIST) mcb_))
(def-functoid 'ENC-BU  '(mca_ mcb_) '(EBIND 24 1 (LIST mca_) mcb_))
(def-functoid 'ENC-IOTA '(mcb_)     '(EBIND 25 1 (LIST) mcb_))
(def-functoid 'ENC-LAM '(mca_ mcb_) '(EBIND 26 1 (LIST mca_) mcb_))
(def-functoid 'ENC-IF  '(mcp_ mca_ mcb_) '(EBIND 27 0 (LIST mca_ mcb_) mcp_))
(def-functoid 'ENC-NUM '(mck_)      '(ECONST (* 2 mck_)))
(def-constant 'ENC-SETC '(enc-setc-def (== ENC-SETC (ECONST 1))))
(for-each (lambda (e) (notation! (car e) 'kind 'functoid 'arity (cadr e) 'english (caddr e)))
  '((ENC-NOT 1 "the encoded negation of $1") (ENC-AND 2 "the encoded conjunction of $1 and $2")
    (ENC-OR 2 "the encoded disjunction of $1 and $2") (ENC-IMP 2 "the encoded implication from $1 to $2")
    (ENC-IFF 2 "the encoded equivalence of $1 and $2") (ENC-IN 2 "the encoded membership of $1 in $2")
    (ENC-EQ 2 "the encoded equation $1 = $2") (ENC-QEQ 2 "the encoded quasi-equation $1 == $2")
    (ENC-UNION 1 "the encoded union of the list $1") (ENC-INTER 1 "the encoded intersection of the list $1")
    (ENC-CART 1 "the encoded product of the list $1") (ENC-TUPLES 1 "the encoded tuples over $1")
    (ENC-NTH 2 "the encoded $1-th entry of $2") (ENC-LENGTH 1 "the encoded length of $1")
    (ENC-LIST 1 "the encoded list of the entries of $1") (ENC-APPLY 2 "the encoded application of $1 to $2")
    (ENC-FUN 2 "the encoded functions from $1 to $2") (ENC-ALL 1 "the encoded universal with body $1")
    (ENC-EX 1 "the encoded existential with body $1") (ENC-SEP 2 "the encoded separation of $1 by $2")
    (ENC-COMP 1 "the encoded comprehension by $1") (ENC-BU 2 "the encoded union over $1 of $2")
    (ENC-IOTA 1 "the encoded description by $1") (ENC-LAM 2 "the encoded lambda over $1 with body $2")
    (ENC-IF 3 "the encoded conditional term on $1") (ENC-NUM 1 "the encoded numeral $1")))
(notation! 'ENC-TRUTH 'kind 'constant 'arity 0 'english "the encoded TRUTH")
(notation! 'ENC-FALSITY 'kind 'constant 'arity 0 'english "the encoded FALSITY")
(notation! 'ENC-SETC 'kind 'constant 'arity 0 'english "the encoded class SET")

;;; The n-ary formulas of 4.6, by recursion on a count n (the first n entries of a list),
;;; LEFT-nested over a TRUTH / FALSITY base:  ORL(x, l, 3) = ((FALSITY or x in l1) or x in l2) or x in l3.
;;; The shape is the core's choice: the kernel's n-ary UNION and INTERSECTION meet the right-nested
;;; connectives only through the schema, and a recursion on the count is an `ni' (no list
;;; induction, no subtraction).
(def-by-nn-recursion 'ENC-ORL '(mcx_ mcl_) 'ENC-FALSITY '(mcn_ mcv_)
  '(ENC-OR mcv_ (ENC-IN mcx_ (NTH (succ mcn_) mcl_))))
(def-by-nn-recursion 'ENC-ANDL '(mcx_ mcl_) 'ENC-TRUTH '(mcn_ mcv_)
  '(ENC-AND mcv_ (ENC-IN mcx_ (NTH (succ mcn_) mcl_))))
(def-by-nn-recursion 'ENC-ANDE '(mcl_ mca_) 'ENC-TRUTH '(mcn_ mcv_)
  '(ENC-AND mcv_ (ENC-IN (NTH (succ mcn_) mcl_) mca_)))
(def-by-nn-recursion 'ENC-CARTL '(mcx_ mcl_) 'ENC-TRUTH '(mcn_ mcv_)
  '(ENC-AND mcv_ (ENC-IN (ENC-NTH (ENC-NUM (succ mcn_)) mcx_) (NTH (succ mcn_) mcl_))))
(def-by-nn-recursion 'ENC-EQL '(mcl_ mca_) 'ENC-TRUTH '(mcn_ mcv_)
  '(ENC-AND mcv_ (ENC-EQ (NTH (succ mcn_) mcl_) (NTH (succ mcn_) mca_))))
(notation! 'ENC-ORL 'kind 'functoid 'arity 3 'english "the disjunction of $1 in the first $3 entries of $2")
(notation! 'ENC-ANDL 'kind 'functoid 'arity 3 'english "the conjunction of $1 in the first $3 entries of $2")
(notation! 'ENC-ANDE 'kind 'functoid 'arity 3 'english "the conjunction of the first $3 entries of $1 in $2")
(notation! 'ENC-CARTL 'kind 'functoid 'arity 3 'english "the componentwise memberships of $1 in the first $3 entries of $2")
(notation! 'ENC-EQL 'kind 'functoid 'arity 3 'english "the componentwise equations of the first $3 entries of $1 and $2")

;;; -----------------------------------------------------------------------
;;; 3. Contexts and sequents.

(def-constant 'CTX-SET '(ctx-def (== CTX-SET (SEP mcg_ (POWER CLF) (IN (CARD mcg_) NN)))))
(notation! 'CTX-SET 'kind 'constant 'arity 0 'english "the contexts (finite sets of sentences)")
(def-constant 'SEQ-SET '(seq-def (== SEQ-SET (CARTESIAN CTX-SET CLF))))
(notation! 'SEQ-SET 'kind 'constant 'arity 0 'english "the sequents")
(def-functoid 'CTX-ADD '(mcg_ mca_) '(UNION mcg_ (PAIR mca_ mca_)))
(notation! 'CTX-ADD 'kind 'functoid 'arity 2 'english "the context $1 extended by $2")
(def-functoid 'CTX-FV '(mcg_) '(BIG-UNION mcw_ mcg_ (EXPR-FV mcw_)))
(notation! 'CTX-FV 'kind 'functoid 'arity 1 'english "the free names of the context $1")

;;; -----------------------------------------------------------------------
;;; 4. The core relations.  (mc--ex VARS BODY) is the unguarded existential chain.

(define (mc--ex vars body)
  (if (null? vars) body `(FORSOME ,(car vars) ,(mc--ex (cdr vars) body))))
(define (mc--and . fs)
  (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(apply mc--and (cdr fs)))))
(define mc--core-names '())
(define (mc--cr! name note body)
  (def-predicate name '(mct_ mchs_ mcc_) body)
  (notation! name 'kind 'predicate 'arity 3 'english note)
  (set! mc--core-names (append mc--core-names (list name))))

;;; 4.1 LOGIC (21 named in the note, which counts 22).
(mc--cr! 'CR-AND-INTRO "the core and-intro relates $2 to $3"
  (mc--ex '(mcg_ mca_ mcb_) (mc--and '(= mcc_ (LIST mcg_ (ENC-AND mca_ mcb_)))
                                     '(= mchs_ (LIST (LIST mcg_ mca_) (LIST mcg_ mcb_))))))
(mc--cr! 'CR-AND-ELIM "the core and-elim relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mca_ mcb_) (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(IN (ENC-AND mca_ mcb_) mcg_)
                                          '(= mchs_ (LIST (LIST (CTX-ADD (CTX-ADD mcg_ mca_) mcb_) mcf_))))))
(mc--cr! 'CR-OR-INTRO-LEFT "the core or-intro-left relates $2 to $3"
  (mc--ex '(mcg_ mca_ mcb_) (mc--and '(= mcc_ (LIST mcg_ (ENC-OR mca_ mcb_)))
                                     '(= mchs_ (LIST (LIST mcg_ mca_))))))
(mc--cr! 'CR-OR-INTRO-RIGHT "the core or-intro-right relates $2 to $3"
  (mc--ex '(mcg_ mca_ mcb_) (mc--and '(= mcc_ (LIST mcg_ (ENC-OR mca_ mcb_)))
                                     '(= mchs_ (LIST (LIST mcg_ mcb_))))))
(mc--cr! 'CR-OR-ELIM "the core or-elim relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mca_ mcb_) (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(IN (ENC-OR mca_ mcb_) mcg_)
                                          '(= mchs_ (LIST (LIST (CTX-ADD mcg_ mca_) mcf_) (LIST (CTX-ADD mcg_ mcb_) mcf_))))))
(mc--cr! 'CR-IMPLIES-INTRO "the core implies-intro relates $2 to $3"
  (mc--ex '(mcg_ mca_ mcb_) (mc--and '(= mcc_ (LIST mcg_ (ENC-IMP mca_ mcb_)))
                                     '(= mchs_ (LIST (LIST (CTX-ADD mcg_ mca_) mcb_))))))
(mc--cr! 'CR-BACKCHAIN "the core backchain relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mca_) (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(IN (ENC-IMP mca_ mcf_) mcg_)
                                     '(= mchs_ (LIST (LIST mcg_ mca_))))))
(mc--cr! 'CR-NOT-INTRO "the core not-intro relates $2 to $3"
  (mc--ex '(mcg_ mca_) (mc--and '(= mcc_ (LIST mcg_ (ENC-NOT mca_)))
                                '(= mchs_ (LIST (LIST (CTX-ADD mcg_ mca_) ENC-FALSITY))))))
(mc--cr! 'CR-NOT-ELIM "the core not-elim relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mca_) (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(IN (ENC-NOT mca_) mcg_) '(IN mca_ mcg_)
                                     '(= mchs_ (LIST)))))
(mc--cr! 'CR-IFF-INTRO "the core iff-intro relates $2 to $3"
  (mc--ex '(mcg_ mca_ mcb_) (mc--and '(= mcc_ (LIST mcg_ (ENC-IFF mca_ mcb_)))
                                     '(= mchs_ (LIST (LIST (CTX-ADD mcg_ mca_) mcb_) (LIST (CTX-ADD mcg_ mcb_) mca_))))))
(mc--cr! 'CR-IFF-ELIM "the core iff-elim relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mca_ mcb_) (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(IN (ENC-IFF mca_ mcb_) mcg_)
             '(= mchs_ (LIST (LIST (CTX-ADD (CTX-ADD mcg_ (ENC-IMP mca_ mcb_)) (ENC-IMP mcb_ mca_)) mcf_))))))
;; forall-intro: the eigenvariable condition by FV: the name y is free neither in Gamma nor in the body.
(mc--cr! 'CR-FORALL-INTRO "the core forall-intro relates $2 to $3"
  (mc--ex '(mcg_ mcb_ mcy_) (mc--and '(= mcc_ (LIST mcg_ (ENC-ALL mcb_))) '(IN mcy_ NN)
             '(NOT (IN mcy_ (UNION (CTX-FV mcg_) (EXPR-FV mcb_))))
             '(= mchs_ (LIST (LIST mcg_ (EXPR-OPEN mcb_ 0 (EFVAR mcy_))))))))
;; forall-elim: in the core the definedness side sequent  Gamma |- t = t  is ALWAYS a premise (4.7).
(mc--cr! 'CR-FORALL-ELIM "the core forall-elim relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mcb_ mctm_) (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(IN (ENC-ALL mcb_) mcg_) '(IN mctm_ CLT)
             '(= mchs_ (LIST (LIST (CTX-ADD mcg_ (EXPR-OPEN mcb_ 0 mctm_)) mcf_) (LIST mcg_ (ENC-EQ mctm_ mctm_)))))))
;; forsome-intro.  DEPARTS from the kernel (and from the note, which names no side condition): the
;; witness must DENOTE, so the core carries the same side sequent as forall-elim.  The kernel's
;; forsome-intro (`ew') has none, and with an undefined witness it proves FALSITY modulo 0
;; (scratchpad/meta2/exprobe.scm, 2026-10-08).
(mc--cr! 'CR-FORSOME-INTRO "the core forsome-intro relates $2 to $3"
  (mc--ex '(mcg_ mcb_ mctm_) (mc--and '(= mcc_ (LIST mcg_ (ENC-EX mcb_))) '(IN mctm_ CLT)
             '(= mchs_ (LIST (LIST mcg_ (EXPR-OPEN mcb_ 0 mctm_)) (LIST mcg_ (ENC-EQ mctm_ mctm_)))))))
(mc--cr! 'CR-FORSOME-ELIM "the core forsome-elim relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mcb_ mcy_) (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(IN (ENC-EX mcb_) mcg_) '(IN mcy_ NN)
             '(NOT (IN mcy_ (UNION (CTX-FV mcg_) (EXPR-FV mcf_))))
             '(= mchs_ (LIST (LIST (CTX-ADD mcg_ (EXPR-OPEN mcb_ 0 (EFVAR mcy_))) mcf_))))))
(mc--cr! 'CR-ASSUMPTION "the core assumption relates $2 to $3"
  (mc--ex '(mcg_ mca_) (mc--and '(= mcc_ (LIST mcg_ mca_)) '(IN mca_ mcg_) '(= mchs_ (LIST)))))
;; theorem-assumption: the goal form (any member of T); the kernel's context form is a cut away.
(mc--cr! 'CR-THEOREM-ASSUMPTION "the core theorem-assumption relates $2 to $3"
  (mc--ex '(mcg_ mca_) (mc--and '(= mcc_ (LIST mcg_ mca_)) '(IN mca_ mct_) '(= mchs_ (LIST)))))
(mc--cr! 'CR-CUT "the core cut relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mca_) (mc--and '(= mcc_ (LIST mcg_ mcf_))
                                     '(= mchs_ (LIST (LIST mcg_ mca_) (LIST (CTX-ADD mcg_ mca_) mcf_))))))
(mc--cr! 'CR-WEAKENING "the core weakening relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mcd_) (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(SUBSET mcd_ mcg_)
                                     '(= mchs_ (LIST (LIST mcd_ mcf_))))))
(mc--cr! 'CR-CONTRADICTION "the core proof-by-contradiction relates $2 to $3"
  (mc--ex '(mcg_ mcf_) (mc--and '(= mcc_ (LIST mcg_ mcf_))
                                '(= mchs_ (LIST (LIST (CTX-ADD mcg_ (ENC-NOT mcf_)) ENC-FALSITY))))))
(mc--cr! 'CR-TRUTH-INTRO "the core truth-intro relates $2 to $3"
  (mc--ex '(mcg_) (mc--and '(= mcc_ (LIST mcg_ ENC-TRUTH)) '(= mchs_ (LIST)))))

;;; 4.2 EQUALITY.
;; eq-subst: "some occurrences of s replaced by t" is P[z := s] against P[z := t] for a name z;
;; the context equation is s = t or s == t, one orientation (the others are admissible).
(mc--cr! 'CR-EQ-SUBST "the core eq-subst relates $2 to $3"
  (mc--ex '(mcg_ mcp_ mcz_ mcs_ mctm_)
    (mc--and '(= mcc_ (LIST mcg_ (EXPR-SUBST mcp_ mcz_ mcs_))) '(IN mcz_ NN) '(IN mcp_ EXPR-SET)
             '(OR (IN (ENC-EQ mcs_ mctm_) mcg_) (IN (ENC-QEQ mcs_ mctm_) mcg_))
             '(= mchs_ (LIST (LIST mcg_ (EXPR-SUBST mcp_ mcz_ mctm_)))))))
;; eq-subst, THE OTHER ORIENTATION (the user's decision, 2026-10-13: the core's eq-subst is two-way).
;; THE CLAIM: the same rewriting step as CR-EQ-SUBST, licensed by the context equation read the other
;; way round, t = s or t == s.  The kernel's pi-eq-subst! (primitive-inferences.scm 604-622) accepts
;; any of the four forms (= s t), (= t s), (== s t), (== t s) for the step that replaces s by t, so the
;; one-way relation above under-describes the kernel.  It is a second relation rather than two more
;; disjuncts of the first so that no proof written against CR-EQ-SUBST changes; together the two are
;; the two-way rule.  With it, the strictness of = on the RIGHT is derived (meta-def-laws.scm,
;; adm-def-strict-eq-r) and leaves the table of schemas.  (Not named CR-EQ-SUBST-REV: def-predicate mints
;; cr-eq-subst-rev, the reversed companion of CR-EQ-SUBST's defining IFF, and the two would collide.)
(mc--cr! 'CR-EQ-SUBST-SYM "the core eq-subst (other orientation) relates $2 to $3"
  (mc--ex '(mcg_ mcp_ mcz_ mcs_ mctm_)
    (mc--and '(= mcc_ (LIST mcg_ (EXPR-SUBST mcp_ mcz_ mcs_))) '(IN mcz_ NN) '(IN mcp_ EXPR-SET)
             '(OR (IN (ENC-EQ mctm_ mcs_) mcg_) (IN (ENC-QEQ mctm_ mcs_) mcg_))
             '(= mchs_ (LIST (LIST mcg_ (EXPR-SUBST mcp_ mcz_ mctm_)))))))
;; reflexivity fires only on a free variable or an atomic constant (4.7).
(mc--cr! 'CR-REFLEXIVITY "the core reflexivity relates $2 to $3"
  (mc--ex '(mcg_ mctm_ mcn_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-EQ mctm_ mctm_))) '(IN mcn_ NN)
             '(OR (= mctm_ (EFVAR mcn_)) (= mctm_ (ECONST mcn_))) '(= mchs_ (LIST)))))
(mc--cr! 'CR-QUASI-REFLEXIVITY "the core quasi-reflexivity relates $2 to $3"
  (mc--ex '(mcg_ mctm_) (mc--and '(= mcc_ (LIST mcg_ (ENC-QEQ mctm_ mctm_))) '(= mchs_ (LIST)))))

;;; 4.6 STRUCTURAL MEMBERSHIP AND TUPLE SCHEMAS, each a goal with no premise unless marked.
(mc--cr! 'CR-UNION-MEM "the core union-mem relates $2 to $3"
  (mc--ex '(mcg_ mcx_ mcl_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-IFF (ENC-IN mcx_ (ENC-UNION mcl_)) (ENC-ORL mcx_ mcl_ (LENGTH mcl_)))))
             '(= mchs_ (LIST)))))
;; DEPARTS: n >= 1.  For n = 0 the right side is TRUTH and x a proper class would satisfy it.
(mc--cr! 'CR-INTERSECTION-MEM "the core intersection-mem relates $2 to $3"
  (mc--ex '(mcg_ mcx_ mcl_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-IFF (ENC-IN mcx_ (ENC-INTER mcl_)) (ENC-ANDL mcx_ mcl_ (LENGTH mcl_)))))
             '(<= 1 (LENGTH mcl_)) '(= mchs_ (LIST)))))
;; DEPARTS: stated through NTH and LENGTH of x, not as the note's chain of n existentials (which in
;; the locally nameless encoding needs a list of n indices built by recursion); n >= 1.
(mc--cr! 'CR-CARTESIAN-MEM "the core cartesian-mem relates $2 to $3"
  (mc--ex '(mcg_ mcx_ mcl_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-IFF (ENC-IN mcx_ (ENC-CART mcl_))
                                          (ENC-AND (ENC-IN mcx_ (ENC-TUPLES ENC-SETC))
                                                   (ENC-AND (ENC-EQ (ENC-LENGTH mcx_) (ENC-NUM (LENGTH mcl_)))
                                                            (ENC-CARTL mcx_ mcl_ (LENGTH mcl_)))))))
             '(<= 1 (LENGTH mcl_)) '(= mchs_ (LIST)))))
(mc--cr! 'CR-TUPLES-MEM "the core tuples-mem relates $2 to $3"
  (mc--ex '(mcg_ mcl_ mca_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-IFF (ENC-IN (ENC-LIST mcl_) (ENC-TUPLES mca_)) (ENC-ANDE mcl_ mca_ (LENGTH mcl_)))))
             '(= mchs_ (LIST)))))
;; DEPARTS: the list must DENOTE (a premise), by the list doctrine of 2026-10-01: [0, SET] denotes
;; nothing, so NTH(1, [0, SET]) == 0 is false.  The kernel's nth-reduce is unguarded.
(mc--cr! 'CR-NTH-EQ "the core nth-eq relates $2 to $3"
  (mc--ex '(mcg_ mcl_ mck_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-QEQ (ENC-NTH (ENC-NUM mck_) (ENC-LIST mcl_)) (NTH mck_ mcl_))))
             '(IN mck_ NN) '(<= 1 mck_) '(<= mck_ (LENGTH mcl_))
             '(= mchs_ (LIST (LIST mcg_ (ENC-EQ (ENC-LIST mcl_) (ENC-LIST mcl_))))))))
(mc--cr! 'CR-LENGTH-EQ "the core length-eq relates $2 to $3"
  (mc--ex '(mcg_ mcl_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-QEQ (ENC-LENGTH (ENC-LIST mcl_)) (ENC-NUM (LENGTH mcl_)))))
             '(= mchs_ (LIST (LIST mcg_ (ENC-EQ (ENC-LIST mcl_) (ENC-LIST mcl_))))))))
;; DEPARTS: both lists must denote (premises), for the same reason: [SET] = [SET] is false while
;; SET = SET is true.  The kernel's tuple-equality-decompose is unguarded.
(mc--cr! 'CR-TUPLE-EQ "the core tuple-eq relates $2 to $3"
  (mc--ex '(mcg_ mcl_ mca_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-IFF (ENC-EQ (ENC-LIST mcl_) (ENC-LIST mca_)) (ENC-EQL mcl_ mca_ (LENGTH mcl_)))))
             '(= (LENGTH mcl_) (LENGTH mca_))
             '(= mchs_ (LIST (LIST mcg_ (ENC-EQ (ENC-LIST mcl_) (ENC-LIST mcl_)))
                             (LIST mcg_ (ENC-EQ (ENC-LIST mca_) (ENC-LIST mca_))))))))

;;; 4.3 CONDITIONAL TERMS.  DEPARTS from the kernel: the main branch gains the QUASI-equation
;;; IF(p, a, b) == a.  The kernel's if-true gains the STRICT (= (IF p a b) a), which asserts that a
;;; denotes, and proves FALSITY modulo 0 with a = IOTA x. (x in NN and FALSITY)
;;; (scratchpad/meta2/ifprobe-falsity.scm, 2026-10-08).
(mc--cr! 'CR-IF-TRUE "the core if-true relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mcp_ mca_ mcb_)
    (mc--and '(= mcc_ (LIST mcg_ mcf_))
             '(= mchs_ (LIST (LIST mcg_ mcp_)
                             (LIST (CTX-ADD mcg_ (ENC-QEQ (ENC-IF mcp_ mca_ mcb_) mca_)) mcf_))))))
(mc--cr! 'CR-IF-FALSE "the core if-false relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mcp_ mca_ mcb_)
    (mc--and '(= mcc_ (LIST mcg_ mcf_))
             '(= mchs_ (LIST (LIST mcg_ (ENC-NOT mcp_))
                             (LIST (CTX-ADD mcg_ (ENC-QEQ (ENC-IF mcp_ mca_ mcb_) mcb_)) mcf_))))))

;;; 4.4 SET FORMATION, DESCRIPTIONS, FUNCTIONS (9 of the note's 10: functoid-beta-eq has no
;;; encoding, the encoding has no functoid records -- a finding).  Bodies use the index 0 for the
;;; bound variable; an outside argument is locally closed (it sits in a sentence), so it needs no
;;; shift under one more binder.
(mc--cr! 'CR-SEP-SETHOOD "the core sep-sethood relates $2 to $3"
  (mc--ex '(mcg_ mca_ mcp_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-IN (ENC-SEP mca_ mcp_) ENC-SETC)))
             '(= mchs_ (LIST (LIST mcg_ (ENC-IN mca_ ENC-SETC)))))))
(mc--cr! 'CR-SEP-MEM "the core sep-mem relates $2 to $3"
  (mc--ex '(mcg_ mca_ mcp_ mctm_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-IFF (ENC-IN mctm_ (ENC-SEP mca_ mcp_))
                                          (ENC-AND (ENC-IN mctm_ mca_) (EXPR-OPEN mcp_ 0 mctm_)))))
             '(= mchs_ (LIST)))))
(mc--cr! 'CR-COMP-MEM "the core comp-mem relates $2 to $3"
  (mc--ex '(mcg_ mcp_ mctm_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-IFF (ENC-IN mctm_ (ENC-COMP mcp_))
                                          (ENC-AND (ENC-IN mctm_ ENC-SETC) (EXPR-OPEN mcp_ 0 mctm_)))))
             '(= mchs_ (LIST)))))
(mc--cr! 'CR-BIG-UNION-SETHOOD "the core big-union-sethood relates $2 to $3"
  (mc--ex '(mcg_ mca_ mcb_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-IN (ENC-BU mca_ mcb_) ENC-SETC)))
             '(= mchs_ (LIST (LIST mcg_ (ENC-IN mca_ ENC-SETC))
                             (LIST mcg_ (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) mca_) (ENC-IN mcb_ ENC-SETC)))))))))
(mc--cr! 'CR-BIG-UNION-MEM "the core big-union-mem relates $2 to $3"
  (mc--ex '(mcg_ mca_ mcb_ mcx_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-IFF (ENC-IN mcx_ (ENC-BU mca_ mcb_))
                                          (ENC-EX (ENC-AND (ENC-IN (EBVAR 0) mca_) (ENC-IN mcx_ mcb_))))))
             '(= mchs_ (LIST)))))
;; iota-def: exists-unique x. p, written  EX(p AND ALL(p => BVAR 1 = BVAR 0)): under the inner
;; binder the index 0 of p is the inner variable, so p itself is p[x := y].
(mc--cr! 'CR-IOTA-DEF "the core iota-def relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mcp_)
    (mc--and '(= mcc_ (LIST mcg_ mcf_))
             '(= mchs_ (LIST (LIST mcg_ (ENC-EX (ENC-AND mcp_ (ENC-ALL (ENC-IMP mcp_ (ENC-EQ (EBVAR 1) (EBVAR 0)))))))
                             (LIST (CTX-ADD mcg_ (EXPR-OPEN mcp_ 0 (ENC-IOTA mcp_))) mcf_))))))
;; iota-in-elim: the description denotes is a PREMISE sequent (the kernel reads it off two shapes
;; of context formula).
(mc--cr! 'CR-IOTA-IN-ELIM "the core iota-in-elim relates $2 to $3"
  (mc--ex '(mcg_ mcf_ mcp_)
    (mc--and '(= mcc_ (LIST mcg_ mcf_))
             '(= mchs_ (LIST (LIST mcg_ (ENC-EQ (ENC-IOTA mcp_) (ENC-IOTA mcp_)))
                             (LIST (CTX-ADD mcg_ (EXPR-OPEN mcp_ 0 (ENC-IOTA mcp_))) mcf_))))))
(mc--cr! 'CR-LAMBDA-TYPE "the core lambda-type relates $2 to $3"
  (mc--ex '(mcg_ mca_ mcb_ mcd_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-IN (ENC-LAM mca_ mcb_) (ENC-FUN mca_ mcd_))))
             '(= mchs_ (LIST (LIST mcg_ (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) mca_) (ENC-IN mcb_ mcd_))))
                             (LIST mcg_ (ENC-IN mca_ ENC-SETC)))))))
;; DEPARTS: a QUASI-equation.  The note's strict  lambda(u) = b[u]  asserts that b[u] denotes.
(mc--cr! 'CR-LAMBDA-BETA-EQ "the core lambda-beta-eq relates $2 to $3"
  (mc--ex '(mcg_ mca_ mcb_ mctm_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-QEQ (ENC-APPLY (ENC-LAM mca_ mcb_) mctm_) (EXPR-OPEN mcb_ 0 mctm_))))
             '(= mchs_ (LIST (LIST mcg_ (ENC-IN mctm_ mca_)))))))

;;; 4.7 DEFINEDNESS: THE SCHEMAS ADMITTED BY THE USER'S DECISIONS OF 2026-10-13 AND 2026-10-14.
;;; META-5 (structure-library/meta-def.scm, scratchpad/triage/META-5-REPORT.md section 2) transcribed the
;;; clauses of the kernel's certificate pi--defined? as rules DEF-X and showed that the core above derives
;;; no definedness of a compound term except through eq-subst: every route through T instantiates a
;;; universal AT the term and owes its definedness.  The rules below are therefore not derivable; they are
;;; ADMITTED, one at a time, each with the claim it makes.  Each is the relation DEF-X of meta-def.scm
;;; without the conjunct (IN c SEQ-SET), which CORE-CLOSED supplies; the bodies are written alike, so
;;; that DEF-X(T, hs, c) yields CR-DEF-X(T, hs, c) up to the names of the bound variables, and the
;;; admissibility of DEF-X is the closure law of CR-DEF-X (meta-def-laws.scm, section 4).
;;; Strictness of = is not among them: on the left it was derived by META-5 (adm-def-strict-eq-l), on the
;;; right it is derived with CR-EQ-SUBST-SYM (adm-def-strict-eq-r).
;;; ADMITTED LATER (the user's decision of 2026-10-14; agent META-7): DEF-STRICT-ARG and DEF-STRICT-DOM (an
;;; argument of a defined application of a strict constructor, the domain of a defined binder term, is
;;; defined; the second half of META-5's row 5), as (6) and (7) below, with STRICT-HEAD (moved here from
;;; meta-def.scm).
;;; ADMITTED LATER (the user's decision of 2026-10-17, "yes do the predicate case"; agent META-10):
;;; DEF-STRICT-PRED (META-5's row 6), the strictness of a predicate application, as (8) below, with the
;;; predicate codes PRED-CODE.

;; The TOTAL class constructors (*total-term-heads*, primitive-inferences.scm): 11 UNION, 12
;; INTERSECTION, 13 CARTESIAN, 14 TUPLES, 19 FUN, 30 succ, 31 succ_ORD.  (Moved here from meta-def.scm,
;; where META-5 defined it, so that CR-DEF-TOTAL can name it.)
(def-predicate 'TOTAL-HEAD '(mchd_)
  '(OR (AND (<= 11 mchd_) (<= mchd_ 14)) (OR (= mchd_ 19) (AND (<= 30 mchd_) (<= mchd_ 31)))))
(notation! 'TOTAL-HEAD 'kind 'predicate 'arity 1 'english "the head $1 is a total class constructor")

;; (1) STRICTNESS OF IN, LEFT.  THE CLAIM: a membership t in A that holds has a DENOTING left side; in
;; NBG / VNB only an object (indeed a set) is a member of anything.  The kernel's clauses
;; asm-establishes-defined? and pi--strict-hyp-certifies? (META-5 rows 3 and 5) read it.
(mc--cr! 'CR-DEF-STRICT-IN-L "the core definedness rule strict-in-left relates $2 to $3"
  (mc--ex '(mcg_ mcw_ mca_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-EQ mcw_ mcw_))) '(= mchs_ (LIST (LIST mcg_ (ENC-IN mcw_ mca_)))))))
;; (1') STRICTNESS OF IN, RIGHT.  THE CLAIM: a membership t in A that holds has a DENOTING right side, a
;; class.  The same schema read at the other argument (META-5 row 5); one decision with (1).
(mc--cr! 'CR-DEF-STRICT-IN-R "the core definedness rule strict-in-right relates $2 to $3"
  (mc--ex '(mcg_ mcw_ mca_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-EQ mca_ mca_))) '(= mchs_ (LIST (LIST mcg_ (ENC-IN mcw_ mca_)))))))
;; (2) TOTAL CONSTRUCTORS.  THE CLAIM: UNION, INTERSECTION, CARTESIAN, TUPLES, FUN, succ and succ_ORD
;; applied to denoting arguments denote: for the class constructors this is class comprehension (each is
;; the class of the sets satisfying a formula of its arguments); for succ and succ_ORD it is that the
;; operation is total, its value at a non-number an object about which the guarded axioms say nothing.
;; The kernel's *total-term-heads* clause (META-5 row 8).  The head list is TOTAL-HEAD above; the
;; translator extends it only with the codes of genuine total constructors, never a def-functoid's.
(mc--cr! 'CR-DEF-TOTAL "the core definedness rule total-constructor relates $2 to $3"
  (mc--ex '(mcg_ mchd_ mcl_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-EQ (EAPP mchd_ mcl_) (EAPP mchd_ mcl_)))) '(TOTAL-HEAD mchd_)
             '(= (LENGTH mchs_) (LENGTH mcl_))
             '(FORALL mci_ (IMPLIES (IN mci_ NN) (IMPLIES (<= 1 mci_) (IMPLIES (<= mci_ (LENGTH mcl_))
                (= (NTH mci_ mchs_) (LIST mcg_ (ENC-EQ (NTH mci_ mcl_) (NTH mci_ mcl_)))))))))))
;; (3) BINDER TERMS OVER A DENOTING DOMAIN.  THE CLAIM: SEP x A. p, BIG-UNION x A. b and
;; VNB-LAMBDA x A. b denote when A denotes: separation (the subclass of A cut out by p), the union of the
;; values b[x] that are sets as x ranges over A, and the class of the pairs [x, b[x]] for x in A with
;; b[x] denoting -- each a class by comprehension, whatever the body.  The kernel's binder-domain
;; clause (META-5 row 9).
(mc--cr! 'CR-DEF-BINDER "the core definedness rule binder-domain relates $2 to $3"
  (mc--ex '(mcg_ mchd_ mca_ mcb_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-EQ (EBIND mchd_ 1 (LIST mca_) mcb_) (EBIND mchd_ 1 (LIST mca_) mcb_))))
             '(OR (= mchd_ 22) (OR (= mchd_ 24) (= mchd_ 26)))
             '(= mchs_ (LIST (LIST mcg_ (ENC-EQ mca_ mca_)))))))
;; (4) COMPREHENSION.  THE CLAIM: COMP x. p denotes, for every formula p: the class of the sets
;; satisfying p.  Note the strength: the encoded quantifiers range over CLASSES, so for a p that
;; quantifies over classes this is the impredicative comprehension of Morse-Kelley, not the predicative
;; comprehension of NBG.  The kernel already accepts every COMP unconditionally (META-5 row 10); the
;; schema describes it, it does not extend it.
(mc--cr! 'CR-DEF-COMP "the core definedness rule comprehension relates $2 to $3"
  (mc--ex '(mcg_ mcp_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-EQ (ENC-COMP mcp_) (ENC-COMP mcp_)))) '(= mchs_ (LIST)))))
;; (5) LISTS.  THE CLAIM: a literal list [e1 .. en] every entry of which is a SET denotes (the list
;; doctrine of 2026-10-01: such a list denotes iff every entry is a set; this is the "if" half, one
;; premise per entry).  The kernel's pi--sets-defined? clause (META-5 row 7).
(mc--cr! 'CR-DEF-LIST "the core definedness rule list relates $2 to $3"
  (mc--ex '(mcg_ mcl_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-EQ (ENC-LIST mcl_) (ENC-LIST mcl_))))
             '(= (LENGTH mchs_) (LENGTH mcl_))
             '(FORALL mci_ (IMPLIES (IN mci_ NN) (IMPLIES (<= 1 mci_) (IMPLIES (<= mci_ (LENGTH mcl_))
                (= (NTH mci_ mchs_) (LIST mcg_ (ENC-IN (NTH mci_ mcl_) ENC-SETC))))))))))

;; The constructor heads an application of which is STRICT in its arguments (primitive-inferences.scm,
;; pi--sob-walk, RESTRICTED to genuine constructors: the kernel walks every head but FORALL FORSOME IOTA
;; COMP IF and the binder bodies, and walks a def-functoid application through its instantiated body
;; since R4, 2026-10-13).  Encoded: the relations 7 IN and 8 = (their two arguments), the term heads 11-19
;; (UNION INTERSECTION CARTESIAN TUPLES NTH LENGTH LIST APPLY FUN), and the named constructors succ (30)
;; and succ_ORD (31).  The translator extends the list with the codes it gives the other constructors of
;; *total-term-heads* and the arithmetic heads; never with a def-functoid's code.  (Defined by META-5 in
;; meta-def.scm; moved here 2026-10-14, META-7, so that CR-DEF-STRICT-ARG can name it.)  For 7 and 8 the
;; premise of (6) is the definedness of a FORMULA, which is no sentence (WF-FML of ENC-EQ wants terms), so
;; (6) never fires at those codes; they are kept so that the relation is META-5's DEF-STRICT-ARG verbatim.
(def-predicate 'STRICT-HEAD '(mchd_)
  '(OR (AND (<= 7 mchd_) (<= mchd_ 8)) (OR (AND (<= 11 mchd_) (<= mchd_ 19)) (AND (<= 30 mchd_) (<= mchd_ 31)))))
(notation! 'STRICT-HEAD 'kind 'predicate 'arity 1 'english "an application of the head $1 is strict in its arguments")

;; (6) STRICTNESS OF THE CONSTRUCTORS IN THEIR ARGUMENTS (the user's decision, 2026-10-14).  THE CLAIM: an
;; application of a strict constructor that denotes has denoting arguments: UNION, INTERSECTION,
;; CARTESIAN, TUPLES, NTH, LENGTH, LIST, APPLY, FUN, succ and succ_ORD at an argument that does not denote
;; do not denote (the manual's "undefinedness propagates through all operations", the strictness of
;; application in the partial logic of LUTINS that VNB's certificate adopts).  For LIST it is the "only
;; if" half of the list doctrine of 2026-10-01 read for definedness (a list denotes only if its entries
;; are sets, so only if they denote); for APPLY it is strictness in the operator and the operand.  It is
;; the converse of (2) for the total heads.  The kernel's clause pi--strict-hyp-certifies? walks down
;; these heads (META-5 row 5); one premise, the definedness of the application, one conclusion per
;; argument position.
(mc--cr! 'CR-DEF-STRICT-ARG "the core definedness rule strict-argument relates $2 to $3"
  (mc--ex '(mcg_ mchd_ mcl_ mci_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-EQ (NTH mci_ mcl_) (NTH mci_ mcl_))))
             '(STRICT-HEAD mchd_) '(IN mci_ NN) '(<= 1 mci_) '(<= mci_ (LENGTH mcl_))
             '(= mchs_ (LIST (LIST mcg_ (ENC-EQ (EAPP mchd_ mcl_) (EAPP mchd_ mcl_))))))))
;; (7) STRICTNESS OF THE BINDER TERMS IN THEIR DOMAIN (the user's decision, 2026-10-14).  THE CLAIM: a
;; denoting SEP x A. p, BIG-UNION x A. b or VNB-LAMBDA x A. b has a denoting domain A: each is formed from
;; the class A, and a term built on a non-denoting part does not denote.  It is the converse of (3).  The
;; kernel's walk enters a binder term through its domain only (pi--sob-walk; META-5 row 5).
(mc--cr! 'CR-DEF-STRICT-DOM "the core definedness rule strict-domain relates $2 to $3"
  (mc--ex '(mcg_ mchd_ mca_ mcb_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-EQ mca_ mca_)))
             '(OR (= mchd_ 22) (OR (= mchd_ 24) (= mchd_ 26)))
             '(= mchs_ (LIST (LIST mcg_ (ENC-EQ (EBIND mchd_ 1 (LIST mca_) mcb_) (EBIND mchd_ 1 (LIST mca_) mcb_))))))))

;; THE PREDICATE CODES (agent META-10, 2026-10-17).  A predicate atom P(a1 .. an) is the head-10 node
;; [3, 10, [ECONST k, a1, .., an]] (section 1): the name first, a CONST, then the arguments.  PRED-CODE(k)
;; says that the code k names a PREDICATE CONSTANT: a primitive relation the encoding writes as a head-10
;; atom (11 <=, 13 <, 7 ORD-LT), a def-predicate name (9 LIMIT-ORD), a structure predicate IS-X.  Taken:
;; 7 ORD-LT and 9 LIMIT-ORD (meta-ind.scm), 11 <= and 13 < (meta-def.scm).  The translator of K3 extends
;; the list with the codes it gives the other def-predicate names and the structure predicates IS-X,
;; never with the code of a term constant.  IN, = and == are not predicate NAMES: they are the heads 7, 8,
;; 9 of section 1, as the connectives (heads 0-6) and the quantifiers (binder heads 20, 21) are.
(def-predicate 'PRED-CODE '(mcpk_)
  '(OR (= mcpk_ 7) (OR (= mcpk_ 9) (OR (= mcpk_ 11) (= mcpk_ 13)))))
(notation! 'PRED-CODE 'kind 'predicate 'arity 1 'english "the code $1 names a predicate constant")

;; (8) STRICTNESS OF A PREDICATE APPLICATION (the user's decision, 2026-10-17; agent META-10).  THE CLAIM:
;; an atom P(a1 .. an) that holds, P a PREDICATE CONSTANT (PRED-CODE: a primitive relation <=, <, ORD-LT,
;; a def-predicate name, a structure predicate IS-X), has DENOTING arguments a1 .. an.  VNB's atoms are
;; strict: an atom with a non-denoting argument is false, whatever the constant's definition says, because
;; def-predicate installs  forall x1 .. xn. P(x1 .. xn) iff body  quantified over OBJECTS, so the body
;; speaks only where the arguments denote.  One premise [g, P(l)], one conclusion [g, l_i = l_i] per
;; argument position i = 2 .. |l| (position 1 is the name).
;; WHAT IT DOES NOT SAY, and the relation's form excludes it: the premise is a HEAD-10 node whose first
;; entry is a CONST with a predicate code.  So NOT for == (head 9: quasi-equality is NOT strict,
;; 1/0 == 1/0 holds), NOT for a connective (heads 0-6: NOT (1/0 = 1/0) is true) or a quantifier (binder
;; heads 20, 21), and NOT for a definition's BODY read in place of the predicate: with P(x, y) iff
;; NOT x = y, NOT (1/0 = 1/0) is true and P(1/0, 1/0) is false.  (IN and = have their own strictness
;; rules, (1), (1') and the derived strictness of =.)  META controls: def-strict-pred-refuses-qeq and
;; def-strict-pred-refuses-not (theorem-library/meta-def-laws.scm, section 6).
;; PRECONDITION OF ITS SOUNDNESS.  The rule is sound only together with a kernel in which every
;; INSTANTIATION of a definition owes the definedness of the instance: forall-elim (the core's
;; CR-FORALL-ELIM carries [g, t = t] as a premise; the kernel's posts t = t, LUTINS rule of 2026-09-18)
;; and, since round 3 (docs s.14.1), the macete door, which owes t = t at an uncertified match.  An
;; unfolding that did not owe it would rewrite NOT (1/0 = 1/0) into P(1/0, 1/0), this rule would give
;; 1/0 = 1/0, and FALSITY would follow.  Suite control: "DEF-STRICT-PRED precondition".
(mc--cr! 'CR-DEF-STRICT-PRED "the core definedness rule strict-predicate relates $2 to $3"
  (mc--ex '(mcg_ mcl_ mck_ mci_)
    (mc--and '(= mcc_ (LIST mcg_ (ENC-EQ (NTH mci_ mcl_) (NTH mci_ mcl_))))
             '(= (NTH 1 mcl_) (ECONST mck_)) '(PRED-CODE mck_)
             '(IN mci_ NN) '(<= 2 mci_) '(<= mci_ (LENGTH mcl_))
             '(= mchs_ (LIST (LIST mcg_ (EAPP 10 mcl_)))))))

;;; -----------------------------------------------------------------------
;;; 5. CORE-RULE, CORE-CLOSED, DERIVABLE.

(def-predicate 'HYPS-IN '(mchs_ mcs_)
  '(FORALL mci_ (IMPLIES (IN mci_ NN) (IMPLIES (<= 1 mci_) (IMPLIES (<= mci_ (LENGTH mchs_))
                                                                    (IN (NTH mci_ mchs_) mcs_))))))
(notation! 'HYPS-IN 'kind 'predicate 'arity 2 'english "every entry of the list $1 is in $2")

(def-predicate 'CORE-RULE '(mct_ mchs_ mcc_)
  (let loop ((ns mc--core-names))
    (if (null? (cdr ns))
        `(,(car ns) mct_ mchs_ mcc_)
        `(OR (,(car ns) mct_ mchs_ mcc_) ,(loop (cdr ns))))))
(notation! 'CORE-RULE 'kind 'predicate 'arity 3 'english "some core rule over $1 relates $2 to $3")

(def-predicate 'CORE-CLOSED '(mct_ mcs_)
  '(FORALL mchs_ (FORALL mcc_ (IMPLIES (CORE-RULE mct_ mchs_ mcc_)
                               (IMPLIES (HYPS-IN mchs_ mcs_)
                                (IMPLIES (IN mcc_ SEQ-SET) (IN mcc_ mcs_)))))))
(notation! 'CORE-CLOSED 'kind 'predicate 'arity 2 'english "$2 is closed under the core rules over $1")

(def-functoid 'DERIVABLE '(mct_)
  '(SEP mcq_ SEQ-SET (FORALL mcs_ (IMPLIES (IN mcs_ (POWER SEQ-SET)) (IMPLIES (CORE-CLOSED mct_ mcs_) (IN mcq_ mcs_))))))
(notation! 'DERIVABLE 'kind 'functoid 'arity 1 'english "the sequents derivable in the core over $1")

;;; -----------------------------------------------------------------------
;;; 6. The kernel relations of phase 2, TRANSCRIBED from their checkers.  Each is to be read
;;; beside the checker; a kernel sequent is well formed by construction (make-wff), which is the
;;; conjunct (IN c SEQ-SET).  Contexts are compared as SETS (the checkers' convention 1), so the
;;; checker's "the hypothesis context is the conclusion's plus q" is an equation of sets.

;; rule-checkers-logic.scm 943-959 (detach): one hypothesis; the same goal; some (IMPLIES p q) in the
;; conclusion context with p in that context, and the hypothesis context = the conclusion's u {q}.
(def-predicate 'REL-DETACH '(mct_ mchs_ mcc_)
  (mc--and '(IN mcc_ SEQ-SET)
    (mc--ex '(mcg_ mcf_ mcp_ mcq_)
      (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(IN (ENC-IMP mcp_ mcq_) mcg_) '(IN mcp_ mcg_)
               '(= mchs_ (LIST (LIST (CTX-ADD mcg_ mcq_) mcf_)))))))
(notation! 'REL-DETACH 'kind 'predicate 'arity 3 'english "the kernel's detach relates $2 to $3")

;; rule-checkers-logic.scm 988-1004 (contraposition; UNREACHABLE, pi-contraposit! has no caller):
;; one hypothesis; the same context; the goal (NOT p); some (IMPLIES p q) in the context; the
;; hypothesis goal (NOT q).
(def-predicate 'REL-CONTRAPOSITION '(mct_ mchs_ mcc_)
  (mc--and '(IN mcc_ SEQ-SET)
    (mc--ex '(mcg_ mcp_ mcq_)
      (mc--and '(= mcc_ (LIST mcg_ (ENC-NOT mcp_))) '(IN (ENC-IMP mcp_ mcq_) mcg_)
               '(= mchs_ (LIST (LIST mcg_ (ENC-NOT mcq_))))))))
(notation! 'REL-CONTRAPOSITION 'kind 'predicate 'arity 3 'english "the kernel's contraposition relates $2 to $3")

;; rule-checkers-logic.scm 1191-1211 (union-intro k): the rule tag carries the index k, 1 <= k <= n;
;; the goal (IN x (UNION S1 .. Sn)); one hypothesis, the same context, goal (IN x S_k).
(def-predicate 'REL-UNION-INTRO '(mct_ mchs_ mcc_)
  (mc--and '(IN mcc_ SEQ-SET)
    (mc--ex '(mcg_ mcx_ mcl_ mck_)
      (mc--and '(= mcc_ (LIST mcg_ (ENC-IN mcx_ (ENC-UNION mcl_)))) '(IN mck_ NN) '(<= 1 mck_)
               '(<= mck_ (LENGTH mcl_))
               '(= mchs_ (LIST (LIST mcg_ (ENC-IN mcx_ (NTH mck_ mcl_)))))))))
(notation! 'REL-UNION-INTRO 'kind 'predicate 'arity 3 'english "the kernel's union-intro relates $2 to $3")

;;; The five kernel relations of the META-KIT pass (agent META-KIT, 2026-10-08), transcribed from the
;;; checkers of the 02:30Z tree (rule-checkers-logic.scm, md5 f60079fc...).  A rule with one
;;; hypothesis PER LIST ENTRY has |hs| = |l| and the i-th hypothesis written through NTH.  A kernel
;;; UNION or INTERSECTION has at least one argument: make-wff refuses an application with no
;;; argument (wff.scm, the `else' arm of walk-term), which is the conjunct (<= 1 (LENGTH l)) where
;;; the core needs it (intersection-mem, section 4.6); union-elim does not need it.

;; rule-checkers-logic.scm 1212-1229 (union-elim): some (IN x (UNION S1 .. Sn)) in the conclusion
;; context; one hypothesis per set, the same goal, the context with that membership REMOVED and
;; (IN x S_i) added (chk-ctx-+?: concl minus {f} union {added}).
(def-predicate 'REL-UNION-ELIM '(mct_ mchs_ mcc_)
  (mc--and '(IN mcc_ SEQ-SET)
    (mc--ex '(mcg_ mcf_ mcx_ mcl_)
      (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(IN (ENC-IN mcx_ (ENC-UNION mcl_)) mcg_)
               '(= (LENGTH mchs_) (LENGTH mcl_))
               '(FORALL mci_ (IMPLIES (IN mci_ NN) (IMPLIES (<= 1 mci_) (IMPLIES (<= mci_ (LENGTH mcl_))
                  (= (NTH mci_ mchs_)
                     (LIST (CTX-ADD (DIFFERENCE mcg_ (PAIR (ENC-IN mcx_ (ENC-UNION mcl_)) (ENC-IN mcx_ (ENC-UNION mcl_))))
                                    (ENC-IN mcx_ (NTH mci_ mcl_)))
                           mcf_))))))))))
(notation! 'REL-UNION-ELIM 'kind 'predicate 'arity 3 'english "the kernel's union-elim relates $2 to $3")

;; rule-checkers-logic.scm 1231-1248 (intersection-intro): the goal (IN x (INTERSECTION S1 .. Sn));
;; one hypothesis per set, the same context, goal (IN x S_i).  n >= 1: make-wff (above).
(def-predicate 'REL-INTERSECTION-INTRO '(mct_ mchs_ mcc_)
  (mc--and '(IN mcc_ SEQ-SET)
    (mc--ex '(mcg_ mcx_ mcl_)
      (mc--and '(= mcc_ (LIST mcg_ (ENC-IN mcx_ (ENC-INTER mcl_)))) '(<= 1 (LENGTH mcl_))
               '(= (LENGTH mchs_) (LENGTH mcl_))
               '(FORALL mci_ (IMPLIES (IN mci_ NN) (IMPLIES (<= 1 mci_) (IMPLIES (<= mci_ (LENGTH mcl_))
                  (= (NTH mci_ mchs_) (LIST mcg_ (ENC-IN mcx_ (NTH mci_ mcl_))))))))))))
(notation! 'REL-INTERSECTION-INTRO 'kind 'predicate 'arity 3 'english "the kernel's intersection-intro relates $2 to $3")

;; rule-checkers-logic.scm 1250-1273 (intersection-elim k): some (IN x (INTERSECTION S1 .. Sn)) in the
;; conclusion context, 1 <= k <= n; one hypothesis, the same goal, the context gains (IN x S_k).
(def-predicate 'REL-INTERSECTION-ELIM '(mct_ mchs_ mcc_)
  (mc--and '(IN mcc_ SEQ-SET)
    (mc--ex '(mcg_ mcf_ mcx_ mcl_ mck_)
      (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(IN (ENC-IN mcx_ (ENC-INTER mcl_)) mcg_)
               '(IN mck_ NN) '(<= 1 mck_) '(<= mck_ (LENGTH mcl_))
               '(= mchs_ (LIST (LIST (CTX-ADD mcg_ (ENC-IN mcx_ (NTH mck_ mcl_))) mcf_)))))))
(notation! 'REL-INTERSECTION-ELIM 'kind 'predicate 'arity 3 'english "the kernel's intersection-elim relates $2 to $3")

;; rule-checkers-logic.scm 1143-1162 (tuples-intro): the goal (IN [e1 .. en] (TUPLES A)); one
;; hypothesis per component, the same context, goal (IN e_i A) (none for the empty tuple).
(def-predicate 'REL-TUPLES-INTRO '(mct_ mchs_ mcc_)
  (mc--and '(IN mcc_ SEQ-SET)
    (mc--ex '(mcg_ mcl_ mca_)
      (mc--and '(= mcc_ (LIST mcg_ (ENC-IN (ENC-LIST mcl_) (ENC-TUPLES mca_))))
               '(= (LENGTH mchs_) (LENGTH mcl_))
               '(FORALL mci_ (IMPLIES (IN mci_ NN) (IMPLIES (<= 1 mci_) (IMPLIES (<= mci_ (LENGTH mcl_))
                  (= (NTH mci_ mchs_) (LIST mcg_ (ENC-IN (NTH mci_ mcl_) mca_)))))))))))
(notation! 'REL-TUPLES-INTRO 'kind 'predicate 'arity 3 'english "the kernel's tuples-intro relates $2 to $3")

;; rule-checkers-logic.scm 1164-1189 (tuples-elim k): some (IN [e1 .. en] (TUPLES A)) in the conclusion
;; context, 1 <= k <= n; one hypothesis, the same goal, the context gains (IN e_k A).
(def-predicate 'REL-TUPLES-ELIM '(mct_ mchs_ mcc_)
  (mc--and '(IN mcc_ SEQ-SET)
    (mc--ex '(mcg_ mcf_ mcl_ mca_ mck_)
      (mc--and '(= mcc_ (LIST mcg_ mcf_)) '(IN (ENC-IN (ENC-LIST mcl_) (ENC-TUPLES mca_)) mcg_)
               '(IN mck_ NN) '(<= 1 mck_) '(<= mck_ (LENGTH mcl_))
               '(= mchs_ (LIST (LIST (CTX-ADD mcg_ (ENC-IN (NTH mck_ mcl_) mca_)) mcf_)))))))
(notation! 'REL-TUPLES-ELIM 'kind 'predicate 'arity 3 'english "the kernel's tuples-elim relates $2 to $3")
