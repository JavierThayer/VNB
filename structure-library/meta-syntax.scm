;;; meta-syntax.scm -- THE SYNTAX OF THE KERNEL AS A VNB OBJECT: locally nameless expressions,
;;; their stages, and the four structural operations FV, SUBST, OPEN, LC.
;;; (docs/meta-k2-admissibility-2026-10-08.md, sections 5 and 6, phase 1: the cost probe.)
;;; DEFINITIONS ONLY; the laws are in theorem-library/meta-syntax-laws.scm.
;;; Agent META-1, 2026-10-08.  Template: structure-library/strand-messages.scm.
;;;
;;; THE NODES.  Every node is a literal LIST whose first entry is a numeral TAG; every other
;;; entry is in NN, a list of nodes, or a node:
;;;     EFVAR(n)          = [0, n]               a free variable, n in NN (a NAME)
;;;     EBVAR(k)          = [1, k]               a bound variable, k in NN (a de Bruijn INDEX)
;;;     ECONST(c)         = [2, c]               an atomic constant, c in NN
;;;     EAPP(h, l)        = [3, h, l]            h in NN a head code, l a list of nodes
;;;     EBIND(h, n, a, b) = [4, h, n, a, b]      h a head code, n in NN the number of variables
;;;                                              bound, a a list of nodes OUTSIDE the binder,
;;;                                              b the body (indices 0 .. n-1 refer to it)
;;; The tags separate the five cases by arithmetic (NTH(1, -) is the tag, and 3 /= 4 is
;;; `arith'); no token set and no token law.  The names of the design note (FV, SUBST, OPEN,
;;; LC, EXPR) are spelled EXPR-FV, EXPR-SUBST, EXPR-OPEN, EXPR-LC, EXPR-SET here: SUBST folds onto
;;; the `subst' tactic, OPEN onto the metric-space vocabulary's `open', and a bare EXPR onto the
;;; Scheme variable name `expr' of the kernel code (CLAUDE.md, Case folding).
;;;
;;; THE STAGES (def-by-nn-recursion, as MSG-STAGE):
;;;     EXPR-STAGE(0)       = {0} x NN  u  {1} x NN  u  {2} x NN
;;;     EXPR-STAGE(succ n)  = S_n  u  {3} x NN x TUPLES(S_n)  u  {4} x NN x NN x TUPLES(S_n) x S_n
;;;     EXPR-SET            = the union over n in NN of EXPR-STAGE(n)          (a def-constant)
;;; {k} is PAIR(k, k).  The products are the n-ary CARTESIAN (membership: the primitive
;;; `cartesian-decompose'); the 5-ary one is a set by replacement (`cartesian5-set', laws file).
;;;
;;; THE RANK.  EXPR-RANK(e) is the least stage index holding e, an IOTA over NN (MSG-RANK's device).
;;;
;;; THE OPERATIONS: ROUTE (A) OF THE BRIEF, a function PER STAGE, with the KEEP CLAUSE.  For each
;;; operation F a def-by-nn-recursion F-STAGE(n) is a VNB-LAMBDA on EXPR-STAGE(n) (OPEN's on
;;; EXPR-STAGE(n) x NN), and
;;;     F-STAGE(succ n)(e) = IF e in S_n THEN F-STAGE(n)(e) ELSE <the APP / BIND case on F-STAGE(n)>
;;; so that F-STAGE(succ n) agrees with F-STAGE(n) on S_n BY CONSTRUCTION (the coherence lemma is
;;; one beta and one IF).  The operation on an expression is read at its RANK:
;;;     F(e) = F-STAGE(EXPR-RANK(e))(e)
;;; and the ELSE branch is the one that fires at the rank (an expression is NEW at its rank).  The
;;; children of an APP / BIND are reached through MAKE-SET(l) (a set-valued F: FV, LC) or through
;;; the list map MAPL / MAPLK below (an expression-valued F: SUBST, OPEN).
;;;
;;;     EXPR-FV(e)          the set of free names            (FV-STAGE)
;;;     EXPR-SUBST(e, m, u) replace EFVAR(m) by u           (SUBST-STAGE, parameters m, u)
;;;     EXPR-OPEN(e, k, u)  replace the index k (k + n under a binder of n) by u   (OPEN-STAGE)
;;;     EXPR-LCD(e)         the depths d at which e is closed: every index j at binder depth
;;;                         dl satisfies j < d + dl                           (LCD-STAGE)
;;;     EXPR-LC(e)          0 in EXPR-LCD(e): locally closed, no dangling index
;;;
;;; THE LIST MAP.  The tree has no map over a list (lists are opaque: LENGTH, NTH, CONS).  MAPL(f, l)
;;; is the IOTA of the list of sets of the length of l whose i-th entry is f(NTH(i, l)); MAPLK(f,
;;; l, k) the same with entries f(NTH(i, l), k).  Existence: tuple-tabulation; uniqueness:
;;; tuple-extensionality (laws file).
;;;
;;; STATEMENT CHECKS.  (1) Every equation here is a definition (def-functoid, def-constant, the
;;; recursion equations of def-by-nn-recursion as `==').  Nothing is asserted.  (2) The IOTAs
;;; (EXPR-RANK, MAPL, MAPLK) have their existence-and-uniqueness obligations discharged in the laws
;;; file under the hypotheses that need them.  (3) BINDERS: every parameter and bound variable is
;;; an mx*_ name, used by no other body in the tree; none folds onto a class name, an accessor or a
;;; registered constant.
;;;
;;; Dependencies: structure-library/ordinals (def-by-nn-recursion), structure-library/list-recursion
;;; (MAKE-SET of a list), the base theory (TUPLES, CARTESIAN, PAIR, LENGTH, NTH, UNION, BIG-UNION,
;;; SEP, IOTA, LIST, IF).  No proof is cited.

;;; -----------------------------------------------------------------------
;;; The five constructors.

(def-functoid 'EFVAR '(mxn_) '(LIST 0 mxn_))
(notation! 'EFVAR 'kind 'functoid 'arity 1 'english "the free variable named $1")
(def-functoid 'EBVAR '(mxk_) '(LIST 1 mxk_))
(notation! 'EBVAR 'kind 'functoid 'arity 1 'english "the bound variable of index $1")
(def-functoid 'ECONST '(mxc_) '(LIST 2 mxc_))
(notation! 'ECONST 'kind 'functoid 'arity 1 'english "the constant of code $1")
(def-functoid 'EAPP '(mxh_ mxl_) '(LIST 3 mxh_ mxl_))
(notation! 'EAPP 'kind 'functoid 'arity 2 'english "the application of the head $1 to the list $2")
(def-functoid 'EBIND '(mxh_ mxn_ mxa_ mxb_) '(LIST 4 mxh_ mxn_ mxa_ mxb_))
(notation! 'EBIND 'kind 'functoid 'arity 4
           'english "the binder $1 of $2 variables over the list $3 with body $4")

;;; -----------------------------------------------------------------------
;;; The stages, the class of expressions, the rank.

(def-by-nn-recursion 'EXPR-STAGE '()
  '(UNION (CARTESIAN (PAIR 0 0) NN) (UNION (CARTESIAN (PAIR 1 1) NN) (CARTESIAN (PAIR 2 2) NN)))
  '(mxn_ mxv_)
  '(UNION mxv_ (UNION (CARTESIAN (PAIR 3 3) NN (TUPLES mxv_))
                      (CARTESIAN (PAIR 4 4) NN NN (TUPLES mxv_) mxv_))))
(notation! 'EXPR-STAGE 'kind 'functoid 'arity 1 'english "the stage $1 of the expressions")

(def-constant 'EXPR-SET
  '(expr-set-def (== EXPR-SET (BIG-UNION mxn_ NN (EXPR-STAGE mxn_)))))
(notation! 'EXPR-SET 'kind 'constant 'arity 0 'english "the expressions")

(def-functoid 'EXPR-RANK '(mxe_)
  '(IOTA mxr_ (AND (IN mxr_ NN)
                   (AND (IN mxe_ (EXPR-STAGE mxr_))
                        (FORALL mxj_ (IMPLIES (IN mxj_ NN)
                                              (IMPLIES (IN mxe_ (EXPR-STAGE mxj_))
                                                       (<= mxr_ mxj_))))))))
(notation! 'EXPR-RANK 'kind 'functoid 'arity 1 'english "the rank of the expression $1")

;;; -----------------------------------------------------------------------
;;; The list maps.

(def-functoid 'MAPL '(mxf_ mxl_)
  '(IOTA mxr_ (AND (IN mxr_ (TUPLES SET))
                   (AND (= (LENGTH mxr_) (LENGTH mxl_))
                        (FORALL mxi_ (IMPLIES (IN mxi_ NN) (IMPLIES (<= 1 mxi_)
                                     (IMPLIES (<= mxi_ (LENGTH mxl_))
                                              (= (NTH mxi_ mxr_) (mxf_ (NTH mxi_ mxl_)))))))))))
(notation! 'MAPL 'kind 'functoid 'arity 2 'english "the list of the values of $1 at the entries of $2")

(def-functoid 'MAPLK '(mxf_ mxl_ mxk_)
  '(IOTA mxr_ (AND (IN mxr_ (TUPLES SET))
                   (AND (= (LENGTH mxr_) (LENGTH mxl_))
                        (FORALL mxi_ (IMPLIES (IN mxi_ NN) (IMPLIES (<= 1 mxi_)
                                     (IMPLIES (<= mxi_ (LENGTH mxl_))
                                              (= (NTH mxi_ mxr_) (mxf_ (NTH mxi_ mxl_) mxk_))))))))))
(notation! 'MAPLK 'kind 'functoid 'arity 3
           'english "the list of the values of $1 at the entries of $2 and at $3")

;;; -----------------------------------------------------------------------
;;; FV: the free names.

(def-by-nn-recursion 'FV-STAGE '()
  '(VNB-LAMBDA mxe_ (EXPR-STAGE 0)
     (IF (= (NTH 1 mxe_) 0) (PAIR (NTH 2 mxe_) (NTH 2 mxe_)) EMPTY-SET))
  '(mxn_ mxv_)
  '(VNB-LAMBDA mxe_ (EXPR-STAGE (succ mxn_))
     (IF (IN mxe_ (EXPR-STAGE mxn_))
         (mxv_ mxe_)
         (IF (= (NTH 1 mxe_) 3)
             (BIG-UNION mxw_ (MAKE-SET (NTH 3 mxe_)) (mxv_ mxw_))
             (UNION (BIG-UNION mxw_ (MAKE-SET (NTH 4 mxe_)) (mxv_ mxw_)) (mxv_ (NTH 5 mxe_)))))))
(notation! 'FV-STAGE 'kind 'functoid 'arity 1 'english "the free-name map on the stage $1")

(def-functoid 'EXPR-FV '(mxe_) '((FV-STAGE (EXPR-RANK mxe_)) mxe_))
(notation! 'EXPR-FV 'kind 'functoid 'arity 1 'english "the free names of $1")

;;; -----------------------------------------------------------------------
;;; SUBST: replace the free variable m by u.

(def-by-nn-recursion 'SUBST-STAGE '(mxm_ mxu_)
  '(VNB-LAMBDA mxe_ (EXPR-STAGE 0) (IF (= mxe_ (LIST 0 mxm_)) mxu_ mxe_))
  '(mxn_ mxv_)
  '(VNB-LAMBDA mxe_ (EXPR-STAGE (succ mxn_))
     (IF (IN mxe_ (EXPR-STAGE mxn_))
         (mxv_ mxe_)
         (IF (= (NTH 1 mxe_) 3)
             (LIST 3 (NTH 2 mxe_) (MAPL mxv_ (NTH 3 mxe_)))
             (LIST 4 (NTH 2 mxe_) (NTH 3 mxe_) (MAPL mxv_ (NTH 4 mxe_)) (mxv_ (NTH 5 mxe_)))))))
(notation! 'SUBST-STAGE 'kind 'functoid 'arity 3
           'english "the map replacing the free variable $1 by $2 on the stage $3")

(def-functoid 'EXPR-SUBST '(mxe_ mxm_ mxu_) '((SUBST-STAGE mxm_ mxu_ (EXPR-RANK mxe_)) mxe_))
(notation! 'EXPR-SUBST 'kind 'functoid 'arity 3
           'english "$1 with the free variable $2 replaced by $3")

;;; The operation as a SET function on EXPR-SET (what MAPL takes; a functoid cannot be passed).
(def-functoid 'SUBST-FUN '(mxm_ mxu_) '(VNB-LAMBDA mxw_ EXPR-SET (EXPR-SUBST mxw_ mxm_ mxu_)))
(notation! 'SUBST-FUN 'kind 'functoid 'arity 2
           'english "the map replacing the free variable $1 by $2")

;;; -----------------------------------------------------------------------
;;; OPEN: replace the index k (k + n under a binder of n variables) by u.

(def-by-nn-recursion 'OPEN-STAGE '(mxu_)
  '(VNB-LAMBDA (LIST mxe_ mxk_) (CARTESIAN (EXPR-STAGE 0) NN)
     (IF (= mxe_ (LIST 1 mxk_)) mxu_ mxe_))
  '(mxn_ mxv_)
  '(VNB-LAMBDA (LIST mxe_ mxk_) (CARTESIAN (EXPR-STAGE (succ mxn_)) NN)
     (IF (IN mxe_ (EXPR-STAGE mxn_))
         (mxv_ mxe_ mxk_)
         (IF (= (NTH 1 mxe_) 3)
             (LIST 3 (NTH 2 mxe_) (MAPLK mxv_ (NTH 3 mxe_) mxk_))
             (LIST 4 (NTH 2 mxe_) (NTH 3 mxe_) (MAPLK mxv_ (NTH 4 mxe_) mxk_)
                   (mxv_ (NTH 5 mxe_) (+ mxk_ (NTH 3 mxe_))))))))
(notation! 'OPEN-STAGE 'kind 'functoid 'arity 2
           'english "the map opening an index with $1 on the stage $2")

(def-functoid 'EXPR-OPEN '(mxe_ mxk_ mxu_) '((OPEN-STAGE mxu_ (EXPR-RANK mxe_)) mxe_ mxk_))
(notation! 'EXPR-OPEN 'kind 'functoid 'arity 3
           'english "$1 with the index $2 opened by $3")

;;; The operation as a SET function on EXPR-SET x NN (what MAPLK takes).
(def-functoid 'OPEN-FUN '(mxu_)
  '(VNB-LAMBDA (LIST mxw_ mxj_) (CARTESIAN EXPR-SET NN) (EXPR-OPEN mxw_ mxj_ mxu_)))
(notation! 'OPEN-FUN 'kind 'functoid 'arity 1 'english "the map opening an index with $1")

;;; -----------------------------------------------------------------------
;;; LC: the closing depths, and local closure.

(def-by-nn-recursion 'LCD-STAGE '()
  '(VNB-LAMBDA mxe_ (EXPR-STAGE 0)
     (IF (= (NTH 1 mxe_) 1) (SEP mxd_ NN (< (NTH 2 mxe_) mxd_)) NN))
  '(mxn_ mxv_)
  '(VNB-LAMBDA mxe_ (EXPR-STAGE (succ mxn_))
     (IF (IN mxe_ (EXPR-STAGE mxn_))
         (mxv_ mxe_)
         (IF (= (NTH 1 mxe_) 3)
             (SEP mxd_ NN (FORALL mxw_ (IMPLIES (IN mxw_ (MAKE-SET (NTH 3 mxe_))) (IN mxd_ (mxv_ mxw_)))))
             (SEP mxd_ NN (AND (FORALL mxw_ (IMPLIES (IN mxw_ (MAKE-SET (NTH 4 mxe_)))
                                                     (IN mxd_ (mxv_ mxw_))))
                               (IN (+ mxd_ (NTH 3 mxe_)) (mxv_ (NTH 5 mxe_)))))))))
(notation! 'LCD-STAGE 'kind 'functoid 'arity 1 'english "the closing-depth map on the stage $1")

(def-functoid 'EXPR-LCD '(mxe_) '((LCD-STAGE (EXPR-RANK mxe_)) mxe_))
(notation! 'EXPR-LCD 'kind 'functoid 'arity 1 'english "the depths at which $1 is closed")

(def-predicate 'EXPR-LC '(mxe_) '(IN 0 (EXPR-LCD mxe_)))
(notation! 'EXPR-LC 'kind 'predicate 'arity 1 'english "$1 is locally closed")
