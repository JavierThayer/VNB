;;; cg2-vocab.scm -- set products and set powers in a group (compact-groups notes, Prop 5.8:
;;; H = union of the V^k).  DEFINITIONS ONLY.  Agent ISOM, 2026-10-26 (the user's to confirm).
;;;
;;;   SET-PROD(g, A, B)    = { a b : a in A, b in B }, a SEP over CARR(g)
;;;   SET-POWER(g, V, k)   = V^k by recursion on k: V^0 = {e}, V^(k+1) = V^k V
;;;                          (def-by-nn-recursion: the two equations set-power-zero /
;;;                          set-power-succ, definitional, quasi-equalities)
;;;   POWERS-UNION(g, V)   = the union of the V^k, k in NN (the notes' union over k >= 1;
;;;                          the same set when e is in V, since V^0 = {e} lies in V^1)
;;; The accessors are CARR, OPR, IDEN: the definitions read the same on a GROUP and on a
;;; TOP-GROUP (slots 1-3 in both).
;;; BINDERS: spg_ spa_ spb_ spz_ spx_ spy_ sqg_ sqv_ sqk_ sqval_ pug_ puv_ puk_.
(def-functoid 'SET-PROD '(spg_ spa_ spb_)
  '(SEP spz_ (CARR spg_) (FORSOME spx_ (AND (IN spx_ spa_) (FORSOME spy_ (AND (IN spy_ spb_) (= spz_ ((OPR spg_) spx_ spy_))))))))
(notation! 'SET-PROD 'kind 'functoid 'arity 3 'english "the product set $2 $3 in $1")
(def-by-nn-recursion 'SET-POWER '(sqg_ sqv_)
  '(SINGLETON (IDEN sqg_))
  '(sqk_ sqval_)
  '(SET-PROD sqg_ sqval_ sqv_))
(notation! 'SET-POWER 'kind 'functoid 'arity 3 'english "the $3-th power of the set $2 in $1")
(def-functoid 'POWERS-UNION '(pug_ puv_)
  '(BIG-UNION puk_ NN (SET-POWER pug_ puv_ puk_)))
(notation! 'POWERS-UNION 'kind 'functoid 'arity 2 'english "the union of the powers of $2 in $1")

;;; ---------------------------------------------------------------------------------------------
;;; MOVED HERE 2026-10-27 (integration) from cg1-vocab.scm (library analysis), text unchanged:
;;;   IS-SUBGROUP(g, H), IS-NORMAL-SUBGROUP(g, H)
;;;       H inside CARR g contains e and is closed under the product and the inverse; normal:
;;;       also under conjugation u h u^-1.   BINDERS: sgg_ sgh_ sga_ sgb_ sgu_.
(def-predicate 'IS-SUBGROUP '(sgg_ sgh_)
  '(AND (SUBSET sgh_ (CARR sgg_)) (AND (IN (IDEN sgg_) sgh_)
     (AND (FORALL sga_ (IMPLIES (IN sga_ sgh_) (FORALL sgb_ (IMPLIES (IN sgb_ sgh_) (IN ((OPR sgg_) sga_ sgb_) sgh_)))))
          (FORALL sga_ (IMPLIES (IN sga_ sgh_) (IN ((INV sgg_) sga_) sgh_)))))))
(notation! 'IS-SUBGROUP 'kind 'predicate 'arity 2 'english "$2 is a subgroup of $1")
(def-predicate 'IS-NORMAL-SUBGROUP '(sgg_ sgh_)
  '(AND (IS-SUBGROUP sgg_ sgh_)
     (FORALL sgu_ (IMPLIES (IN sgu_ (CARR sgg_)) (FORALL sga_ (IMPLIES (IN sga_ sgh_)
       (IN ((OPR sgg_) ((OPR sgg_) sgu_ sga_) ((INV sgg_) sgu_)) sgh_)))))))
(notation! 'IS-NORMAL-SUBGROUP 'kind 'predicate 'arity 2 'english "$2 is a normal subgroup of $1")

;;; MOVED HERE 2026-10-27 (integration) from cg4-vocab.scm (library analysis), text unchanged:
;;;   GPOW(g, x, n)  x^n in the group g, n in NN: x^0 = e, x^(n+1) = x x^n (def-by-nn-recursion;
;;;                  gpow-zero / gpow-succ).   BINDERS: gpg_ gpx_ gpn_ gpv_.
(def-by-nn-recursion 'GPOW '(gpg_ gpx_)
  '(IDEN gpg_)
  '(gpn_ gpv_)
  '((OPR gpg_) gpx_ gpv_))
(notation! 'GPOW 'kind 'functoid 'arity 3 'english "the $3-th power of $2 in $1")

;;; MOVED HERE 2026-10-27 (integration) from tg-vocab.scm (library analysis), text unchanged:
;;;   GRP-MONOID(g)  the monoid underlying the group g: [CARR, OPR, IDEN].   BINDERS: gmg_.
(def-functoid 'GRP-MONOID '(gmg_)
  '(LIST (CARR gmg_) (OPR gmg_) (IDEN gmg_)))
(notation! 'GRP-MONOID 'kind 'functoid 'arity 1 'english "the monoid underlying the group $1")
