;;; group-zpow-vocab.scm -- integer powers in a group (ALGNUM, 2026-10-27).  DEFINITIONS ONLY.  Library: algebra.
;;; Built ON worker-04's GPOW (cg4-vocab.scm: x^n for n in NN, x^0 = e, x^(n+1) = x x^n), one name per notion:
;;;   GROUP-ZPOW(g, x, k)   x^k for k in ZZ: x^k = GPOW(g, x, k) for k >= 0, the inverse of x^(-k) for k < 0.
(def-functoid 'GROUP-ZPOW '(g x k)
  '(IF (<= 0 k) (GPOW g x k) ((INV g) (GPOW g x (- 0 k)))))
(notation! 'GROUP-ZPOW 'kind 'functoid 'arity 3 'english "the $3-th power of $2 in $1 (an integer exponent)")
;;;   IS-ELEMENT-ORDER(g, x, d)   d is the order of x: d >= 1, x^d = e, and no smaller positive power of x is e
(def-predicate 'IS-ELEMENT-ORDER '(g x d)
  '(AND (IN d NN) (AND (<= 1 d) (AND (= (GPOW g x d) (IDEN g))
        (FORALL eod_ (IMPLIES (IN eod_ NN) (IMPLIES (<= 1 eod_) (IMPLIES (= (GPOW g x eod_) (IDEN g)) (<= d eod_)))))))))
(notation! 'IS-ELEMENT-ORDER 'kind 'predicate 'arity 3 'english "$3 is the order of $2 in $1")
;;;   IS-GENERATOR(g, x)          x generates g: every element of g is x^k for some integer k (the notes, section 7)
(def-predicate 'IS-GENERATOR '(g x)
  '(AND (IN x (CARR g)) (FORALL geny_ (IMPLIES (IN geny_ (CARR g)) (FORSOME genk_ (AND (IN genk_ ZZ) (= geny_ (GROUP-ZPOW g x genk_))))))))
(notation! 'IS-GENERATOR 'kind 'predicate 'arity 2 'english "$2 generates the group $1")
;;;   GROUP-PROD(X, Y)            the direct product X x Y of two groups: carrier CARTESIAN(CARR X, CARR Y), the
;;;                               operations componentwise (modelled on RING-PROD, ring.scm)
(def-functoid 'GROUP-PROD '(X Y)
  '(LIST
     (CARTESIAN (CARR X) (CARR Y))
     (VNB-LAMBDA (LIST gpp_ gpq_) (CARTESIAN (CARTESIAN (CARR X) (CARR Y)) (CARTESIAN (CARR X) (CARR Y)))
       (LIST ((OPR X) (NTH 1 gpp_) (NTH 1 gpq_))
             ((OPR Y) (NTH 2 gpp_) (NTH 2 gpq_))))
     (LIST (IDEN X) (IDEN Y))
     (VNB-LAMBDA gpp_ (CARTESIAN (CARR X) (CARR Y))
       (LIST ((INV X) (NTH 1 gpp_))
             ((INV Y) (NTH 2 gpp_))))))
(notation! 'GROUP-PROD 'kind 'functoid 'arity 2 'english "the direct product of the groups $1 and $2")
;;;   TRIV-GROUP                  the trivial group {0}
(def-constant 'TRIV-GROUP
  (list 'triv-group-def
        '(= TRIV-GROUP
            (LIST (PAIR 0 0)
                  (VNB-LAMBDA (LIST tgp_ tgq_) (CARTESIAN (PAIR 0 0) (PAIR 0 0)) 0)
                  0
                  (VNB-LAMBDA tgp_ (PAIR 0 0) 0)))))
(notation! 'TRIV-GROUP 'kind 'constant 'english "the trivial group")
;;;   GROUP-FAMPROD(gf, m)        G_1 x ... x G_m for the family i |-> gf(i): the iterated GROUP-PROD, from TRIV-GROUP
;;;   GROUP-FAMTUPLE(xf, m)       the element (x_1, ..., x_m) of it, nested the same way
(def-by-nn-recursion 'GROUP-FAMPROD '(gfam_) 'TRIV-GROUP '(gfn_ gfv_) '(GROUP-PROD gfv_ (gfam_ (succ gfn_))))
(notation! 'GROUP-FAMPROD 'kind 'functoid 'arity 2 'english "the product of the groups $1(1), ..., $1($2)")
(def-by-nn-recursion 'GROUP-FAMTUPLE '(xfam_) 0 '(xfn_ xfv_) '(LIST xfv_ (xfam_ (succ xfn_))))
(notation! 'GROUP-FAMTUPLE 'kind 'functoid 'arity 2 'english "the tuple ($1(1), ..., $1($2))")
