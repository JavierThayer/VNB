;;; set-basics.scm -- the NBG facts about SET that the kernel rules do not give.
;;;
;;; VNB's kernel has separation (pi-sep-sethood!: {z in A : p} is a set when A
;;; is), power set, pairing, big-union.  What it does not have, and what every
;;; argument that carves a class out of a set eventually wants, is the NBG
;;; principle that a class INCLUDED in a set is itself a set.
;;;
;;; It went missing until the METRIC-TOP typing proof needed it (a subfamily of
;;; the topology has to be a set before BIG-UNION's sethood rule will look at it),
;;; and its absence is exactly the kind of triviality that has no business being
;;; an obstacle.

;;; subclass-of-set-is-set: A subset B, B a set => A a set.
(support 'subclass-of-set-is-set
  '(FORALL A (FORALL B
     (IMPLIES (IN B SET)
       (IMPLIES (SUBSET A B)
         (IN A SET))))))
(warrant! 'subclass-of-set-is-set 'proof
  "NBG: A is included in the set B, so A = {z in B : z in A} -- the two classes have the same members, and class-extensionality identifies them.  The right-hand side is a set by separation (pi-sep-sethood!, B being a set).  Stated rather than derived only because the SEP-then-extensionality step is pure bookkeeping.")
