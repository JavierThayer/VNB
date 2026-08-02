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

;;; subclass-of-set-is-set MOVED and PROVEN, 2026-07-27.  It was asserted here
;;; with a `proof' warrant whose text WAS the derivation; the derivation is now
;;; run, in theorem-library/subset-lemmas.scm.  The statement could not live here
;;; and be proved here: `sp'/`qed' arrive at load.scm:388 and this file loads at
;;; 70.  Nothing else in this file needs it, so the file is now empty of claims.
