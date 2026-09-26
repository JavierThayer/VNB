;;; cc-pi.scm -- THE CONSTANT pi, DEFINED FROM THE KERNEL OF exp (the notes 2.3.3).
;;; DEFINITION ONLY; existence, uniqueness and the characterisation `pi-spec'
;;; are PROVEN in theorem-library/cc-exp-kernel.scm.
;;; Batch 31-B, 2026-09-25.
;;;
;;; THE USER'S DEFINITION (2026-09-25): pi is the generator of the kernel
;;; K = {z in CC : exp z = 1} lying in the upper half plane, divided by 2i.
;;; Equivalently -- the form used here -- PI is THE positive real p such that
;;;     K = {k * (2 p i) : k in ZZ},
;;; i.e. p in RR, 0 < p, and for every complex z,  exp z = 1  iff  z = k (2 p i)
;;; for some integer k.  (If K = ZZ g with Im g > 0 then g = 2 p i with
;;; p = Im g / 2: K lies on the imaginary axis, cc-exp-kernel-imaginary.)
;;;
;;; THE SHAPE.  A parameterless defined object is a `def-constant' (CLAUDE.md:
;;; never a def-functoid with an empty parameter list), IOTA-bodied, on the model
;;; of ESUP (theorem-library/rake-esup-defined.scm): the defining equation
;;; `pi-def' is installed as a definitional theorem, and the description is
;;; SATISFIABLE and UNIQUE by theorems proven before any use of PI:
;;;   cc-pi-exists   exists p with the property  (cc-exp-kernel.scm)
;;;   cc-pi-unique   two such p are equal        (cc-exp-kernel.scm)
;;; `pi-spec' (the property of PI) follows by `iota-d' from the two.
;;;
;;; The binders cekp_, cekz_, cekk_ are bound by nothing else in the tree.
;;; `%pi' in a parsed string reads as the symbol `pi', i.e. this constant.
;;; A binder spelled `pi' now folds onto this registered constant:
;;; theorem-library/rake-combinatorics2.scm:596 binds `pi' (FORALL pi ...), which
;;; the fatal constant-binder-audit will report once this file loads; that binder
;;; must be renamed (scratchpad/rename-sym.py) when this file is wired.
;;;
;;; Dependencies: structure-library/cc-elementary.scm (CC-EXP).

(def-constant 'PI
  (list 'pi-def
        '(== PI
             (IOTA cekp_
               (AND (IN cekp_ RR)
                    (AND (< 0 cekp_)
                         (FORALL cekz_
                           (IMPLIES (IN cekz_ CC)
                             (IFF (= (CC-EXP cekz_) 1)
                                  (FORSOME cekk_
                                    (AND (IN cekk_ ZZ)
                                         (= cekz_ (* cekk_ (* (* 2 cekp_) +i))))))))))))))
