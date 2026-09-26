;;; ag-view-read-offs.scm -- THE ADDITIVE-GROUP VIEW READ-OFFS, PROVEN.
;;;
;;; Two `def-functor' views send a structure to its underlying ABELIAN-GROUP:
;;;
;;;     RING-ADDITIVE-AG(A)   = [carr(A), add(A),  zero(A),  neg(A)]   (views.scm:27)
;;;     MODULE-VECTOR-AG(md)  = [vec(md), vadd(md), vzero(md), vneg(md)] (views.scm:191)
;;;
;;; and ABELIAN-GROUP's slot order is (CARR OPR IDEN INV).  So reading a slot of
;;; either view -- `carr(ring-additive-ag(A))', `opr(module-vector-ag(md))' --
;;; ought to give back the source structure's own operation.  `def-functor'
;;; installs a functoid and a typing axiom and NO read-off, so until this file
;;; the six equations were ASSERTED supports (matrix.scm:400-408 for the ras-
;;; three, mod-seq.scm:55-67 for the mvag- three), each carrying a `proof'
;;; warrant whose text recited a derivation nobody had run.  They are cited at
;;; 33 sites in 11 files and appear in 12 bills.
;;;
;;; THE STATEMENT CHANGED, AND IT HAD TO.  The retired supports were UNGUARDED:
;;;
;;;     forall A. carr(ring-additive-ag(A)) = carr(A)
;;;
;;; for an ARBITRARY A, ring or not.  `=' is the partial-equality predicate --
;;; `t = t' ASSERTS that t denotes (primitive-inferences.scm, `pi-reflexivity!'
;;; and `term-self-defined?') -- so the unguarded form claims that `nth(1, A)'
;;; denotes for every object A whatsoever, which no proof can deliver and which
;;; is not what anyone meant.  Each statement below therefore carries the guard
;;; that makes its terms denote, and keeps `=':
;;;
;;;     forall A.  is-ring(A)   => carr(ring-additive-ag(A)) = carr(A)
;;;     forall md. is-module(md) => carr(module-vector-ag(md)) = vec(md)
;;;
;;; The guard is not a weakening in practice: every one of the 33 citation sites
;;; is inside a proof that already has `is-ring' / `is-module' of the structure
;;; in hand, so `fact' auto-detaches it.
;;;
;;; WHY NOT `=='.  The sibling read-off files (normed-field-ring-view.scm,
;;; nvs-module-view.scm) state theirs with `==' and owe no definedness at all.
;;; That was declined here (the user's call, 2026-09-15): these six are about
;;; the additive group OF A RING and the vector group OF A MODULE, the guard is
;;; what makes the terms denote, and a guarded `=' says both things at once.
;;;
;;; NOTHING HERE IS ASSERTED.  The proof is the functoid unfold composed with an
;;; NTH projection -- both trusted base -- plus the structure predicate's own
;;; definition for the definedness obligation.  `is-ring' / `is-module' are the
;;; auto-generated IS-X IFFs, installed `definitional' by `def-structure'
;;; (structures.scm:640), so they contribute {} to every bill: all six are
;;; `proven modulo 0'.
;;;
;;; THE SHAPE OF A PROOF, and the one place it is not uniform:
;;;
;;;     (di) (di)                peel the binder, then land the guard -- the
;;;                              antecedent is not a typing, so one call takes
;;;                              the quantifier only (CLAUDE.md, "a GUARDED
;;;                              universal goes whole under one `di'")
;;;     (mac-h 'is-ring ...)     unfold the guard
;;;     (dk-split-all!)          its conjuncts, including the typing of the slot
;;;     (slot ACC)               the target accessor down to (NTH k _)
;;;     (mac 'RING-ADDITIVE-AG)  the functoid unfold
;;;     (nth-r)                  NTH k of a LIST literal -- the source term
;;;     (rfl)                    closed by the typing conjunct just landed
;;;
;;; `ras-carr' needs two extra steps and the reason is worth stating: its target
;;; accessor and its source accessor are the SAME symbol, CARR.  A macete
;;; rewrites EVERY occurrence, so the opening `(slot 'CARR)' takes the goal's
;;; right-hand side `carr(A)' to `nth(1, A)' along with the left, and after the
;;; NTH reduction the goal reads `carr(A) = nth(1, A)' -- true, and not closable
;;; by `rfl' while the two sides are different S-expressions.  The right-hand
;;; side is put BACK with a `have!' of `nth(1, A) == carr(A)' (proved on its own
;;; side branch by the same accessor macete) and one `subst'.  The other five
;;; read a slot whose source name differs from its target name (CARR/VEC,
;;; OPR/ADD, OPR/VADD, IDEN/ZERO, IDEN/VZERO), so their right-hand side is
;;; untouched and the typing conjunct closes them directly.
;;;
;;; Dependencies: views.scm (both def-functors), ring.scm / module.scm (the two
;;; IS-X definitions), interactive + proof-debt + driver-kit.  No structure of
;;; this file's own.  Must load before the earliest citer, theorem-library/
;;; lam-fun-bricks.scm.

;;; ---- file-local driver (the `avr-' prefix; `slot' is a tactic and single or
;;; ---- double capitals are the case-fold danger zone).

;;; (avr-read-off! NAME VAR IS-PRED IS-MAC VIEW ACC VAL WITNESS)
;;;   NAME    the theorem name
;;;   VAR     the universally quantified structure variable
;;;   IS-PRED the guard, e.g. (IS-RING A)
;;;   IS-MAC  the macete that unfolds it, e.g. 'is-ring
;;;   VIEW    the def-functor head, e.g. 'RING-ADDITIVE-AG
;;;   ACC     the ABELIAN-GROUP accessor being read, e.g. 'CARR
;;;   VAL     the source term it should equal, e.g. (CARR A)
;;;   WITNESS the conjunct of the IS-X unfold that types VAL, which is what
;;;           discharges rfl's definedness obligation.  Errors if it is not in
;;;           the context: a silent miss would leave the leaf open and say
;;;           nothing until the qed.
(define (avr-read-off! name var is-pred is-mac view acc val witness)
  (sp (make-wff (list 'FORALL var
                  (list 'IMPLIES is-pred
                    (list '= (list acc (list view var)) val)))))
  (di)                                  ; the binder
  (di)                                  ; the guard -- its antecedent is not a
                                        ; typing, so one `di' does not take both
  (mac-h is-mac is-pred)
  (dk-split-all!)
  (if (not (member witness (dk-asms)))
      (error "avr-read-off!: the typing conjunct is not in the context"
             name (expression->string witness)))
  (slot acc)                            ; the accessor down to (NTH k _)
  (mac view)                            ; the functoid unfold
  (nth-r)                               ; NTH k of the LIST literal
  (if (eq? (car val) acc)
      ;; SAME SYMBOL BOTH SIDES (ras-carr: CARR read off CARR).  The opening
      ;; `slot' rewrote the goal's right-hand side too, so the goal now reads
      ;; VAL = (NTH k VAR) rather than VAL = VAL.  Put the right-hand side back:
      ;; the projection equation is proved on its own side branch by the same
      ;; accessor macete, and one `subst' undoes it in the goal.  `slot-h' is NOT
      ;; the door here -- it has no accessor fallback and dies with
      ;; "mac-h: unknown theorem/macete: carr" (CLAUDE.md).
      (let ((proj (caddr (dk-goal))))   ; (NTH k VAR)
        (have! (list '== proj val) (lambda () (slot acc) (qrfl)))
        (subst (list '== proj val))))
  (rfl)
  (if (not (proof-done? *ps*))
      (error "avr-read-off!: proof did not close" name (dk-goal)))
  (qed name))

;;; =====================================================================
;;; (1) RING-ADDITIVE-AG -- the additive group of a ring.
;;; =====================================================================

(avr-read-off! 'ras-carr 'A '(IS-RING A) 'is-ring 'RING-ADDITIVE-AG
               'CARR '(CARR A) '(IN (CARR A) SET))

(avr-read-off! 'ras-op 'A '(IS-RING A) 'is-ring 'RING-ADDITIVE-AG
               'OPR '(ADD A)
               '(IN (ADD A) (FUN (CARTESIAN (CARR A) (CARR A)) (CARR A))))

(avr-read-off! 'ras-id 'A '(IS-RING A) 'is-ring 'RING-ADDITIVE-AG
               'IDEN '(ZERO A) '(IN (ZERO A) (CARR A)))

;;; =====================================================================
;;; (2) MODULE-VECTOR-AG -- the vector group of a module.
;;; =====================================================================

(avr-read-off! 'mvag-carr 'md '(IS-MODULE md) 'is-module 'MODULE-VECTOR-AG
               'CARR '(VEC md) '(IN (VEC md) SET))

(avr-read-off! 'mvag-op 'md '(IS-MODULE md) 'is-module 'MODULE-VECTOR-AG
               'OPR '(VADD md)
               '(IN (VADD md) (FUN (CARTESIAN (VEC md) (VEC md)) (VEC md))))

(avr-read-off! 'mvag-id 'md '(IS-MODULE md) 'is-module 'MODULE-VECTOR-AG
               'IDEN '(VZERO md) '(IN (VZERO md) (VEC md)))
