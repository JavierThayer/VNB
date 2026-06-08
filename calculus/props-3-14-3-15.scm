;;; calculus/props-3-14-3-15.scm
;;; ====================================================================
;;; A runnable demonstration of Propositions 3.14 and 3.15 of
;;; docs/calculus.pdf in the VNB prover -- the SUCCESSES and the
;;; instructive FAILURES from the 2026-06-08 probe.  Scratch/teaching
;;; script, NOT part of load.scm.  The axioms it uses live in
;;; structure-library/metric-open-sets.scm (IS-OPEN/IS-CLOSED/PREIMAGE +
;;; the four characterisation supports) and structure-library/compose.scm.
;;;
;;; Run it (fast -- skips the load-time library proofs):
;;;   cd ~/prover
;;;   VNB_SKIP_PROOFS=1 ./prover -i calculus/props-3-14-3-15.scm < /dev/null
;;; then grep the output for "==>".
;;;
;;; The maths:
;;;   Def 3.13  f continuous at a:  forall e>0 exists d>0.
;;;             d_X(x,a)<=d ==> d_Y(f x,f a)<=e.            [IS-CONTINUOUS-AT]
;;;   Prop 3.14 f continuous at a <=> for every sequence x_n -> a,
;;;             f(x_n) -> f(a).                              [sequential]
;;;   Prop 3.15 TFAE: (1) f continuous; (2) preimage of every closed set is
;;;             closed; (3) preimage of every open set is open.
;;; ====================================================================

(define (==> label val)
  (display "==> ") (display label) (display ": ") (write val) (newline))
(define (--- title)
  (newline) (display ";;; ----- ") (display title) (display " -----") (newline))

;;; A robustness helper, and itself a lesson: bc* needs values for any of a
;;; cited theorem's schema variables that don't occur in its conclusion (here
;;; the codomain space `t').  You CANNOT hardcode the internal name -- VNB's
;;; fresh-var counter is global, so the goal's `t' is t_1 only in the FIRST
;;; proof of a session and drifts thereafter (see FAILURE B).  So read it back
;;; from context at runtime: asm-arg pulls argument ARGPOS (0-based) out of the
;;; first assumption headed by HEAD.  For IS-CONTINUOUS(s,t,f), arg 2 is t.
(define (asm-arg head argpos)
  (let loop ((as (sequent-node-assumptions (proof-state-focus *ps*))))
    (if (null? as) (error "asm-arg: no assumption headed by" head)
        (let ((f (wff-formula (car as))))
          (if (and (pair? f) (eq? (car f) head)) (list-ref f argpos)
              (loop (cdr as)))))))

;;; ====================================================================
;;; SUCCESS 1.  Prop 3.15, (1) => (3): a continuous map pulls open sets
;;; back to open sets.  Closes by citing the warranted support
;;; continuous-implies-open-preimage, supplying the codomain space t from
;;; context.  (The full biconditional closes too; the single direction is
;;; shown so focus/`ass' juggling doesn't distract.)
;;; ====================================================================
(--- "SUCCESS 1: Prop 3.15 (1)=>(3), open preimage")
(sp (make-wff '(FORALL s (FORALL t (FORALL f
   (IMPLIES (IS-CONTINUOUS s t f)
     (FORALL V (IMPLIES (IS-OPEN t V) (IS-OPEN s (PREIMAGE s f V))))))))))
(di)(di)(di)(di)
(bc* 'continuous-implies-open-preimage ((t (asm-arg 'is-continuous 2))))
(ass-all)
(==> "continuity => open-preimage closes" (proof-done? *ps*))

;;; ====================================================================
;;; SUCCESS 2.  Prop 3.15, (1) => (2): the NEW closed-set machinery.  Same
;;; shape as SUCCESS 1 with IS-CLOSED in place of IS-OPEN; cites
;;; continuous-implies-closed-preimage.  (Earlier I wrongly reported this
;;; as a bc* bug -- that was the t-name drift below, not the support.)
;;; ====================================================================
(--- "SUCCESS 2: Prop 3.15 (1)=>(2), closed preimage [new]")
(sp (make-wff '(FORALL s (FORALL t (FORALL f
   (IMPLIES (IS-CONTINUOUS s t f)
     (FORALL A (IMPLIES (IS-CLOSED t A) (IS-CLOSED s (PREIMAGE s f A))))))))))
(di)(di)(di)(di)
(bc* 'continuous-implies-closed-preimage ((t (asm-arg 'is-continuous 2))))
(ass-all)
(==> "continuity => closed-preimage closes" (proof-done? *ps*))

;;; ====================================================================
;;; SUCCESS 3.  COMPOSE is DEFINITIONAL -- COMPOSE(f,g) := VNB-LAMBDA z. f(g z)
;;; -- so the apply law (f o g)(x) = f(g(x)) is a genuine proof, not an
;;; asserted axiom: unfold COMPOSE, beta-reduce, reflexivity.  No typing
;;; hypotheses (pure beta).
;;; ====================================================================
(--- "SUCCESS 3: compose-apply proves by beta")
(sp (make-wff '(= ((COMPOSE f g) x) (f (g x)))))
(mac 'COMPOSE) (lam-b) (rfl)
(==> "(COMPOSE f g)(x) = f(g(x)) proves" (proof-done? *ps*))

;;; ====================================================================
;;; SUCCESS 4.  compose-type reduces by lambda-type (lam-t): the function-
;;; membership goal becomes the pointwise obligation, which fun-codomain-iff
;;; discharges.  (Shown reduced, not ground to QED.)
;;; ====================================================================
(--- "SUCCESS 4: compose-type reduces via lam-t")
(sp (make-wff '(FORALL A (FORALL B (FORALL C (FORALL f (FORALL g
   (IMPLIES (AND (IN g (FUN A B)) (IN f (FUN B C)))
     (IN (COMPOSE f g) (FUN A C))))))))))
(di)(di) (mac 'COMPOSE) (lam-t)
(==> "compose-type goal after lam-t"
     (expression->string (sequent-node-assertion (proof-state-focus *ps*))))

;;; ====================================================================
;;; SUCCESS 5.  IS-CLOSED unfolds to subset + complement-open.
;;; ====================================================================
(--- "SUCCESS 5: IS-CLOSED unfolds")
(sp (make-wff '(IS-CLOSED s A)))
(mac 'IS-CLOSED)
(==> "IS-CLOSED(s,A) unfolds to"
     (expression->string (sequent-node-assertion (proof-state-focus *ps*))))

;;; ====================================================================
;;; SUCCESS 6.  Prop 3.14 is NATIVELY statable: with COMPOSE the composite
;;; sequence n |-> f(g(n)) is a real term, so no Skolem stand-in is needed.
;;; (Before COMPOSE/VNB-LAMBDA this could not be written at all.)
;;; ====================================================================
(--- "SUCCESS 6: Prop 3.14 statable with COMPOSE")
(==> "native 3.14 statement is a wff"
     (and (make-wff '(IMPLIES (AND (IS-CONTINUOUS-AT s t f a) (CONVERGES-TO s g a))
                       (CONVERGES-TO t (COMPOSE f g) (f a)))) #t))

;;; ====================================================================
;;; SUCCESS 7.  The hypothesis-side machinery 3.14's full proof needs DOES
;;; exist -- under the terse name `ai' (antecedent-inference), the dual of
;;; `di'.  Here it eliminates an existential HYPOTHESIS, introducing a fresh
;;; eigenvariable (the "let d be the witness" step).  ai also splits
;;; AND-hypotheses and case-splits OR.
;;; ====================================================================
(--- "SUCCESS 7: ai eliminates an existential hypothesis")
(sp (make-wff '(IMPLIES (FORSOME x (P x)) (FORSOME y (P y)))))
(di) (ai '(FORSOME x (P x)))
(==> "ai introduced a fresh witness; goal now"
     (expression->string (sequent-node-assertion (proof-state-focus *ps*))))

;;; ====================================================================
;;; FAILURE A (soft, runs live).  Cite a support but DON'T supply its
;;; hypothesis-only variable: the prover refuses and says exactly what is
;;; missing.  Watch for ";VNB warning: ... undetermined schema var(s) (t)".
;;; ====================================================================
(--- "FAILURE A: bare bc* leaves t undetermined")
(sp (make-wff '(FORALL s (FORALL t (FORALL f
   (IMPLIES (IS-CONTINUOUS s t f)
     (FORALL V (IMPLIES (IS-OPEN t V) (IS-OPEN s (PREIMAGE s f V))))))))))
(di)(di)(di)(di)
(bc* 'continuous-implies-open-preimage)       ; no binding -> warns
(==> "bare bc* advanced the proof? (expect #f)" (proof-done? *ps*))

;;; ====================================================================
;;; FAILURE B (runs live).  THE drift trap, and why the helper exists.
;;; The identical SUCCESS 1 proof, but with the binding HARDCODED to 't_1
;;; instead of read from context.  VNB's fresh-var counter is GLOBAL, so
;;; the goal's codomain variable is t_1 only in the first proof of a
;;; session; by now it has drifted.  We print the goal's ACTUAL t next to
;;; the hardcoded 't_1 -- they differ, so the binding misses and the proof
;;; does not close, even though SUCCESS 1 (same proof, asm-arg) did.
;;; ====================================================================
(--- "FAILURE B: hardcoded schema-var name drifts; helper reads it instead")
(sp (make-wff '(FORALL s (FORALL t (FORALL f
   (IMPLIES (IS-CONTINUOUS s t f)
     (FORALL V (IMPLIES (IS-OPEN t V) (IS-OPEN s (PREIMAGE s f V))))))))))
(di)(di)(di)(di)
(==> "goal's ACTUAL t variable here" (asm-arg 'is-continuous 2))
(==> "but the hardcoded binding says" 't_1)
(bc* 'continuous-implies-open-preimage ((t 't_1)))   ; HARDCODED -> mismatch
(ass-all)
(==> "hardcoded 't_1 closes? (expect #f -- drift)" (proof-done? *ps*))

;;; ====================================================================
;;; FAILURE C (documented, NOT executed -- Scheme-level errors that would
;;; abort the script).  Two bc* surface-syntax stumbles:
;;;
;;;   (bc* 'continuous-implies-open-preimage '())
;;;        => ;Ill-formed special form  -- bc* is a macro; the binding slot
;;;           must be ()  NOT  '()  (the quote breaks expansion).
;;;
;;;   (bc* 'continuous-implies-open-preimage ((t t_1)))
;;;        => ;Unbound variable: t_1   -- binding VALUES are evaluated as
;;;           Scheme, so an internal goal var must be QUOTED:  ((t 't_1))
;;;           (and even then it drifts -- see FAILURE B; prefer asm-arg).
;;;
;;; Also: `lookup-theorem` THROWS on a miss (use hash-table-ref/default).
;;; ====================================================================

;;; ====================================================================
;;; NOT ATTEMPTED.  Prop 3.14's full e-d proof is a long manual natural-
;;; deduction grind (flatten the unfolded conjunctive hypothesis with
;;; repeated ai; inst the buried `forall e' clauses; ai the resulting
;;; `exists d'/`exists N' to name witnesses; ew the witness; thread the
;;; <= chain with metric-sym + metric-triangle).  Every rule it needs
;;; exists; only the automation is missing.  Deliberately left unground.
;;; ====================================================================
(--- "DONE")
(==> "demo finished" 'ok)
