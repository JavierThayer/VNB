;;; seminorm-scalar-field-drive.scm -- THE LEAF LEFT FOR THE USER (2026-08-24).
;;;
;;; IS-SEMINORM, IS-SEMINORM-FAMILY and IS-FRECHET-STRUCTURE each asserted, of
;;; one m, both (IS-MODULE m) -- which pins length(scal(m)) = 6 through MODULE's
;;; (substructure SCAL RING) -- and (IS-NORMED-FIELD (SCAL m)), which pins the
;;; same term to 7.  All three were EMPTY and their four supports vacuous.  The
;;; repair NAMES the field and pins the slot to its six-slot ring view; the
;;; derivation of falsity, before and after, is scratchpad/sn-falsity-probe.scm,
;;; and the standing refusal is test-suite-negative.scm section 2f.
;;;
;;; WHAT THE REPAIR COSTS, and it is what this leaf is about.  The field is
;;; EXISTENTIALLY bound inside the defining IFF:
;;;
;;;     FORSOME fld.  IS-NORMED-FIELD(fld)
;;;                   and scal(m) = normed-field-as-commutative-ring(fld)
;;;                   and forall lam, x. p(act(m)(lam,x)) = (fnrm(fld))(lam) * p(x)
;;;
;;; so every future consumer that used to read `(IS-NORMED-FIELD (SCAL m))'
;;; straight out of the unfolded hypothesis must now SKOLEMIZE.  No proof in the
;;; tree does that today -- nothing cites any of the four supports and nothing
;;; unfolds any of the three predicates, which is why the repair moved ZERO bills
;;; -- so this drive is where the cost is paid for the first time, in the
;;; smallest statement that has to pay it.
;;;
;;; THE STATEMENT (a projection, not new mathematics):
;;;
;;;     forall m, p.  IS-SEMINORM(m, p)
;;;                   =>  FORSOME fld. IS-NORMED-FIELD(fld)
;;;                                    and scal(m) = normed-field-as-commutative-ring(fld)
;;;
;;; i.e. "a seminorm's scalars are a normed field", which is the half of the
;;; conjunct a consumer wants without the homogeneity law riding along.  Proving
;;; it makes the read-off citable by name, so no later proof has to repeat the
;;; skolemization.
;;;
;;; Run:   ./prover -b -i prove-scripts/drives/seminorm-scalar-field-drive.scm
;;;
;;; WHAT THIS SCRIPT DOES, and where it stops.  It peels the two universals and
;;; the antecedent, unfolds IS-SEMINORM in the hypothesis, splits the resulting
;;; conjunction, and SKOLEMIZES the existential by hand.  `obtain' cannot do that
;;; last step -- it diffs the context around its own lane, so a FORSOME that was
;;; already in the context is invisible to it (CLAUDE.md, "obtain cannot
;;; skolemize an existential that is ALREADY in the context"), and it swallows
;;; the error besides.  `ai' on the FORSOME does it, and the eigenvariable is
;;; read off by free-variable set difference rather than guessed.
;;;
;;; WHAT IS LEFT: supply the eigenvariable as the goal's witness and close the
;;; two conjuncts, both of which are then literally in the context.
;;;
;;; WHAT THE COPILOT SAYS ABOUT THIS LEAF, measured 2026-08-24 -- two findings,
;;; neither of them this repair's doing:
;;;
;;;   * `what-now' DIES on it, and on any goal where a `def-functoid' macete is
;;;     a live rewrite candidate: the rewrite lane calls `lookup-theorem' on the
;;;     candidate's name, a functoid has a macete and no theorem, and
;;;     `lookup-theorem' ERRORS on a miss.  The panel stops at
;;;     "VNB error: lookup-theorem: unknown theorem normed-field-as-commutative-ring",
;;;     losing every lane after the rewrite lane -- including the existential
;;;     lane.  Reproduced independently on the bare goal
;;;     `(IS-INTEGRAL-DOMAIN (FIELD-AS-INTEGRAL-DOMAIN f))', so it is general and
;;;     pre-existing.
;;;   * with `lookup-theorem' softened so the panel completes, the existential
;;;     lane offers `(ew 'p)' -- the SEMINORM as the witness for a normed field.
;;;     It proposes typed context terms and does not reach for the eigenvariable
;;;     the skolemization just introduced, which is the one witness that works.
;;;
;;; So the lane fix this leaf asks for is: guard that `lookup-theorem' call, and
;;; have the existential lane offer a skolem eigenvariable whose typing conjunct
;;; matches a conjunct of the goal.

(sp (make-wff '(FORALL m (FORALL p (IMPLIES (IS-SEMINORM m p)
   (FORSOME fld (AND (IS-NORMED-FIELD fld)
                     (= (SCAL m) (NORMED-FIELD-AS-COMMUTATIVE-RING fld)))))))))

;; Two `di's, not one: an UNGUARDED universal peels the quantifier and lands
;; nothing, so the antecedent arrives on the second call (CLAUDE.md).
(di)
(di)

(mac-h 'IS-SEMINORM '(IS-SEMINORM m p))

;; ai every conjunction to exhaustion.  `dk-split!' would do this, but it starts
;; by ai-ing the formula handed to it, and what is in the context here is the
;; whole unfolded body rather than a formula this script constructed.
(define (ssf-split!)
  (let loop ((n 0))
    (let ((h (let scan ((l (dk-asms)))
               (cond ((null? l) #f)
                     ((and (pair? (car l)) (eq? (caar l) 'AND)) (car l))
                     (else (scan (cdr l)))))))
      (if (and h (< n 50)) (begin (ai h) (loop (+ n 1))) n))))
(ssf-split!)

;; The existential, found by SHAPE at the top level -- there is exactly one
;; FORSOME among the conjuncts of the unfolded body.
(define ssf-ex
  (let scan ((l (dk-asms)))
    (cond ((null? l) (error "seminorm-scalar-field-drive: no FORSOME in the context"))
          ((and (pair? (car l)) (eq? (caar l) 'FORSOME)) (car l))
          (else (scan (cdr l))))))

;; Skolemize, and read the eigenvariable off by free-variable set difference --
;; never off the eigenvariable counter, whose numbering is not stable.
(define ssf-fv-before
  (apply append (map (lambda (a) (free-vars a)) (dk-asms))))
(ai ssf-ex)
(ssf-split!)
(define ssf-eigen
  (let ((new (filter (lambda (v) (not (memq v ssf-fv-before)))
                     (apply append (map (lambda (a) (free-vars a)) (dk-asms))))))
    (if (null? new)
        (error "seminorm-scalar-field-drive: ai landed no eigenvariable")
        (car new))))

(newline)
(display "### the scalar field, skolemized out of IS-SEMINORM(m, p):\n")
(display "###   eigenvariable: ") (display ssf-eigen) (newline)
(display "### context now holds:\n")
(for-each (lambda (a)
            (display "###   ") (display (expression->string a)) (newline))
          (dk-asms))
(display "### goal: ") (display (expression->string (dk-goal))) (newline)
(newline)
(display "### WHAT IS LEFT -- two moves and a close:\n")
(display "###   (ew '") (display ssf-eigen)
(display ")       supply the eigenvariable as the witness\n")
(display "###   (di)                        splits the AND goal into two leaves\n")
(display "###                               -- `split' is not a tactic name; a `di'\n")
(display "###                               on an AND goal is what opens it\n")
(display "###   (ass) on each leaf          both conjuncts are in the context\n")
(display "### Verified closable 2026-08-24: those three moves close it, 0 leaves.\n")
(display "### Then (qed 'seminorm-scalars-normed-field), and add the file to\n")
(display "### load.scm -- a proof file load.scm does not name never runs.\n")
