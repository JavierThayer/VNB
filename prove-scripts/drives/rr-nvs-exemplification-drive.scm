;;; rr-nvs-exemplification-drive.scm -- THE LEAF LEFT FOR THE USER (2026-08-23).
;;;
;;; The five vacuous results are repaired: `IS-FINITE-DIMENSIONAL' is now said
;;; of NORMED-VECTOR-SPACE-AS-MODULE(m), so the hypothesis of hahn-banach,
;;; norm-as-sup, norm-attained-by-functional, vector-taylor-remainder-bound and
;;; nvs-taylor-remainder-bound no longer pins length(m) to 7 and to 6 at once.
;;;
;;; A REPAIRED PREDICATE IS STILL AN EMPTY PREDICATE UNTIL SOMETHING SATISFIES
;;; IT, and these two are distinct claims:
;;;
;;;   SATISFIABLE   -- nothing in the statement contradicts itself.  Decided,
;;;                    for this class of defect, by statement-satisfiability-
;;;                    audit (audit.scm) and measured by
;;;                    scratchpad/nvs-findim-falsity-probe.scm, which now
;;;                    reports NO SHARED TERM WITH TWO LENGTHS.
;;;   EXEMPLIFIED   -- something in the tree exhibits one.  NOTHING DOES.
;;;                    `structure-exemplification-audit' puts NORMED-VECTOR-SPACE
;;;                    in its UNWITNESSED list: there is no declare-instance! of
;;;                    the shape and no witness theorem.  R^n is the missing
;;;                    construction.
;;;
;;; Unexemplified is not vacuous -- it is an ordinary missing construction --
;;; but it is why no proof in the library has ever had to MEET this hypothesis,
;;; and it is the reason the defect could sit for months.
;;;
;;; THIS DRIVE BUILDS THE FIRST WITNESS: the reals as a one-dimensional real
;;; normed vector space.  n = 1 is the whole point -- it needs no finite
;;; products, no bases and no linear algebra, and every obligation it raises is
;;; an ordinary fact about RR and abs.
;;;
;;;     RR-NVS = [ normed-field-as-commutative-ring(rr-normed-field),   SCAL
;;;                RR, binplus, 0, binneg, bintimes,                    VEC..ACT
;;;                abs ]                                                VNRM
;;;
;;; SCAL is the six-slot RING VIEW of the normed field, never the raw 7-tuple:
;;; the declaration's own law says so, and pinning the raw instance is the
;;; defect normed-vector-space.scm carried until 2026-08-23.
;;;
;;; Run:   ./prover -b -i prove-scripts/drives/rr-nvs-exemplification-drive.scm
;;;
;;; WHAT IT COSTS, measured: `declare-instance!' accepts the 7-tuple (it checks
;;; the length against the shape -- that check is what caught the original
;;; RR-NORMED-FIELD/IS-RING inconsistency in May 2026), the defining IFF unfolds
;;; into TWENTY-ONE conjuncts, and `surface-goal!' takes every one of them down
;;; to the surface language.  The list this script prints is the whole of the
;;; work.  One closes on the spot (`0 in rr', by arith); the rest are:
;;;
;;;   1  length(rr-nvs) = 7            -- (mac 'rr-nvs-def) then (len-r) (arith)
;;;   2  is-ring(normed-field-as-commutative-ring(rr-normed-field))
;;;                                    -- the view's typing axiom composed with
;;;                                       commutative-ring-is-ring; note the
;;;                                       companion IS-FIELD-RING of the same
;;;                                       term is the leaf of
;;;                                       rr-scalars-field-ring-drive.scm
;;;   3  rr in set                     -- rr-is-set
;;;   4,6,7,8  the operation typings -- binplus-in-fun-rr, binneg-in-fun-rr,
;;;            bintimes-in-fun-rr, and abs into RR.  Note 7 arrives already
;;;            reading fun(cartesian(rr, rr), rr): the scalar carrier came out
;;;            as RR through the rr-scalar-ring-carr read-off, so the action's
;;;            domain is the ordinary real product and nothing about the ring
;;;            view is left in the goal.
;;;   9-12  the additive abelian group of RR -- is-associative / is-commutative /
;;;         is-identity / has-inverses, i.e. rr-add-assoc, rr-add-comm,
;;;         rr-add-zero, rr-neg-inverse, after unfolding each property predicate
;;;   13 the scalar law -- `rfl' (both sides are the same closed term), modulo
;;;      the definedness that `=' being partial asks for
;;;   14-17  the four action laws -- distributivity twice, associativity of the
;;;          action, and 1.x = x: `crs' after bintimes-apply / binplus-apply
;;;   18-21  the four norm laws -- abs-nonneg, abs-zero-iff, abs-mul,
;;;          triangle-inequality: all four are already in the tree
;;;
;;; So the witness is a citation exercise, not a construction: no new
;;; mathematics, and the payoff is that NORMED-VECTOR-SPACE leaves the
;;; unwitnessed list and the whole finite-dimensional Hahn-Banach arc acquires
;;; a model.  The next rung after it -- RR^n, with FINSUM for the sum norm --
;;; is where the real work starts.

(declare-instance! 'RR-NVS 'NORMED-VECTOR-SPACE 'rr-nvs-def
  '((NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) RR binplus 0 binneg bintimes abs))

(sp (make-wff '(IS-NORMED-VECTOR-SPACE RR-NVS)))
(mac 'IS-NORMED-VECTOR-SPACE)

;;; the defining IFF is a right-nested AND; `di' splits one conjunct per call,
;;; so loop on whether an AND leaf is still there rather than counting.
(let loop ((n 0))
  (let ((any #f))
    (for-each (lambda (l)
                (dk-focus! l)
                (if (and (pair? (dk-goal)) (eq? (car (dk-goal)) 'AND))
                    (begin (set! any #t) (vnb-guard (lambda () (di))))))
              (proof-leaves))
    (if (and any (< n 40)) (loop (+ n 1)))))

;;; push every accessor of the instance down to its slot value, then the scalar
;;; slot's own accessors through the ring view to RR / binplus / bintimes / 1.
(for-each (lambda (l)
            (dk-focus! l)
            (vnb-guard (lambda () (surface-goal! 'RR-NVS)))
            (for-each (lambda (m) (vnb-guard (lambda () (mac m))))
                      '(rr-scalar-ring-carr rr-scalar-ring-add
                        rr-scalar-ring-mul  rr-scalar-ring-one
                        rr-scalar-ring-zero rr-scalar-ring-neg)))
          (proof-leaves))

(newline)
(display "### RR-NVS: ") (display (length (proof-leaves)))
(display " obligations, in the surface language:") (newline)
(let ((i 0))
  (for-each (lambda (l)
              (dk-focus! l) (set! i (+ i 1))
              (display "###  ") (display i) (display ". ")
              (display (expression->string (dk-goal))) (newline))
            (proof-leaves)))
(newline)
(display "### Drive them from the numbered notes in this file's header.\n")
(display "### `0 in rr' falls to (arith) on the spot; the rest are citations.\n")
