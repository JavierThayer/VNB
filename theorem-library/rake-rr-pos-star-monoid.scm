;;; theorem-library/rake-rr-pos-star-monoid.scm -- IS-COMM-MONOID(RR-POS-STAR-ADD-MONOID),
;;; PROVEN.  Rake batch 6-C.  Helper prefix `rpm-'.
;;;
;;; The statement is the one asserted at structure-library/extended-reals-pos.scm:167
;;; (warrant `well-known'), character for character:
;;;
;;;     (IS-COMM-MONOID RR-POS-STAR-ADD-MONOID)
;;;
;;; THE ROUTE is nn-add-monoid.scm's, and shorter, because the OPR slot of
;;; RR-POS-STAR-ADD-MONOID = [RR-POS-STAR, eplus, 0] holds the CONSTANT `eplus',
;;; not a tupled VNB-LAMBDA.  Unfold IS-COMM-MONOID, push the accessors to the
;;; surface (`surface-goal!', which is the ONE door -- no accessor macete is
;;; fired by name), and every conjunct is a theorem already on the shelf:
;;;
;;;   (= (LENGTH RR-POS-STAR-ADD-MONOID) 3)          the instance equation + len-r
;;;   (IN RR-POS-STAR SET)                           rr-pos-star-is-set
;;;   (IN eplus (FUN (CARTESIAN RR-POS-STAR RR-POS-STAR) RR-POS-STAR))   eplus-in-fun
;;;   (IN 0 RR-POS-STAR)                             zero-in-rr-pos-star
;;;   (is-associative eplus RR-POS-STAR)             eplus-assoc
;;;   (is-identity eplus 0 RR-POS-STAR)              eplus-zero-left / -right
;;;   (is-commutative eplus RR-POS-STAR)             eplus-comm
;;;
;;; NOT `crs', and not a read-off of anything: the five eplus laws were proved
;;; case by case from the definition of eplus in rake-extended-order.scm
;;; precisely so that this assertion would not have to be believed.  This file
;;; only assembles them.  rake-extended-order.scm:509 says the two laws it
;;; proves are "two of the three laws packed inside the asserted
;;; rr-pos-star-is-comm-monoid" -- they are now the whole of it.
;;;
;;; CITATIONS, by the FILE that installs them (load.scm is being edited today,
;;; so no indices):
;;;   structures.scm / declare-instance!  rr-pos-star-add-monoid-def
;;;                                       (structure-library/extended-reals-pos.scm)
;;;   theorem-library/rake-rr-pos-star    zero-in-rr-pos-star
;;;   theorem-library/rake-eplus-defined  rr-pos-star-is-set, eplus-in-fun
;;;   theorem-library/rake-extended-order eplus-assoc, eplus-comm,
;;;                                       eplus-zero-left, eplus-zero-right
;;; Tactics: interactive, driver-kit, transport (surface-goal!) -- all early.
;;; Nothing here uses `contra', `prep' or `ineq-supply'.
;;;
;;; LOAD WINDOW [rake-extended-order, end).  lo is forced by eplus-assoc /
;;; eplus-comm / eplus-zero-left / eplus-zero-right, all in
;;; theorem-library/rake-extended-order.  NO PROVEN FILE cites
;;; rr-pos-star-is-comm-monoid by name (grep over structure-library/,
;;; theorem-library/, calculus/: comments only), so no citer forces hi.  The
;;; natural slot is immediately after theorem-library/rake-esup-defined, where
;;; the ESUM work begins.

;;; (section (0), the probe-only installation of the definition, was deleted on integration, 2026-09-19)

;;; =====================================================================
;;; (1)  FILE-LOCAL DRIVER HELPERS
;;; =====================================================================

;;; The eigenvariables of a law goal are read off the GOAL, never off the
;;; context order: `dk-asms' is not in peel order, and `di' renames when a name
;;; is taken (the lesson nn-add-monoid.scm:42 records).
(define (rpm-assoc-vars g)         ; (= (eplus (eplus u v) w) (eplus u (eplus v w)))
  (let ((lhs (cadr g)))
    (list (cadr (cadr lhs)) (caddr (cadr lhs)) (caddr lhs))))

(define (rpm-comm-vars g)          ; (= (eplus u v) (eplus v u))
  (let ((lhs (cadr g))) (list (cadr lhs) (caddr lhs))))

(define (rpm-ident-var g)          ; (AND (= (eplus 0 u) u) (= (eplus u 0) u))
  (caddr (cadr g)))

(define (rpm-typed v) (list 'IN v 'RR-POS-STAR))

;;; `fact' will NOT split a CONJUNCTIVE antecedent (CLAUDE.md): eplus-assoc's
;;; guard is (AND (IN x _) (AND (IN y _) (IN z _))) and eplus-comm's is a pair,
;;; so the whole conjunction is `have!'d first -- otherwise the citation lands
;;; the implication silently and the `ass' misses.
(define (rpm-and* xs)
  (fold-right (lambda (x acc) (if acc (list 'AND x acc) x)) #f xs))

;;; =====================================================================
;;; (2)  THE CONJUNCT CLOSERS
;;; =====================================================================

(define (rpm-close-law!)
  (let ((law (car (dk-goal))))
    (mac law)
    (dk-peel!)
    (let ((g (dk-goal)))
      (cond
        ((eq? law 'is-associative)
         (let ((vs (rpm-assoc-vars g)))
           (have! (rpm-and* (map rpm-typed vs)))
           (apply fact 'eplus-assoc vs)
           (ass)))
        ((eq? law 'is-commutative)
         (let ((vs (rpm-comm-vars g)))
           (have! (rpm-and* (map rpm-typed vs)))
           (apply fact 'eplus-comm vs)
           (ass)))
        ((eq? law 'is-identity)
         ;; Both halves are theorems -- eplus is commutative, but the two
         ;; one-sided laws were proved separately in rake-extended-order, so
         ;; neither conjunct costs a commutativity step.  The guard (IN u
         ;; RR-POS-STAR) is a single atom and sits in context, so `fact'
         ;; detaches it by itself.
         (let ((u (rpm-ident-var g)))
           (fact 'eplus-zero-left u)
           (fact 'eplus-zero-right u)
           (dk-conj-close! (lambda () (ass)))))
        (#t (error "rpm-close-law!: unexpected law" (symbol->string law)))))))

(define (rpm-close-conjunct!)
  (let ((g (dk-goal)))
    (cond
      ;; LENGTH([RR-POS-STAR, eplus, 0]) = 3.  `rr-pos-star-add-monoid-def' is
      ;; the INSTANCE EQUATION, not an accessor or an instance-VALUE macete, so
      ;; firing it by name is not a reach past `slot' (accessor-callsite-audit
      ;; tests constant-head? / instance-value-macete-name?; nn-add-monoid.scm
      ;; fires nn-add-monoid-def the same way).
      ((and (eq? (car g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
       (mac 'rr-pos-star-add-monoid-def) (len-r) (arith))
      ((equal? g '(IN RR-POS-STAR SET))  (fact 'rr-pos-star-is-set)   (ass))
      ((equal? g '(IN 0 RR-POS-STAR))    (fact 'zero-in-rr-pos-star)  (ass))
      ((and (eq? (car g) 'IN) (eq? (cadr g) 'eplus))
       (fact 'eplus-in-fun) (ass))
      ((memq (car g) '(is-associative is-commutative is-identity))
       (rpm-close-law!))
      (#t (error "rpm-close-conjunct!: unexpected conjunct" (expression->string g))))))

;;; =====================================================================
;;; (3)  THE PROOF
;;; =====================================================================

(sp (make-wff '(IS-COMM-MONOID RR-POS-STAR-ADD-MONOID)))
(mac 'IS-COMM-MONOID)
;;; `quietly' silences the STATE DUMP only -- surface-goal! prints one line per
;;; rewrite and the log drowns in it.  It does not rely on a guard (the same
;;; note zz-ring-is-ring.scm:136 carries).
(quietly (lambda () (surface-goal! 'RR-POS-STAR-ADD-MONOID)))
;;; The surfaced goal, verbatim from the first probe -- every accessor is gone
;;; and nothing is left that is not a theorem:
;;;   length(rr-pos-star-add-monoid) = 3 and rr-pos-star in set
;;;   and eplus in fun(cartesian(rr-pos-star, rr-pos-star), rr-pos-star)
;;;   and 0 in rr-pos-star and is-associative(eplus, rr-pos-star)
;;;   and is-identity(eplus, 0, rr-pos-star) and is-commutative(eplus, rr-pos-star)
(dk-conj-close! rpm-close-conjunct!)
(qed 'rr-pos-star-is-comm-monoid)
(topic! 'rr-pos-star-is-comm-monoid 'analysis)
(alias! 'rr-pos-star-is-comm-monoid
        "[0,+inf] under extended addition is a commutative monoid")
