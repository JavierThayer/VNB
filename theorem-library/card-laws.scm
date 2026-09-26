;;; theorem-library/card-laws.scm -- the former CARD axioms whose counterpart has a
;;; different SHAPE, restated character for character as the axioms stood and proven
;;; (2026-09-20, batch 9-B: CARD := CARD-STAR, the user's decision).
;;;
;;; CARD is DEFINED in structure-library/cardinality.scm.  Eight facts about it used to
;;; sit on the `primitive' shelf.  Three of them are alpha-equivalent to a theorem the
;;; CARD development already proves, and those simply took the axiom's name:
;;;
;;;   card-segment           theorem-library/card-defined.scm       (was card-star-segment)
;;;   card-empty             theorem-library/card-finite.scm        (was card-star-empty)
;;;   finite-set-induction   theorem-library/rake-card-star-laws.scm
;;;
;;; The other five are proven HERE, because the CARD-STAR development stated them with
;;; CURRIED antecedents (which `fact' can detach) while the axioms CONJOINED them, and a
;;; citer that does `(fact 'card-insert A x)' must keep working unchanged.  Each proof is
;;; the same three moves: peel the axiom's shape, split the conjoined antecedents, cite the
;;; curried theorem, `ass'.
;;;
;;;   card-in-ord           from card-zermelo          (the first conjunct)
;;;   card-insert           from card-insert-curried
;;;   card-finite-bij       from well-ordering-principle  (which is STRONGER: it has no
;;;                                                        finiteness guard)
;;;   card-union-disjoint   from card-union-disjoint-curried
;;;   card-image-injection  from card-image-injection-curried
;;;
;;; The eight statements below are copied VERBATIM from the axioms as they were installed
;;; (structure-library/cardinality.scm and structure-library/injection.scm in
;;; archive/2026-09-20-card-defined/), not from their printed readings.
;;;
;;; AFTER THIS FILE NOTHING ABOUT CARD IS ASSERTED.  The analysis, the citation cone and
;;; the load-order surgery are docs/card-defined-2026-09-20.md.
;;;
;;; Helper prefix: cdl-.

;;; ---- driver helpers ---------------------------------------------------

;; Peel the whole FORALL/IMPLIES prefix, then split every conjunction the peel
;; landed.  The axioms conjoin their antecedents, so the split is what lets
;; `fact' detach the curried theorem's guards from the context.
(define (cdl-open!)
  (dk-peel!)
  (dk-split-all!))

(define (cdl-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; cdl: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "card-laws: proof not complete" name))))

;;; ---- 1.  card-in-ord --------------------------------------------------
;;; card-zermelo (rake-ord-pigeonhole.scm) gives, for S in SET, the conjunction
;;; "CARD(S) in ORD and S bijects with ORD-SEGMENT(CARD S)".  The first conjunct
;;; IS this axiom.

(sp (make-wff
     '(FORALL A
        (IMPLIES (IN A SET)
                 (IN (CARD A) ORD)))))
(cdl-open!)
(let ((av (cadr (cadr (dk-goal)))))              ; goal is (IN (CARD A) ORD)
  (dk-fact! 'card-zermelo av)
  (dk-split-all!)
  (ass))
(cdl-check! 'card-in-ord)
(qed 'card-in-ord)

;;; ---- 2.  card-insert --------------------------------------------------
;;; The guard (IN (CARD A) NN) is CURRIED in the axiom, and was so before this
;;; change (2026-09-18) so that `(fact 'card-insert A x)' keeps both arguments;
;;; what is CONJOINED is x's pair of guards.

(sp (make-wff
     '(FORALL A
        (IMPLIES (IN A SET)
          (IMPLIES (IN (CARD A) NN)
            (FORALL x
              (IMPLIES (AND (IN x SET) (NOT (IN x A)))
                       (= (CARD (UNION A (PAIR x x)))
                          (succ_ORD (CARD A))))))))))
(cdl-open!)
(let* ((un (cadr (cadr (dk-goal))))              ; (UNION A (PAIR x x))
       (av (cadr un))
       (xv (cadr (caddr un))))
  (dk-fact! 'card-insert-curried av xv)
  (ass))
(cdl-check! 'card-insert)
(qed 'card-insert)

;;; ---- 3.  card-finite-bij ----------------------------------------------
;;; well-ordering-principle (rake-ord-pigeonhole.scm) says every SET bijects with
;;; the segment of its cardinal, with no finiteness guard.  This axiom is that
;;; statement weakened by the guard, so the proof is one citation.

(sp (make-wff
     '(FORALL A
        (IMPLIES (AND (IN A SET) (IN (CARD A) NN))
                 (FORSOME phi
                   (IN phi (BIJECTION (ORD-SEGMENT (CARD A)) A)))))))
(cdl-open!)
(let ((av (caddr (caddr (caddr (dk-goal))))))    ; (FORSOME phi (IN phi (BIJECTION _ A)))
  (dk-fact! 'well-ordering-principle av)
  (ass))
(cdl-check! 'card-finite-bij)
(qed 'card-finite-bij)

;;; ---- 4.  card-union-disjoint ------------------------------------------

(sp (make-wff
     '(FORALL A
        (IMPLIES (AND (IN A SET) (IN (CARD A) NN))
          (FORALL B
            (IMPLIES (AND (IN B SET) (AND (IN (CARD B) NN) (= (INTERSECTION A B) EMPTY-SET)))
                     (= (CARD (UNION A B))
                        (+ (CARD A) (CARD B)))))))))
(cdl-open!)
(let* ((un (cadr (cadr (dk-goal))))              ; (UNION A B)
       (av (cadr un))
       (bv (caddr un)))
  (dk-fact! 'card-union-disjoint-curried av bv)
  (ass))
(cdl-check! 'card-union-disjoint)
(qed 'card-union-disjoint)

;;; ---- 5.  card-image-injection -----------------------------------------
;;; Was the eighth axiom, in structure-library/injection.scm:161.  The curried
;;; form quantifies dm first and cod/phi after the finiteness guard; the axiom
;;; quantifies all three up front.

(sp (make-wff
     '(FORALL dm
        (FORALL cod
          (FORALL phi
            (IMPLIES (AND (IN phi (INJECTION dm cod)) (AND (IN dm SET) (IN (CARD dm) NN)))
                     (= (CARD (IMAGE phi dm)) (CARD dm))))))))
(cdl-open!)
(let* ((im  (cadr (cadr (dk-goal))))             ; (IMAGE phi dm)
       (pv  (cadr im))
       (dv  (caddr im))
       (inj (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'INJECTION)))
                     "phi in INJECTION(dm, cod)"))
       (cv  (caddr (caddr inj))))
  (dk-fact! 'card-image-injection-curried dv cv pv)
  (ass))
(cdl-check! 'card-image-injection)
(qed 'card-image-injection)
