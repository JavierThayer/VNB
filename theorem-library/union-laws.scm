;;; theorem-library/union-laws.scm -- union-empty-right and union-assoc, moved out of
;;; theorem-library/fin-subsets.scm on 2026-09-20 (batch 9-B, CARD := CARD-STAR).
;;;
;;;   union-empty-right   A u {} = A
;;;   union-assoc         (A u B) u C = A u (B u C)
;;;
;;; Two unguarded set identities, propositional after the membership unfolds; they
;;; mention no CARD.  They moved because theorem-library/rake-card-star-laws.scm cites
;;; both, and the CARD development now loads far above fin-subsets.scm, whose remaining
;;; theorems rest on card-union-nn (theorem-library/card-inequalities.scm) and so must stay
;;; below the CARD laws.  Their other citers (rake-finsum-union, rake-finsum-cm-union,
;;; fin-subset-monoid) all load below this file.
;;;
;;; USES bc* (class-extensionality): this file must NOT be compiled -- see CLAUDE.md,
;;; "COMPILE THE TREE FIRST".  The original is
;;; archive/2026-09-20-card-defined/fin-subsets-before-split.scm.
;;;
;;; The `fs-' helper block is copied verbatim from fin-subsets.scm; each theorem-library
;;; file gets its own environment, so the two copies do not meet.

;;; --- file-local helpers (fs- prefix) ------------------------------------

;; Peel the leading FORALL/IMPLIES prefix and stop at the first other head.
;; The statements below quantify UNGUARDED and then imply, which one `di' does
;; NOT take whole (CLAUDE.md); loop on the head rather than counting calls.
(define (fs-peel!)
  (let loop ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(forall implies)))
          (begin (di) (loop))))))

;; Drop every assumption but the ones named -- `prop' has a 12-atom cap and
;; `fact' lands its whole instantiation chain.
(define (fs-only! . keepers)
  (for-each (lambda (f) (if (not (member f keepers)) (wk f))) (dk-asms)))

;; The unfolded body of FIN-SUBSETS(A), as the SEP the functoid rewrites to.
;; Written once because three drivers below name it to `sep-me'.
(define (fs-sep a) (list 'SEP 't_ (list 'POWER a) '(IN (CARD t_) NN)))

;; Split a conjunctive goal to leaves and close each from the context.
(define (fs-conj-close!)
  (if (and (pair? (dk-goal)) (eq? (car (dk-goal)) 'and))
      (for-each (lambda (lf) (dk-focus! lf) (fs-conj-close!))
                (dk-opened (lambda () (di))))
      (ass)))

;;; -----------------------------------------------------------------------
;;; (3) union-empty-right:  A u {} = A.
;;;
;;; Unguarded -- UNION and class-extensionality are total over classes, and
;;; nothing is in EMPTY-SET.
;;;
;;; The `declare-named-only!' must PRECEDE the proof: `install-theorem!'
;;; (macetes.scm) consults *named-only-macetes* while it builds the rewrite, so
;;; a declaration written after the `qed' is a silent no-op.  Both declarations
;;; in this file stood after their qed until 2026-09-20.

(declare-named-only! 'union-empty-right
  "Its RIGHT side is a bare variable, so the `-rev' companion would match every
   term in every goal and rewrite it into a union.  Cite it by name.")

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (= (UNION a_ EMPTY-SET) a_))))
  (fs-peel!)
  (bc* 'class-extensionality)
  (fs-peel!)
  (fact 'union-membership 'a_ 'EMPTY-SET 'x)
  (fact 'empty-set-has-no-members 'x)
  (fs-only! '(iff (in x (union a_ empty-set)) (or (in x a_) (in x empty-set)))
            '(not (in x empty-set)))
  (prop)))
(qed 'union-empty-right)
(topic! 'union-empty-right 'plumbing)

;;; -----------------------------------------------------------------------
;;; (4) union-assoc:  (A u B) u C = A u (B u C).
;;;
;;; Unguarded, and purely propositional after four membership unfolds.
;;;
;;; Declared BEFORE the proof -- see union-empty-right above.

(declare-named-only! 'union-assoc
  "An unconditional equation whose left side matches every nested binary union
   in the library.  Cite it by name.")

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (FORALL b_ (FORALL c_
        (= (UNION (UNION a_ b_) c_) (UNION a_ (UNION b_ c_))))))))
  (fs-peel!)
  (bc* 'class-extensionality)
  (fs-peel!)
  (fact 'union-membership '(UNION a_ b_) 'c_ 'x)
  (fact 'union-membership 'a_ 'b_ 'x)
  (fact 'union-membership 'a_ '(UNION b_ c_) 'x)
  (fact 'union-membership 'b_ 'c_ 'x)
  (fs-only! '(iff (in x (union (union a_ b_) c_)) (or (in x (union a_ b_)) (in x c_)))
            '(iff (in x (union a_ b_)) (or (in x a_) (in x b_)))
            '(iff (in x (union a_ (union b_ c_))) (or (in x a_) (in x (union b_ c_))))
            '(iff (in x (union b_ c_)) (or (in x b_) (in x c_))))
  (prop)))
(qed 'union-assoc)
(topic! 'union-assoc 'plumbing)
