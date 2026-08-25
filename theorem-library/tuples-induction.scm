;;; tuples-induction.scm -- list induction, DERIVED.
;;;
;;; theory.scm:637 recorded two things as pending: a CONS constructor, and "a
;;; TUPLES induction principle".  structure-library/list-recursion.scm supplies
;;; the first, and instead of the second it states GENERATION -- that a tuple of
;;; length 0 is [], and that a tuple of length succ n is a CONS.  This file
;;; turns generation into the induction principle, so the tree gains list
;;; induction without gaining an induction axiom.
;;;
;;;   forall A, C.  [] in C
;;;                 and (forall x, M. x in A and M in TUPLES(A) and M in C
;;;                                   => CONS(x,M) in C)
;;;                 => forall L in TUPLES(A). L in C
;;;
;;; CLASS FORM, not a schema: `C' is a class variable and the conclusion is
;;; membership in it, exactly as `nn-induction' (number-systems.scm:167) and
;;; `finite-set-induction' (cardinality.scm) are stated.  VNB quantifies over
;;; classes, so the principle is a single theorem rather than one instance per
;;; property.
;;;
;;; THE PROOF is induction on the LENGTH, which is what makes generation enough:
;;; the helper
;;;
;;;   forall n in NN. forall L. L in TUPLES(A) and LENGTH(L) = n => L in C
;;;
;;; is proved by `ni' -- the nn-induction rule -- and the theorem follows by
;;; instantiating it at n := LENGTH(L), which `length-in-nn' puts in NN.  In the
;;; base, `tuple-length-zero' rewrites L to []; in the step,
;;; `tuple-cons-decompose' produces the head and the tail, the induction
;;; hypothesis applies to the tail (its length is n), and the step hypothesis
;;; puts the CONS back.  Nothing else is used.
;;;
;;; TWO DRIVER NOTES, both of which cost a run.
;;;
;;; `fact' takes a theorem NAME.  For a universal that is IN CONTEXT -- the
;;; induction hypothesis, the step hypothesis -- the move is `inst*!'
;;; (driver-kit.scm) followed by `detach!'; `fact' on a formula warns "unknown
;;; theorem: (not a symbol)" and continues, which is a silent no-op three lines
;;; before the failure it causes.  `ti-apply!' below packages the pair.
;;;
;;; The two universals are selected by their CONCLUSION, never by binder name or
;;; by shape.  `dk-fact!' leaves the whole tuple-cons-decompose instantiation
;;; chain in the context, and two of its links are also FORALL-over-FORALL, so
;;; "the assumption whose body is a FORALL" picks the axiom rather than the step
;;; hypothesis and the driver then detaches the wrong implication.  This is the
;;; brief's rule -- never name an assumption by shape -- in its exact form.

;;; --- file-local helpers (ti- prefix) ------------------------------------

(define (ti-peel!)
  (let loop ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(forall implies))) (begin (di) (loop))))))

(define (ti-head? h) (lambda (f) (and (pair? f) (eq? (car f) h))))

(define (ti-pick pred what)
  (let ((fs (filter pred (dk-asms))))
    (if (null? fs) (error "ti-pick: nothing matching" what) (car fs))))

;; The conclusion under all leading FORALL/IMPLIES -- the handle used to tell
;; the induction hypothesis and the step hypothesis apart.
(define (ti-final f)
  (if (and (pair? f) (memq (car f) '(forall implies))) (ti-final (caddr f)) f))

;; Instantiate an IN-CONTEXT universal at TERMS and detach its guard.
(define (ti-apply! f . terms)
  (let ((r (apply inst*! f terms)))
    (if (and (pair? r) (eq? (car r) 'implies))
        (dk-landed-1 (lambda () (detach! r)))
        r)))

;; Split every conjunction in the context, to exhaustion.
(define (ti-split-all!)
  (let loop ()
    (let ((ands (filter (ti-head? 'and) (dk-asms))))
      (if (pair? ands) (begin (ai (car ands)) (loop))))))

;;; --------------------------------------------------------------------

(sp (make-wff '(FORALL A (FORALL C
  (IMPLIES (AND (IN (LIST) C)
                (FORALL x (FORALL M
                  (IMPLIES (AND (IN x A) (AND (IN M (TUPLES A)) (IN M C)))
                           (IN (CONS x M) C)))))
           (FORALL L (IMPLIES (IN L (TUPLES A)) (IN L C))))))))
(ti-peel!)
(ti-split-all!)

;; The length-indexed form, by induction on the length.
(have! '(FORALL n_ (IMPLIES (IN n_ NN)
          (FORALL l_ (IMPLIES (AND (IN l_ (TUPLES a)) (= (LENGTH l_) n_)) (IN l_ c)))))
  (lambda ()
    (for-each
     (lambda (lf)
       (dk-focus! lf)
       (cond
         ;; BASE.  Length 0, so the tuple IS [].
         ((equal? (dk-goal)
                  '(forall l_ (implies (and (in l_ (tuples a)) (= (length l_) 0)) (in l_ c))))
          (ti-peel!)
          (fact 'tuple-length-zero 'a 'l_)
          (subst '(= l_ (LIST)))
          (ass))
         ;; STEP.  Length succ n_: decompose into head and tail, apply the
         ;; induction hypothesis to the tail, put the head back with the step.
         (else
          (ti-peel!)
          (ti-split-all!)
          (have! '(AND (IN n_ NN) (AND (IN l_ (TUPLES a)) (= (LENGTH l_) (succ n_)))))
          (ai (dk-fact! 'tuple-cons-decompose 'a 'n_ 'l_))          ; the head
          (ti-split-all!)
          (ai (ti-pick (ti-head? 'forsome) "the tail existential"))  ; the tail
          (ti-split-all!)
          (let* ((leq (ti-pick (lambda (f) (and (eq? (car f) '=) (symbol? (cadr f))
                                                (pair? (caddr f))
                                                (eq? (car (caddr f)) 'cons)))
                               "l_ = cons(x0, m0)"))
                 (x0  (cadr (caddr leq)))
                 (m0  (caddr (caddr leq)))
                 (ih  (ti-pick (lambda (f) (equal? (ti-final f) (list 'in (cadr f) 'c)))
                               "the induction hypothesis"))
                 (stp (ti-pick (lambda (f)
                                 (let ((cc (ti-final f)))
                                   (and (eq? (car cc) 'in) (pair? (cadr cc))
                                        (eq? (car (cadr cc)) 'cons))))
                               "the step hypothesis")))
            (have! (list 'AND (list 'IN m0 '(TUPLES a)) (list '= (list 'LENGTH m0) 'n_)))
            (ti-apply! ih m0)                                       ; tail in C
            (have! (list 'AND (list 'IN x0 'a)
                         (list 'AND (list 'IN m0 '(TUPLES a)) (list 'IN m0 'c))))
            (ti-apply! stp x0 m0)                                   ; cons(x0,m0) in C
            (subst leq)
            (ass)))))
     (dk-opened (lambda () (ni))))))

;; From the length-indexed form to the statement, at n := LENGTH(L).
(fact 'length-in-nn 'a 'l)
(let* ((h  (ti-pick (lambda (f) (and (eq? (car f) 'forall) (eq? (cadr f) 'n_)))
                    "the length-indexed helper"))
       (h1 (dk-deepest (lambda () (inst+ h '(LENGTH l)))))
       (h2 (dk-deepest (lambda () (inst+ h1 'l)))))
  ;; (= (LENGTH l) (LENGTH l)) is not vacuous under PARTIAL equality: it asserts
  ;; that LENGTH(l) is defined, which `rfl' reads off (IN (LENGTH l) NN) above.
  (have! '(= (LENGTH l) (LENGTH l)) (lambda () (rfl)))
  (have! '(AND (IN l (TUPLES a)) (= (LENGTH l) (LENGTH l))))
  (detach! h2)
  (ass))

(qed 'tuples-induction)
(topic! 'tuples-induction 'combinatorial)
