;;; card-image-finite.scm -- the image of a finite set is finite.
;;;
;;;     card-image-finite:
;;;       forall phi, X.  X in SET  =>  CARD(X) in NN  =>  CARD(IMAGE(phi, X)) in NN
;;;
;;; phi is an arbitrary CLASS function (any term; nothing is assumed about it,
;;; not even that phi(x) is defined at every x in X).  This is the general
;;; "finite image" brick the metric-normed triage found missing
;;; (scratchpad/triage/metric-normed.md): `card-image-injection' is for
;;; injections only, `card-subset-mono' bounds subsets, and nothing said the
;;; image of a finite set under an arbitrary map is finite.  It blocks
;;; `centre-set-finite' (structure-library/compactness.scm:177) and
;;; `tb-rad-ball-cover' (theorem-library/cauchy-subsequence.scm:261).
;;;
;;; THE PROOF is `finite-set-induction' (structure-library/cardinality.scm,
;;; primitive) on X, with the class instantiated to the COMP
;;;
;;;     C = { x_ | CARD(IMAGE(phi, x_)) in NN }
;;;
;;; with phi FIXED as an eigenvariable first, a parameter of the class (NBG
;;; comprehension, 2026-10-15: until then the map was quantified INSIDE the
;;; class property, which is Morse-Kelley).  Third firing of
;;; finite-set-induction in the tree.
;;;
;;; NO SET EXTENSIONALITY IS NEEDED.  The naive plan -- IMAGE(p, S u {x}) =
;;; IMAGE(p, S) u {p(x)}, an iff over an existential on each side -- is twice
;;; the work and is not even true when p(x) is undefined (`=' is partial, so an
;;; x at which p is undefined contributes nothing to the image).  Every case is
;;; instead an INCLUSION into a set already known finite, closed by
;;; `card-subset-nn' (proven 2026-09-14): an inclusion is the forward direction
;;; only, and it is the same three moves each time -- read the preimage y of a
;;; member z off image-membership-iff, split y's membership in the union, and
;;; put z back where it belongs.
;;;
;;;   BASE  IMAGE(p, {}) subset {}:  the preimage y is in {}, absurd.
;;;   STEP  S in SET, CARD S in NN, S in C, x in SET  =>  S u {x} in C.
;;;         With p the fixed map, `use-em' on  p(x) in SET:
;;;           defined:    IMAGE(p, S u {x}) subset {p(x)} u IMAGE(p, S), which is
;;;                       finite by the hypothesis at p and
;;;                       card-union-singleton-bound (makeset-card-bound.scm).
;;;                       A member z with preimage y: y in S puts z in IMAGE(p,S);
;;;                       y = x puts z = p(x) in the singleton.
;;;           undefined:  IMAGE(p, S u {x}) subset IMAGE(p, S).  A preimage y = x
;;;                       would make p(x) = z with z a set (membership-implies-
;;;                       sethood), i.e. p(x) in SET -- the case hypothesis
;;;                       refutes it.
;;;         Freshness of x (the `not (x in S)' premise) is never used.
;;;
;;; CITATIONS and where they load: finite-set-induction, card-empty, image-set,
;;; membership-implies-sethood, empty-set-is-set, empty-set-has-no-members,
;;; pairing, pairing-membership, union-membership, union-set-closure, nn-zero-in
;;; (all primitive: library.scm base, cardinality.scm, injection.scm,
;;; number-systems.scm); image-membership-iff (injection.scm, definitional);
;;; card-union-singleton-bound (theorem-library/makeset-card-bound);
;;; card-subset-nn (theorem-library/card-subset-nn, the slot right after it).
;;;
;;; LOAD WINDOW [card-subset-nn, <first citer of centre-set-finite>).  lo is
;;; forced by card-subset-nn, the latest citation; hi by whichever file first
;;; cites centre-set-finite once that support is retired -- today
;;; calculus/finite-ball-subcover-proof (loaded far below), and compact-tb-proof
;;; (four slots after card-inequalities) if the triage's plan to move the
;;; subcover proof before it is carried out.  The slot immediately after
;;; card-subset-nn satisfies both.
;;;
;;; Helper prefix: cif-.

;;; --- file-local helpers (cif- prefix) -----------------------------------

;; The class property, x_ free, and the class itself.
;; NBG COMPREHENSION (2026-10-15, the user's decision (i)): the map is FIXED as an
;; eigenvariable of the theorem BEFORE the induction and is a PARAMETER of the
;; class, which quantifies over nothing.  (Until 2026-10-15 the class was
;; { x_ | forall p_. CARD(IMAGE(p_, x_)) in NN }, a quantifier over every class
;; function inside a comprehension: Morse-Kelley, not NBG.  The induction
;; hypothesis is only ever used at the map being fixed, so nothing is lost.)
(define (cif-prop phi)  (list 'IN (list 'CARD (list 'IMAGE phi 'x_)) 'NN))
(define (cif-class phi) (list 'COMP 'x_ (cif-prop phi)))

;; Read the map off a goal (IN (CARD (IMAGE p U)) NN).
(define (cif-goal-map g)
  (if (and (pair? g) (eq? (car g) 'in)
           (pair? (cadr g)) (eq? (car (cadr g)) 'card)
           (pair? (cadr (cadr g))) (eq? (car (cadr (cadr g))) 'image))
      (cadr (cadr (cadr g)))
      (error "cif-goal-map: goal is not (IN (CARD (IMAGE p U)) NN):" (expression->string g))))

;; y in PAIR(a, a) is in context, and so is (AND (IN a SET) (IN a SET)):
;; land (= y a) and return it.
(define (cif-pair-eq! a y)
  (let* ((pm  (dk-fact! 'pairing-membership a a))
         (pmy (inst*! pm y))
         (eqy (list '= y a)))
    (have! eqy (lambda () (dk-only! pmy (list 'IN y (list 'PAIR a a))) (prop)))
    eqy))

;; Close any goal from a contradictory pair POS / NEG in context.  `prop' has an
;; atom cap (*prop-atom-cap*) and the lanes below carry a dozen atoms, so the
;; context is thinned to the pair first -- a `prop' that declines over the cap
;; is silent under `quietly', and the have! then reports its side goal open.
(define (cif-absurd! pos neg)
  (dk-only! pos neg)
  (prop))

;; goal (IN z (IMAGE p S)) with (IN y S) and (= (p y) z) in context.
(define (cif-in-image! y)
  (dk-image-goal!)
  (ew y)
  (dk-conj-close!))

;; goal (IN (CARD (IMAGE p U)) NN).  Context holds (IN U SET), (IN BIG SET) and
;; (IN (CARD BIG) NN).  Proves IMAGE(p, U) subset BIG element by element --
;; ON-PREIMAGE runs with goal (IN z BIG) and, in context, (IN z SET),
;; (IN y U), (= (p y) z) -- and closes by card-subset-nn.
(define (cif-finite-by-subset! p U big on-preimage)
  (let* ((small (list 'IMAGE p U))
         (incl  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ small) (list 'IN 'z_ big)))))
    (fact 'image-set p U)                                   ; (IN small SET)
    (have! incl
      (lambda ()
        (let* ((landed (dk-peel!))                          ; (IN z small)
               (z      (cadr (dk-goal)))
               (hyp    (car landed)))
          (fact 'membership-implies-sethood z small)        ; (IN z SET), before mac-h eats hyp
          (let* ((ex (dk-landed-1 (lambda () (mac-h 'image-membership-iff hyp))))
                 (y  (dk-skolem! ex)))                      ; (IN y U), (= (p y) z)
            (on-preimage z y)))))
    (have! (list 'AND (list 'IN big 'SET) (list 'IN (list 'CARD big) 'NN)))
    (let ((thm (dk-fact! 'card-subset-nn big)))
      (have! (list 'AND (list 'IN small 'SET) incl))
      (dk-apply! thm small)
      (ass))))

;;; -----------------------------------------------------------------------
;;; BASE:  EMPTY-SET in C.

(define (cif-base!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (cond
       ((equal? (dk-goal) '(in empty-set set))
        (fact 'empty-set-is-set) (ass))
       (#t
        ;; goal: CARD(IMAGE(phi, EMPTY-SET)) in NN, phi the fixed map
        (let ((p (cif-goal-map (dk-goal))))
          (fact 'empty-set-is-set)
          (have! '(IN (CARD EMPTY-SET) NN)
                 (lambda () (mac 'card-empty) (fact 'nn-zero-in) (ass)))
          (cif-finite-by-subset! p 'EMPTY-SET 'EMPTY-SET
            (lambda (z y)
              (cif-absurd! (list 'IN y 'EMPTY-SET)
                           (dk-fact! 'empty-set-has-no-members y))))))))
   (dk-opened (lambda () (comp-mi)))))

;;; -----------------------------------------------------------------------
;;; STEP:  S in SET, CARD S in NN, S in C, x in SET, x not in S
;;;          =>  UNION(S, PAIR(x, x)) in C.

;; The step premise of finite-set-induction with C := cif-class, spelled so
;; that `fact' finds it in context up to alpha.
(define (cif-step-formula phi)
  `(FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (IN S ,(cif-class phi))))
     (FORALL x (IMPLIES (AND (IN x SET) (NOT (IN x S)))
       (IN (UNION S (PAIR x x)) ,(cif-class phi)))))))

(define (cif-step! phi)
  (let* ((landed (dk-peel!))
         (g      (dk-goal))                       ; (in (union S (pair x x)) C)
         (S      (cadr (cadr g)))
         (x      (cadr (caddr (cadr g))))
         (U      (list 'UNION S (list 'PAIR x x))))
    (dk-split-all! landed)
    ;; {x} is a set, and U is a set -- wanted in every branch below
    (have! (list 'AND (list 'IN x 'SET) (list 'IN x 'SET)))
    (fact 'pairing x x)
    (have! (list 'AND (list 'IN S 'SET) (list 'IN (list 'PAIR x x) 'SET)))
    (fact 'union-set-closure S (list 'PAIR x x))
    ;; the induction hypothesis: the class property at S, i.e. CARD(IMAGE(phi, S)) in NN
    (let ((ih (dk-landed-find (lambda () (comp-me (list 'IN S (cif-class phi))))
                              (lambda (f)
                                (alpha-equiv? f (list 'IN (list 'CARD (list 'IMAGE phi S)) 'NN))))))
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (equal? (dk-goal) (list 'in U 'set))
             (ass)
             (cif-step-property! S x U ih)))
       (dk-opened (lambda () (comp-mi)))))))

;; goal: CARD(IMAGE(phi, U)) in NN; IH, CARD(IMAGE(phi, S)) in NN, is in context
(define (cif-step-property! S x U ih)
  (let* ((p   (cif-goal-map (dk-goal)))
         (px  (list p x))
         (img (list 'IMAGE p S)))
    (fact 'image-set p S)                         ; (IN img SET); ih is (IN (CARD img) NN)
    (use-em (list 'IN px 'SET)
      ;; p(x) defined:  IMAGE(p, U) subset {p(x)} u IMAGE(p, S)
      (lambda ()
        (let ((big (list 'UNION (list 'PAIR px px) img)))
          (have! (list 'AND (list 'IN px 'SET) (list 'IN px 'SET)))
          (fact 'pairing px px)
          (have! (list 'AND (list 'IN (list 'PAIR px px) 'SET) (list 'IN img 'SET)))
          (fact 'union-set-closure (list 'PAIR px px) img)
          (dk-split! (dk-fact! 'card-union-singleton-bound img px))   ; (IN (CARD big) NN)
          (cif-finite-by-subset! p U big
            (lambda (z y)
              (let ((cases (dk-landed-1 (lambda () (mac-h 'union-membership (list 'IN y U))))))
                (mac 'union-membership)           ; goal (OR (IN z {p(x)}) (IN z img))
                (use-cases cases
                  (lambda () (oi-r) (cif-in-image! y))
                  (lambda ()
                    (oi-l)
                    (cif-pair-eq! x y)                                    ; (= y x)
                    (have! (list '= px z) (lambda () (subst (list '= x y)) (ass)))
                    (have! (list '= z px) (lambda () (subst (list '= px z)) (rfl)))
                    (let* ((pm  (dk-fact! 'pairing-membership px px))
                           (pmz (inst*! pm z)))
                      (dk-only! pmz (list '= z px))
                      (prop)))))))))
      ;; p(x) undefined (or a proper class):  IMAGE(p, U) subset IMAGE(p, S)
      (lambda ()
        (cif-finite-by-subset! p U img
          (lambda (z y)
            (let ((cases (dk-landed-1 (lambda () (mac-h 'union-membership (list 'IN y U))))))
              (use-cases cases
                (lambda () (cif-in-image! y))
                (lambda ()
                  (cif-pair-eq! x y)                                      ; (= y x)
                  (have! (list '= px z) (lambda () (subst (list '= x y)) (ass)))
                  (have! (list 'IN px 'SET) (lambda () (subst (list '= px z)) (ass)))
                  (cif-absurd! (list 'IN px 'SET) (list 'NOT (list 'IN px 'SET))))))))))))

;;; -----------------------------------------------------------------------
;;; THE THEOREM.

(quietly (lambda ()
  (sp (make-wff '(FORALL phi (FORALL X
        (IMPLIES (IN X SET)
          (IMPLIES (IN (CARD X) NN)
                   (IN (CARD (IMAGE phi X)) NN)))))))
  ;; fix the map and the set first: phi is a parameter of the class
  (dk-peel!)                                      ; (IN X SET), (IN (CARD X) NN)
  (let* ((g   (dk-goal))                          ; (in (card (image phi X)) nn)
         (phi (cif-goal-map g))
         (X   (caddr (cadr (cadr g))))
         (C   (cif-class phi)))
    ;; the two induction premises, phi free
    (have! (list 'IN 'EMPTY-SET C) cif-base!)
    (have! (cif-step-formula phi) (lambda () (cif-step! phi)))
    (have! (list 'AND (list 'IN 'EMPTY-SET C) (cif-step-formula phi)))
    ;; finite-set-induction at C: every finite set is in C
    (let ((ind (dk-fact! 'finite-set-induction C)))
      (have! (list 'AND (list 'IN X 'SET) (list 'IN (list 'CARD X) 'NN)))
      (let ((inx (dk-apply! ind X)))
        (dk-landed-find (lambda () (comp-me inx)) (lambda (f) (alpha-equiv? f g)))
        (ass))))))
(qed 'card-image-finite)
(topic! 'card-image-finite 'combinatorial)

;;; centre-set-finite-guarded MOVED to theorem-library/ball-cover-lemmas.scm (2026-10-06, the
;;; library gate: a metric-space statement in a cardinality file).
