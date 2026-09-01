;;; field-ring-view.scm -- EVERY FIELD IS A FIELD-RING.
;;;
;;;     forall s. IS-FIELD(s) ==> IS-FIELD-RING(FIELD-AS-INTEGRAL-DOMAIN(s))
;;;
;;; WHY THIS MATTERS.  `IS-FIELD-RING' (field.scm) was written on 2026-08-23 to
;;; repair `IS-VECTOR-SPACE', which had pinned length(scal(s)) to 6 through
;;; MODULE and to 8 through IS-FIELD: unsatisfiable, and every theorem over it
;;; -- hahn-banach, norm-as-sup, vector-taylor -- vacuous from the day the file
;;; was written.  The repair made the predicate satisfiable.  It did NOT exhibit
;;; anything satisfying it: `structure-exemplification-audit' still listed
;;; field-ring, vector-space, module and normed-vector-space as UNWITNESSED,
;;; i.e. predicates nothing in the tree ever constructs an object for.  A
;;; repaired-but-unwitnessed predicate is better than a refuted one and is still
;;; not a thing you can reason about.
;;;
;;; This is the bridge.  QQ-FIELD is a declared 8-tuple with `qq-field-is-field',
;;; so the theorem below immediately witnesses FIELD-RING, and with it the
;;; VECTOR-SPACE scalar law.
;;;
;;; WHY IT IS A THEOREM AND NOT A `def-functor'.  def-functor installs its typing
;;; claim as an AXIOM -- `theory-add-axiom!' at structures.scm:1171, inside a
;;; `definitional' fluid-let, so contributing {} to every bill.  That is right
;;; for an accessor correspondence whose target laws are a shape-mechanical
;;; subset of the source's.  It is wrong here: IS-FIELD-RING's two laws are
;;; nontriviality (field-zero-not-one, a separate axiom about fields) and an
;;; EXISTENTIAL invertibility, witnessed by the field's MUL-INV slot.  Declaring
;;; that would assume exactly what wants demonstrating.
;;;
;;; WHAT HAD TO BE BUILT FIRST, and it is a finding in its own right:
;;; **SINGLETON had no membership characterisation anywhere in the tree.**  It
;;; occurs in IS-FIELD's own defining IFF (via `derived NON-ZERO', field.scm:44)
;;; and in QQ-FIELD's tuple, and nothing said `x in singleton(y) iff x = y'.  So
;;; nothing could be shown to be in or out of NON-ZERO(s), and the invertibility
;;; law -- stated over `a in non-zero(s)' -- was unreachable from `a in carr(s),
;;; a /= zero(s)'.  PAIR is in the same state (only `pairing', its sethood).
;;; SINGLETON is defined here as MAKE-SET(LIST y): an explicit closed term in the
;;; old vocabulary, conservative by unfolding, which is the tree's own standard
;;; for a definition (see the NN-MINUS / CHOOSE precedent).  It would sit better
;;; in a set-basics file; it is here because the membership proof needs the
;;; interactive tactics, which structure-library/ loads before.

(def-functoid 'SINGLETON '(y_) '(MAKE-SET (LIST y_)))
(sp (make-wff '(FORALL y_ (== (SINGLETON y_) (MAKE-SET (LIST y_))))))
(di) (mac 'SINGLETON) (qrfl) (qed 'singleton-unfold)

(sp (make-wff '(FORALL y_ (FORALL x_ (IFF (IN x_ (SINGLETON y_))
                                          (AND (IN x_ SET) (= x_ y_)))))))
(di)
(mac 'singleton-unfold) (mac 'make-set-membership) (len-r)
(define sm-br (dk-opened (lambda () (di))))

;; ---- FORWARD: membership gives x = y
(dk-focus! (car sm-br))
(dk-split! (car (dk-asms)))
(let* ((ex (any-pred (dk-head? 'FORSOME) (dk-asms))))
  (dk-split! (dk-landed-1 (lambda () (ai ex)))))
(display "fwd asms: ") (write (map expression->string (dk-asms))) (newline)
(let* ((eqn (any-pred (lambda (a) (and (pair? a) (eq? (car a) '=)
                                       (pair? (cadr a)) (eq? (car (cadr a)) 'NTH)))
                      (dk-asms)))
       (i   (cadr (cadr eqn))))
  (display "index var: ") (write i) (newline)
  ;; nn-le-antisym's antecedents are CURRIED (a <= b implies b <= a implies ...)
  ;; and it is guarded on both being in NN, so `fact' detaches all four from
  ;; context once 1 in nn is there -- no AND to build.
  (fact 'nn-one-in)
  (fact 'nn-le-antisym i 1)
  (dk-have! (list '= (list 'NTH i (list 'LIST 'y_)) 'y_)
    (lambda () (subst (list '= i 1)) (nth-r) (rfl)))
  (fact 'eq-sym (list 'NTH i '(LIST y_)) 'x_)
  (fact 'eq-trans 'x_ (list 'NTH i '(LIST y_)) 'y_))
(for-each (lambda (n) (dk-focus! n) (ass))
          (dk-opened (lambda () (di))))
;; ---- BACKWARD: x = y gives membership, witnessed by index 1
(dk-focus! (cadr sm-br))
(dk-split! (car (dk-asms)))
(fact 'nn-one-in) (fact 'nn-le-refl 1)
(fact 'eq-sym 'x_ 'y_)
(for-each
 (lambda (n)
   (dk-focus! n)
   (let ((g (dk-goal)))
     (if (and (pair? g) (eq? (car g) 'FORSOME))
         (begin (ew 1)
                (nth-r)
                (display (expression->string (dk-goal))) (newline)
                (from-context!))
         (ass))))
 (dk-opened (lambda () (di))))
(display "TOTAL leaves: ") (write (length (proof-leaves))) (newline)
(for-each (lambda (n) (display "  leaf: ")
            (display (expression->string (wff-formula (sequent-node-assertion n)))) (newline))
          (proof-leaves))

(qed 'singleton-membership)

(define (frv-slot! nm acc)
  (sp (make-wff (list 'FORALL 'f_
        (list '== (list acc '(FIELD-AS-INTEGRAL-DOMAIN f_)) (list acc 'f_)))))
  (di) (slot acc) (mac 'FIELD-AS-INTEGRAL-DOMAIN) (nth-r) (slot acc) (qrfl)
  (if (not (proof-done? *ps*)) (error "frv-slot!: did not close" nm))
  (qed nm))
(frv-slot! 'field-id-carr 'CARR)
(frv-slot! 'field-id-mul  'MUL)
(frv-slot! 'field-id-one  'ONE)
(frv-slot! 'field-id-zero 'ZERO)
;; ADD and NEG too: the MODULE action laws quantify over add(scal(s)) and the
;; abelian-group law over neg(scal(s)), so a vector space over a FIELD needs the
;; whole six-slot read-off, not the four the field-ring bridge itself used.
(frv-slot! 'field-id-add  'ADD)
(frv-slot! 'field-id-neg  'NEG)

(sp (make-wff '(FORALL s_ (IMPLIES (IS-FIELD s_)
                 (IS-FIELD-RING (FIELD-AS-INTEGRAL-DOMAIN s_))))))
(di)
(mac 'IS-FIELD-RING)
(mac 'field-id-carr) (mac 'field-id-mul) (mac 'field-id-one) (mac 'field-id-zero)
(di)                       ; assume is-field(s_)
;; Land every consequence of IS-FIELD we will need BEFORE unfolding it:
;; `mac-h' REPLACES the assumption it unfolds, so is-field(s_) is gone after.
(fact 'field-as-integral-domain-is-integral-domain 's_)
(fact 'integral-domain-is-commutative-ring '(FIELD-AS-INTEGRAL-DOMAIN s_))
(fact 'field-zero-not-one 's_)
(fact 'field-mul-inverse 's_)
(dk-split! (dk-landed-1 (lambda () (mac-h 'is-field '(IS-FIELD s_)))))

(define (fr-close!)
  (let ((g (dk-goal)))
    (cond
      ((and (pair? g) (eq? (car g) 'AND))
       (for-each (lambda (n) (dk-focus! n) (fr-close!))
                 (dk-opened (lambda () (di)))))
      ((and (pair? g) (eq? (car g) 'FORALL))
       ;; invertibility: the one conjunct with content
       (di) (di)                ; peel the binder AND the a /= 0 guard
       ;; read the element off its TYPING in context, not off the goal's shape
       (let* ((typ (any-pred (lambda (x) (and (pair? x) (eq? (car x) 'IN)
                                              (equal? (caddr x) '(CARR s_))
                                              (symbol? (cadr x))))
                             (dk-asms)))
              (a (cadr typ)))
         ;; a in carr(s_), a /= zero(s_)  ==>  a in non-zero(s_)
         (dk-have! (list 'NOT (list 'IN a (list 'SINGLETON '(ZERO s_))))
           (lambda ()
             (fact 'singleton-membership '(ZERO s_) a)
             (prop)))
         (dk-have! (list 'IN a (list 'DIFFERENCE '(CARR s_) (list 'SINGLETON '(ZERO s_))))
           (lambda ()
             (fact 'difference-membership '(CARR s_) (list 'SINGLETON '(ZERO s_)) a)
             (prop)))
         (dk-have! (list 'IN a '(NON-ZERO s_))
           (lambda () (subst '(= (NON-ZERO s_) (DIFFERENCE (CARR s_) (SINGLETON (ZERO s_)))))
                      (ass)))
         ;; recip(s_)(a) is in non-zero(s_), hence in carr(s_)
         (fact 'fun-apply-type-c '(MUL-INV s_) '(NON-ZERO s_) '(NON-ZERO s_) a)
         (dk-have! (list 'IN (list '(MUL-INV s_) a) '(CARR s_))
           (lambda ()
             (fact 'eq-sym '(NON-ZERO s_)
                   '(DIFFERENCE (CARR s_) (SINGLETON (ZERO s_))))
             (dk-have! (list 'IN (list '(MUL-INV s_) a)
                             '(DIFFERENCE (CARR s_) (SINGLETON (ZERO s_))))
               (lambda () (subst '(= (DIFFERENCE (CARR s_) (SINGLETON (ZERO s_)))
                                     (NON-ZERO s_)))
                          (ass)))
             (fact 'difference-membership '(CARR s_) (list 'SINGLETON '(ZERO s_))
                   (list '(MUL-INV s_) a))
             (prop)))
         ;; the inverse law, at a
         ;; the inverse law at a_ -- cited by NAME, not found by shape: the
         ;; context now holds several universals mentioning MUL-INV (the
         ;; fun-apply-type-c instantiation chain), and a shape finder picks the
         ;; wrong one.
         (inst+ (any-pred
                 (lambda (x)
                   (and (pair? x) (eq? (car x) 'FORALL)
                        (let ((b (caddr x)))
                          (and (pair? b) (eq? (car b) 'IMPLIES)
                               (let ((c (caddr b)))
                                 (and (pair? c) (eq? (car c) '=)))))))
                 (dk-asms))
                a)
         (ew (list '(MUL-INV s_) a))
         (from-context!)))
      ;; field-zero-not-one gives  zero /= one;  the goal wants  one /= zero.
      ((and (pair? g) (eq? (car g) 'NOT)
            (pair? (cadr g)) (eq? (car (cadr g)) '=)
            (equal? (cadr (cadr g)) '(ONE s_)))
       (fact 'neq-sym '(ZERO s_) '(ONE s_))
       (ass))
      (else (ass)))))
(fr-close!)
(qed 'field-is-field-ring)
(topic! 'field-is-field-ring 'algebra)
(alias! 'field-is-field-ring "every field is a field-ring")
