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
;;; claim as an AXIOM -- `add-axiom!' at structures.scm:1171, inside a
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

;;; The SINGLETON def-functoid MOVED 2026-09-20 (batch 12-A) to
;;; structure-library/set-vocabulary.scm, for the reason this header gives: the
;;; definition needs nothing, only the membership PROOF below needs the
;;; interactive tactics.  structure-library/field.scm states IS-FIELD's
;;; defining IFF with the head.  The two proofs stay here, unchanged.
;;; MOVED 2026-10-27 (integration): the proof of `singleton-unfold' is now in theorem-library/singleton-membership.scm
;;; (library core), loaded just before this file.

;;; MOVED 2026-10-27 (integration): the proof of `singleton-membership' is now in theorem-library/singleton-membership.scm
;;; (library core), loaded just before this file.

;;; GUARDED by IS-FIELD(f_) (R4 species (g), approved 2026-10-13): unguarded,
;;; f_ = [0] makes CARR(f_) denote while ADD(f_) = NTH(2, [0]) does not, so the
;;; view tuple does not denote and the read-off is false.  The guard certifies the
;;; accessor components as sets; `nth-r' owes nothing.
(define (frv-slot! nm acc)
  (sp (make-wff (list 'FORALL 'f_
        (list 'IMPLIES '(IS-FIELD f_)
          (list '== (list acc '(FIELD-AS-INTEGRAL-DOMAIN f_)) (list acc 'f_))))))
  (di) (di) (slot acc) (mac 'FIELD-AS-INTEGRAL-DOMAIN) (nth-r) (slot acc) (qrfl)
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

;;; ======================================================================
;;; A field-ring is an integral domain.  MOVED 2026-11-15 (D8) from
;;; theorem-library/gal-poly.scm, unchanged but for the local helper's prefix: the
;;; typing of FIELD-AS-INTEGRAL-DOMAIN, proven below from it, is cited from this
;;; file on, and gal-poly loads ~250 entries later.
;;; ======================================================================
(define (frv-conjs f) (if (and (pair? f) (eq? (car f) 'AND)) (append (frv-conjs (cadr f)) (frv-conjs (caddr f))) (list f)))
(define (frv-iff! thm lhs . args)
  (let ((ii (apply dk-cite! thm args)))
    (if (not (every dk-asm? (frv-conjs (caddr ii))))
        (begin
          (dk-have! (caddr ii) (lambda () (dk-close-if! (lambda () (dk-only! ii lhs)) prop)))
          (dk-split-all! (list (caddr ii)))))
    (caddr ii)))
(sp (make-wff '(FORALL s (IMPLIES (IS-FIELD-RING s) (IS-INTEGRAL-DOMAIN s)))))
(dk-peel!)
(define frv7-fi (frv-iff! 'is-field-ring-def '(IS-FIELD-RING s) 's))
(dk-cite! 'commutative-ring-is-ring 's)
(dk-cite! 'ring-zero-in 's)
(define frv7-ii (dk-cite! 'is-integral-domain-def 's))
(dk-have! (caddr frv7-ii)
  (lambda ()
    (dk-conj-close!
      (lambda ()
        (if (dk-asm? (dk-goal)) (ass)
            (let* ((ls (dk-peel!))
                   (eq (car (filter (dk-head? '=) ls)))
                   (a (cadr (cadr eq))) (b (caddr (cadr eq))))
              (use-em (list '= a '(ZERO s))
                (lambda () (dk-close-if! (lambda () (dk-only! (list '= a '(ZERO s)))) prop))
                (lambda ()
                  (let* ((inv (dk-pick (lambda (fm) (and (dk-head-is? fm 'FORALL) (dk-contains? fm 'FORSOME) (dk-contains? fm '(ONE s)))) "inverses"))
                         (ex (dk-apply! inv a))
                         (c (dk-skolem! ex)))
                    (dk-split-all!)
                    (let* ((h0 (list '= (list '(MUL s) c (list '(MUL s) a b)) (list '(MUL s) (list '(MUL s) a c) b)))
                           (x (dk-have! h0 (lambda () (crs))))
                           (h1 (dk-rewrite-h! h0 (list '(MUL s) a b) '(ZERO s)))
                           (h2 (dk-rewrite-h! h1 (list '(MUL s) a c) '(ONE s)))
                           (z1 (dk-cite! 'ring-mul-zero-right 's c))
                           (h3 (dk-rewrite-h! h2 (list '(MUL s) c '(ZERO s)) '(ZERO s)))
                           (z2 (dk-cite! 'ring-mul-left-id 's b))
                           (h4 (dk-rewrite-h! h3 (list '(MUL s) '(ONE s) b) b)))
                      (dk-have! (list '= b '(ZERO s)) (lambda () (subst (list '= b '(ZERO s))) (rfl))))
                    (dk-close-if! (lambda () (dk-only! (list '= b '(ZERO s)))) prop))))))))))
(dk-close-if! (lambda () (dk-only! frv7-ii (caddr frv7-ii))) prop)
(qed 'field-ring-is-integral-domain)
(topic! 'field-ring-is-integral-domain 'algebra)

(sp (make-wff '(FORALL s_ (IMPLIES (IS-FIELD s_)
                 (IS-FIELD-RING (FIELD-AS-INTEGRAL-DOMAIN s_))))))
(di)
(mac 'IS-FIELD-RING)
(mac 'field-id-carr) (mac 'field-id-mul) (mac 'field-id-one) (mac 'field-id-zero)
(di)                       ; assume is-field(s_)
;; Land every consequence of IS-FIELD we will need BEFORE unfolding it:
;; `mac-h' REPLACES the assumption it unfolds, so is-field(s_) is gone after.
;; IS-COMMUTATIVE-RING of the view, by the generic view driver on a lane (D8,
;; 2026-11-15): this used to be read off the typing AXIOM of the view, which is now
;; the theorem PROVEN below FROM this one.
(dk-have! '(IS-COMMUTATIVE-RING (FIELD-AS-INTEGRAL-DOMAIN s_))
  (lambda ()
    (let ((left (dk-view-close! 'FIELD-AS-INTEGRAL-DOMAIN 'COMMUTATIVE-RING)))
      (if (pair? left)
          (error "field-ring-view: the commutative-ring read-off left open"
                 (map (lambda (l) (expression->string (dk-goal-of l))) left))))))
;; field-zero-not-one and field-mul-inverse were cited here as separate axioms
;; until 2026-09-15, when they became (law ...) clauses of the FIELD declaration
;; (structure-library/field.scm) -- they were a support finishing a definition.
;; The `dk-split!' below now lands both itself, in the shapes the two fr-close!
;; branches already expect: the neq-sym branch, and the inst+ finder for "the
;; FORALL whose consequent is an `='".
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

;;; THE TYPING OF FIELD-AS-INTEGRAL-DOMAIN, PROVEN (D8, 2026-11-15).  It was the
;;; `definitional' typing axiom def-functor installed (views.scm); the obligation is
;;; deferred to here because the absence of zero divisors is a proof, not a read-off:
;;; a field is a field-ring (above), a field-ring is an integral domain (above).
(sp (make-wff '(FORALL r (IMPLIES (IS-FIELD r) (IS-INTEGRAL-DOMAIN (FIELD-AS-INTEGRAL-DOMAIN r))))))
(dk-peel!)
(fact 'field-is-field-ring 'r)
(fact 'field-ring-is-integral-domain '(FIELD-AS-INTEGRAL-DOMAIN r))
(ass)
(qed 'field-as-integral-domain-is-integral-domain)
(view-typing-installed! 'FIELD-AS-INTEGRAL-DOMAIN)
(topic! 'field-is-field-ring 'algebra)
(alias! 'field-is-field-ring "every field is a field-ring")
