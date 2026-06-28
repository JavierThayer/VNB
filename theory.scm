;;; theory.scm -- theory management
;;;
;;; A THEORY consists of:
;;;   - a name
;;;   - a list of axioms (named formulas)
;;;   - a set of installed theorems (proved facts, with their macetes)
;;;   - a set of defined constants
;;;
;;; The base theory contains the VNB set-theory axioms.

(define-record-type <theory>
  (%make-theory name)
  theory?
  (name        theory-name)
  (axioms      theory-axioms       set-theory-axioms!)
  (theorems    theory-theorems     set-theory-theorems!)
  (constants   theory-constants    set-theory-constants!)
  (definitions theory-definitions  set-theory-definitions!))

(define (make-theory name)
  (let ((th (%make-theory name)))
    (set-theory-axioms!       th '())
    (set-theory-theorems!     th (make-equal-hash-table))
    (set-theory-constants!    th (make-equal-hash-table))
    (set-theory-definitions!  th '())
    th))

(define (theory-add-axiom! th name formula)
  (set-theory-axioms! th (cons (cons name formula) (theory-axioms th)))
  (install-theorem! name formula)  ; axioms are usable as theorems
  name)

(define (theory-add-theorem! th name formula)
  (hash-table-set! (theory-theorems th) name formula)
  (fluid-let ((*current-provenance* 'proven))
    (install-theorem! name formula))
  name)

;;; Add a result to the Proof Support Set.  Logically treated the same as
;;; an axiom or theorem (installs a macete, usable as an assumption), but
;;; tagged in *support-theorem-names* so (catalog) lists it under its own
;;; section.  Use for results we believe are provable but choose not to
;;; mechanize -- classical theorems, large constructions, etc.
(define (theory-add-support! th name formula)
  (hash-table-set! (theory-theorems th) name formula)
  (install-theorem! name formula)
  (register-support-theorem! name)
  name)

;;; User-facing: (support 'NAME 'formula) records a result in the current
;;; theory's Proof Support Set.  `add-to-pss' is the same operation under the
;;; plain-English name -- (support ...) literally means "add NAME to the PSS".
(define (support name formula)
  (theory-add-support! *current-theory* name formula))
(define add-to-pss support)

;;; User-facing: (warrant! 'NAME 'kind "informal justification text")
;;; records the grounds on which NAME is accepted (see *warrant-kinds* in
;;; macetes.scm).  Independent of how NAME was installed -- attaches to
;;; axioms, PSS entries, or proven theorems alike.  Place the call right
;;; after the statement it warrants.
(define (warrant! name kind text)
  (register-warrant! name kind text))

;;; User-facing: (gloss! 'NAME "plain-English rendition of the statement")
;;; records what the formula SAYS in words -- for the deeply-nested supports
;;; whose s-expression does not read at a glance.  Orthogonal to warrant!
;;; (which records WHY we accept it); rendered by write-pss-md under the
;;; statement.  Place right after the statement, like warrant!.
(define (gloss! name text)
  (register-gloss! name text))

;;; User-facing: (category! 'NAME 'category) files NAME under one of the PSS
;;; categories (*pss-category-order* in macetes.scm).  The category is also the
;;; INTAKE DISCIPLINE for new entries: when a proof is blocked and you assert a
;;; fact instead of grinding, the category says WHAT KIND of fact it is and why
;;; grinding is not worth it.  Place right after the statement, like warrant!;
;;; new supports SHOULD carry one (load.scm soft-nudges the uncategorised count).
(define (category! name cat)
  (register-category! name cat))

(define (theory-get-theorem th name)
  (hash-table-ref/default (theory-theorems th) name #f))

(define (theory-add-constant! th name definition)
  (hash-table-set! (theory-constants th) name definition)
  name)

;;; Add a defined constant with characterizing axioms.
;;; char-axioms is a list of (axiom-name . formula) pairs.
;;; The axioms are installed as usable theorems but recorded under
;;; 'definitions', not 'axioms', so the distinction is preserved.
(define (theory-add-definition! th const-name char-axioms)
  (for-each (lambda (pair)
              (install-theorem! (car pair) (cdr pair)))
            char-axioms)
  (set-theory-definitions! th
    (cons (cons const-name char-axioms)
          (theory-definitions th)))
  ;; A defined constant is a constant head, not a function variable.
  (register-constant! const-name 'defined-fn)
  const-name)

;;; User-facing: (def-constant 'NAME '(ax1 formula1) '(ax2 formula2) ...)
;;; Existence and uniqueness are the user's responsibility.
(define (def-constant const-name . char-axiom-specs)
  (fluid-let ((*current-provenance* 'definitional))
    (theory-add-definition! *current-theory* const-name
      (map (lambda (spec) (cons (car spec) (cadr spec)))
           char-axiom-specs))))

;;; Display all definitions in the current theory.
(define (display-definitions)
  (let ((defs (theory-definitions *current-theory*)))
    (if (null? defs)
        (display "No definitions.\n")
        (for-each
          (lambda (entry)
            (display "CONSTANT: ")
            (display (car entry))
            (newline)
            (for-each
              (lambda (ax)
                (display "  [")
                (display (car ax))
                (display "] ")
                (write (cdr ax))
                (newline))
              (cdr entry)))
          (reverse defs)))))

;;; Display the Proof Support Set: every name registered via (support ...)
;;; with its formula.  PSS entries are logically theorems we accept
;;; without a machine-checked proof; this lists them for review.
(define (display-pss)
  (let ((names (reverse *support-theorem-names*)))
    (cond
      ((null? names)
       (display "No PSS entries.\n"))
      (else
       (display "Proof Support Set (")
       (display (length names))
       (display " entries):\n\n")
       (for-each
         (lambda (name)
           (display name) (newline)
           (display "    ")
           (write (lookup-theorem name))
           (newline) (newline))
         names)))))

;;; Display every warranted statement, grouped by warrant kind (weakest
;;; first).  Triage view: the `hand-wave' and `well-known' groups are the
;;; ones most worth discharging into informal or formal proofs later.
(define (display-warrants)
  (let ((any #f))
    (for-each
      (lambda (kind)
        (let ((names (filter (lambda (n)
                               (let ((w (warrant-of n)))
                                 (and w (eq? (car w) kind))))
                             (sort (hash-table-keys *warrants*)
                                   (lambda (a b)
                                     (string<? (symbol->string a)
                                               (symbol->string b)))))))
          (unless (null? names)
            (set! any #t)
            (display kind) (display " (") (display (length names))
            (display "):\n")
            (for-each
              (lambda (n)
                (display "    ") (display n) (display " -- ")
                (display (cdr (warrant-of n))) (newline))
              names)
            (newline))))
      *warrant-kinds*)
    (unless any (display "No warrants recorded.\n"))))

;;; Install a named predicate defined by class membership.
;;; (def-predicate 'P 'S) adds axiom: (FORALL x (IFF (P x) (IN x S)))
(define (def-predicate name class-expr)
  (fluid-let ((*current-provenance* 'definitional))
    (theory-add-axiom! *current-theory* name
      `(FORALL x (IFF (,name x) (IN x ,class-expr))))))

;;; -----------------------------------------------------------------------
;;; The base VNB set theory
;;;
;;; Axioms from note.pdf:
;;;   SET is a class constant; (IN a SET) means "a is a set".
;;;   IS-SET is the corresponding predicate: (IS-SET a) <-> (IN a SET).
;;;
;;;   1. Membership implies sethood of left argument (only sets can be members):
;;;        (FORALL a (FORALL b (IMPLIES (IN a b) (IN a SET))))
;;;   2. Extensionality for sets:
;;;        (FORALL a (FORALL b (IMPLIES (AND (IN a SET) (IN b SET))
;;;                                     (IFF (= a b)
;;;                                          (FORALL x (IFF (IN x a) (IN x b)))))))
;;;   3. Empty set:
;;;        (IN EMPTY-SET SET)
;;;        (FORALL x (NOT (IN x EMPTY-SET)))
;;;   4. Pairing (both arguments must be sets):
;;;        (FORALL a (FORALL b (IMPLIES (AND (IN a SET) (IN b SET))
;;;                                     (IN (PAIR a b) SET))))
;;;        (FORALL a (FORALL b (IMPLIES (AND (IN a SET) (IN b SET))
;;;          (FORALL x (IFF (IN x (PAIR a b)) (OR (= x a) (= x b)))))))
;;;   5. Big union (binder form, see expressions.scm BIG-UNION):
;;;        (BIG-UNION z A body) = union_{z in A} body
;;;      The sketched ZF-style (UNION-SET a) is NOT taken as primitive;
;;;      VNB uses the indexed binder, with kernel rules
;;;      pi-big-union-{sethood, mem-intro, mem-elim}!.  The ZF form is
;;;      the special case (BIG-UNION s S s).
;;;   6. Power set:
;;;        (FORALL a (IMPLIES (IN a SET) (IN (POWER a) SET)))
;;;        (FORALL a (FORALL x (IFF (IN x (POWER a))
;;;                                  (AND (IN x SET)
;;;                                       (FORALL z (IMPLIES (IN z x) (IN z a)))))))
;;;   7. Separation:
;;;        (FORALL a (IMPLIES (IN a SET) (IN (SEP x a p) SET)))
;;;
;;; (We defer the full axiom list; the base theory starts with these.)

(define (make-vnb-base-theory)
  (let ((th (make-theory 'VNB-SET-THEORY)))

    (theory-add-axiom! th 'membership-implies-sethood
      '(FORALL a (FORALL b (IMPLIES (IN a b) (IN a SET)))))

    (theory-add-axiom! th 'subset-def
      '(FORALL A (FORALL B
          (IFF (SUBSET A B)
               (FORALL x (IMPLIES (IN x A) (IN x B)))))))

    (theory-add-axiom! th 'subset-set
      '(FORALL A (SUBSET A SET)))

    (theory-add-axiom! th 'extensionality
      '(FORALL a (FORALL b
          (IMPLIES (AND (IN a SET) (IN b SET))
                   (IFF (= a b)
                        (FORALL x (IFF (IN x a) (IN x b))))))))

    ;; Class-extensionality.  Two classes with the same elements are equal,
    ;; with no set-of-both precondition.  Foundational NBG axiom; comment at
    ;; ~line 259 of this file previously flagged its absence.  Needed to
    ;; conclude ORD is a set from "a set K has the same elements as ORD".
    (theory-add-axiom! th 'class-extensionality
      '(FORALL A (FORALL B
          (IMPLIES (FORALL x (IFF (IN x A) (IN x B)))
                   (= A B)))))

    (theory-add-axiom! th 'empty-set-is-set
      '(IN EMPTY-SET SET))

    (theory-add-axiom! th 'empty-set-has-no-members
      '(FORALL x (NOT (IN x EMPTY-SET))))

    ;; Pairing requires both arguments to be sets; otherwise the membership
    ;; iff combined with membership-implies-sethood would force every class
    ;; into SET (any class a satisfies a ∈ PAIR(a,a) under the unconditional
    ;; iff, hence a ∈ SET, contradicting burali-forti).
    (theory-add-axiom! th 'pairing
      '(FORALL a (FORALL b
          (IMPLIES (AND (IN a SET) (IN b SET))
                   (IN (PAIR a b) SET)))))

    (theory-add-axiom! th 'pairing-membership
      '(FORALL a (FORALL b
          (IMPLIES (AND (IN a SET) (IN b SET))
                   (FORALL x
                     (IFF (IN x (PAIR a b))
                          (OR (= x a) (= x b))))))))

    (theory-add-axiom! th 'power-set
      '(FORALL a (IMPLIES (IN a SET) (IN (POWER a) SET))))

    (theory-add-axiom! th 'power-set-membership
      '(FORALL a (FORALL x
          (IFF (IN x (POWER a))
               (AND (IN x SET)
                    (FORALL z (IMPLIES (IN z x) (IN z a))))))))

    ;; CHOICE: if A is inhabited, (CHOICE A) is in A.
    ;; (REVIEW.md G-3) This is GLOBAL CHOICE in the NBG/Bourbaki sense:
    ;; A ranges over all classes, including proper classes such as ORD.
    ;; So `(CHOICE ORD) ∈ ORD` is asserted -- strictly stronger than ZFC's
    ;; Axiom of Choice (which is restricted to families of sets).  In
    ;; first-order set-theoretic terms this is the Hilbert ε for classes.
    (theory-add-axiom! th 'choice-axiom
      '(FORALL A
          (IMPLIES (FORSOME x (IN x A))
                   (IN (CHOICE A) A))))

    ;; -------------------------------------------------------------------
    ;; Function spaces and Cartesian products: sethood
    ;;
    ;; FUN is a primitive class constructor, total over all classes.
    ;; (FUN A)   = all total functions whose domain is A  (primary form)
    ;; (FUN A B) = {f in (FUN A) : forall x in A, f(x) in B}  (derived form)
    ;;
    ;; FUN(A) is generally a proper class (functions can have any codomain).
    ;; FUN(A,B) is a set exactly when both A and B are sets.
    ;; When A is a set, members of FUN(A) and FUN(A,B) are sets.
    ;; (CARTESIAN A B) is a set iff both factors are.

    ;; FUN(A,B) sethood
    (theory-add-axiom! th 'fun-set-iff
      '(FORALL A (FORALL B
          (IFF (IN (FUN A B) SET)
               (AND (IN A SET) (IN B SET))))))

    ;; f ∈ FUN(A,B) and A is a set ⟹ f is a set
    (theory-add-axiom! th 'fun-elements-are-sets
      '(FORALL A (FORALL B (FORALL f
          (IMPLIES (AND (IN f (FUN A B)) (IN A SET))
                   (IN f SET))))))

    ;; f ∈ FUN(A) and A is a set ⟹ f is a set
    (theory-add-axiom! th 'fun-domain-elements-are-sets
      '(FORALL A (FORALL f
          (IMPLIES (AND (IN f (FUN A)) (IN A SET))
                   (IN f SET)))))

    ;; f(x) is defined iff x ∈ A, when f ∈ FUN(A).
    ;; Recall VNB equality is partial: (= t t) is the definedness predicate
    ;; for the term t.  So `(= (f x) (f x))` reads "f(x) is defined", and
    ;; the iff says: f's domain is exactly A.  This also makes the domain
    ;; recoverable from f: see DOM(f) below.
    (theory-add-axiom! th 'fun-domain-apply-def
      '(FORALL A (FORALL f (FORALL x
          (IMPLIES (IN f (FUN A))
                   (IFF (= (f x) (f x))
                        (IN x A)))))))

    ;; Extensionality: functions in FUN(A) are equal iff they agree on all of A
    (theory-add-axiom! th 'fun-domain-extensionality
      '(FORALL A (FORALL f (FORALL g
          (IMPLIES (AND (IN f (FUN A)) (IN g (FUN A))
                        (FORALL x (IMPLIES (IN x A) (= (f x) (g x)))))
                   (= f g))))))

    ;; FUN(A,B) is exactly those functions in FUN(A) whose values lie in B
    (theory-add-axiom! th 'fun-codomain-iff
      '(FORALL A (FORALL B (FORALL f
          (IFF (IN f (FUN A B))
               (AND (IN f (FUN A))
                    (FORALL x (IMPLIES (IN x A) (IN (f x) B)))))))))

    ;; -------------------------------------------------------------------
    ;; IS-FUN(f) and DOM(f).
    ;;
    ;; IS-FUN(f): "f is a function" -- there exists a set A with f in FUN(A).
    ;; The strengthened fun-domain-apply-def (iff form) makes such an A
    ;; uniquely determined by f, justifying the term "the" domain.
    ;;
    ;; DOM(f): the domain of f as a class.  Characterised by membership:
    ;; x in DOM(f) iff x is a set and f(x) is defined.  Recall the VNB
    ;; partial-equality convention: (= t t) is the definedness predicate
    ;; for t.  When f in FUN(A) we have x in DOM(f) iff x in A
    ;; (dom-fun-membership); the class equality DOM(f) = A is a consequence
    ;; modulo class extensionality, which is not an axiom of VNB.

    (theory-add-axiom! th 'is-fun-def
      '(FORALL f
          (IFF (IS-FUN f)
               (FORSOME A (AND (IN A SET) (IN f (FUN A)))))))

    (theory-add-axiom! th 'dom-membership
      '(FORALL f (FORALL x
          (IFF (IN x (DOM f))
               (AND (IN x SET) (= (f x) (f x)))))))

    ;; Membership-level agreement between DOM(f) and the FUN-witness A.
    ;; DERIVED from dom-membership + fun-domain-apply-def (iff form) +
    ;; membership-implies-sethood; stated as an axiom for convenience.
    (theory-add-axiom! th 'dom-fun-membership
      '(FORALL A (FORALL f
          (IMPLIES (IN f (FUN A))
                   (FORALL x (IFF (IN x (DOM f)) (IN x A)))))))

    ;; When A is a set, DOM(f) is a set (a subclass of A, by separation)
    ;; and DOM(f) = A as sets, by extensionality.  Stated as one axiom
    ;; for convenience.
    (theory-add-axiom! th 'dom-of-fun
      '(FORALL A (FORALL f
          (IMPLIES (AND (IN f (FUN A)) (IN A SET))
                   (AND (IN (DOM f) SET) (= (DOM f) A))))))

    ;; -------------------------------------------------------------------
    ;; RES(f, B): the restriction of f to B.
    ;;
    ;; Defined whenever f and B are -- bongo-style.  Typed-in-FUN(B) only
    ;; when f is a function and B is a subset of f's domain.  Outside that
    ;; case RES(f, B) exists as a term but carries no typing guarantees.
    ;;
    ;; Semantically:  RES(f, B) = lambda x in B. f(x)
    ;; (Cannot be written symbolically as VNB-LAMBDA because the raw
    ;; S-expression form does not carry a domain; we characterise RES
    ;; axiomatically instead.)

    (theory-add-axiom! th 'res-typing
      '(FORALL A
          (FORALL B
              (FORALL f
                  (IMPLIES (AND (IN f (FUN A)) (SUBSET B A))
                           (IN (RES f B) (FUN B)))))))

    (theory-add-axiom! th 'res-apply
      '(FORALL A
          (FORALL B
              (FORALL f
                  (FORALL x
                      (IMPLIES (AND (IN f (FUN A)) (SUBSET B A) (IN x B))
                               (= ((RES f B) x) (f x))))))))

    ;; DERIVED (from res-typing + res-apply + fun-codomain-iff):
    ;; restriction preserves codomain.
    (theory-add-axiom! th 'res-codomain
      '(FORALL A
          (FORALL B
              (FORALL C
                  (FORALL f
                      (IMPLIES (AND (IN f (FUN A C)) (SUBSET B A))
                               (IN (RES f B) (FUN B C))))))))

    ;; -------------------------------------------------------------------
    ;; PARTIAL-FUN: partial functions.
    ;;
    ;; A partial function on A is a (total) function defined on some
    ;; subset of A.  Two forms:
    ;;   (PARTIAL-FUN A)    -- domain bounded by A, codomain unconstrained;
    ;;                         generally a proper class (codomains arbitrary).
    ;;   (PARTIAL-FUN A C)  -- codomain fixed; a set when A, C are sets.
    ;;
    ;; Sethood of the binary form is stated as an axiom for now; it is
    ;; derivable using the BIG-UNION binder (the family
    ;; {FUN(B, C) : B in POWER(A)} is set-indexed and each member is a
    ;; set), but the derivation has not been carried out as a proof.

    (theory-add-axiom! th 'partial-fun-membership
      '(FORALL A
          (FORALL f
              (IFF (IN f (PARTIAL-FUN A))
                   (FORSOME B (AND (IN B (POWER A)) (IN f (FUN B))))))))

    (theory-add-axiom! th 'partial-fun-binary-membership
      '(FORALL A
          (FORALL C
              (FORALL f
                  (IFF (IN f (PARTIAL-FUN A C))
                       (FORSOME B (AND (IN B (POWER A)) (IN f (FUN B C)))))))))

    (theory-add-axiom! th 'partial-fun-binary-sethood
      '(FORALL A
          (FORALL C
              (IMPLIES (AND (IN A SET) (IN C SET))
                       (IN (PARTIAL-FUN A C) SET)))))

    (theory-add-axiom! th 'cartesian-set-iff
      '(FORALL A (FORALL B
          (IFF (IN (CARTESIAN A B) SET)
               (AND (IN A SET) (IN B SET))))))

    ;; TUPLES(A) is the class of all finite sequences of elements from A.
    ;; TUPLES(A) is a set when A is a set.
    (theory-add-axiom! th 'tuples-sethood
      '(FORALL A (IMPLIES (IN A SET) (IN (TUPLES A) SET))))

    ;; -------------------------------------------------------------------
    ;; MAKE-SET: the set of elements of a tuple.
    ;;   make-set-membership:
    ;;     x ∈ make-set(L) ↔ ∃ i ∈ NN. 1 ≤ i ∧ i ≤ length(L) ∧ nth(i, L) = x
    ;;   The 1 ≤ i ≤ length(L) bounds are essential.  nth out-of-range is
    ;;   unspecified in the intended model; without the bounds, an
    ;;   unspecified value would be a member of every make-set.
    ;;   make-set-sethood:    L ∈ TUPLES(A) ∧ A ∈ SET → make-set(L) ∈ SET
    ;;   make-set-empty:      make-set([]) = EMPTY-SET

    (theory-add-axiom! th 'make-set-membership
      '(FORALL x (FORALL L
          (IFF (IN x (MAKE-SET L))
               (FORSOME i (AND (IN i NN)
                          (AND (<= 1 i)
                          (AND (<= i (LENGTH L))
                               (= (NTH i L) x)))))))))

    (theory-add-axiom! th 'make-set-sethood
      '(FORALL A (FORALL L
          (IMPLIES (AND (IN L (TUPLES A)) (IN A SET))
                   (IN (MAKE-SET L) SET)))))

    (theory-add-axiom! th 'make-set-empty
      '(= (MAKE-SET (LIST)) EMPTY-SET))

    ;; -------------------------------------------------------------------
    ;; LENGTH: the number of elements in a tuple.
    ;;   length-of-empty: length([]) = 0
    ;;   length-in-nn:    L ∈ TUPLES(SET) → length(L) ∈ NN
    ;;   nth-in-range:    L ∈ TUPLES(A) ∧ 1 ≤ i ≤ length(L) → nth(i,L) ∈ A
    ;; (Recursive characterization of length requires a CONS/PREPEND constructor
    ;;  and a TUPLES induction principle, both pending.)

    (theory-add-axiom! th 'length-of-empty
      '(= (LENGTH (LIST)) 0))

    (theory-add-axiom! th 'length-in-nn
      '(FORALL L (IMPLIES (IN L (TUPLES SET)) (IN (LENGTH L) NN))))

    (theory-add-axiom! th 'nth-in-range
      '(FORALL A (FORALL i (FORALL L
          (IMPLIES (AND (IN i NN) (IN L (TUPLES A)) (<= 1 i) (<= i (LENGTH L)))
                   (IN (NTH i L) A))))))

    ;; -------------------------------------------------------------------
    ;; UNION, INTERSECTION, COMPLEMENT-IN are total over classes -- they
    ;; are defined whether or not their arguments are sets.  We axiomatise:
    ;;   (a) membership iff (binary form: characterises the operation
    ;;       semantically; n-ary uses the kernel rules pi-union-intro/elim
    ;;       and pi-intersection-intro/elim, which already accept any arity)
    ;;   (b) sethood closure (binary; n-ary follows by induction).
    ;; COMPLEMENT-IN is the relative complement A \ B (REVIEW.md D-6).
    ;; B need not be a set; A \ B is a set when A is a set since A\B ⊆ A.

    (theory-add-axiom! th 'union-set-closure
      '(FORALL A (FORALL B
          (IMPLIES (AND (IN A SET) (IN B SET))
                   (IN (UNION A B) SET)))))

    (theory-add-axiom! th 'union-membership
      '(FORALL A (FORALL B (FORALL x
          (IFF (IN x (UNION A B))
               (OR (IN x A) (IN x B)))))))

    (theory-add-axiom! th 'intersection-set-closure
      '(FORALL A (FORALL B
          (IMPLIES (OR (IN A SET) (IN B SET))
                   (IN (INTERSECTION A B) SET)))))

    (theory-add-axiom! th 'intersection-membership
      '(FORALL A (FORALL B (FORALL x
          (IFF (IN x (INTERSECTION A B))
               (AND (IN x A) (IN x B)))))))

    ;; Variadic decomposition rewrites for UNION and INTERSECTION.  Each is
    ;; the n-ary generalization of the binary *-membership axiom above;
    ;; together with the kernel rules pi-{union,intersection}-{intro,elim}!
    ;; they let proofs treat membership in an n-ary join/meet as a flat
    ;; disjunction/conjunction in one step instead of n-1 binary peels.
    ;; The RESTVAR/SPLICE forms are recognised by the macete engine; see
    ;; macetes.scm.

    (theory-add-axiom! th 'union-decompose
      '(FORALL x (FORALL AS
          (IFF (IN x (UNION (RESTVAR AS)))
               (SPLICE OR e AS (IN x e))))))

    (theory-add-axiom! th 'intersection-decompose
      '(FORALL x (FORALL AS
          (IFF (IN x (INTERSECTION (RESTVAR AS)))
               (SPLICE AND e AS (IN x e))))))

    ;; cartesian-decompose is a procedural macete (see below), not an
    ;; axiom: its replacement introduces n FORSOME-bound fresh variables
    ;; per invocation, which cannot be expressed as a static template.
    ;; Semantically it is the axiom schema
    ;;   x ∈ CARTESIAN(A_1, ..., A_n)  ↔  ∃a_1 ∈ A_1. ... ∃a_n ∈ A_n.
    ;;                                         x = [a_1, ..., a_n]
    ;; one instance per arity n ≥ 1.

    (theory-add-axiom! th 'complement-in-set-closure
      '(FORALL A (FORALL B
          (IMPLIES (IN A SET)
                   (IN (COMPLEMENT-IN A B) SET)))))

    (theory-add-axiom! th 'complement-in-membership
      '(FORALL A (FORALL B (FORALL x
          (IFF (IN x (COMPLEMENT-IN A B))
               (AND (IN x A) (NOT (IN x B))))))))

    ;; SET and ORD are primitive class constants
    (theory-add-constant! th 'SET 'SET)
    (theory-add-constant! th 'ORD 'ORD)

    th))

;;; -----------------------------------------------------------------------
;;; Global current theory (can be rebound)

(define *current-theory*
  (fluid-let ((*current-provenance* 'primitive))
    (make-vnb-base-theory)))

;;; Install IS-SET predicate: (IS-SET x) <-> (IN x SET)
(def-predicate 'IS-SET 'SET)

;;; Install IS-ORD predicate: (IS-ORD x) <-> (IN x ORD)
(def-predicate 'IS-ORD 'ORD)

(define (current-theory) *current-theory*)

;;; -----------------------------------------------------------------------
;;; rewrite-by-proc: top-down walker driving procedural macetes.
;;;
;;; (proc expr bvars) is called at every position.  If it returns a
;;; non-#f new expression, that is the rewrite for that position (and the
;;; walker does not descend further into it).  Otherwise the walker
;;; descends through propositional connectives and binders, threading the
;;; in-scope bound-variable list so the proc can pass it to fresh-var.
;;; Stops at atoms, term-forming heads, and any pair whose head is not
;;; recognised below.

(define (rewrite-by-proc proc expr)
  (rewrite-by-proc/bv proc expr '()))

(define (rewrite-by-proc/bv proc expr bvars)
  (let ((top (proc expr bvars)))
    (cond
      (top top)
      ((not (pair? expr)) expr)
      (else
       (case (car expr)
         ((AND OR IMPLIES IFF)
          (let ((l (rewrite-by-proc/bv proc (cadr  expr) bvars))
                (r (rewrite-by-proc/bv proc (caddr expr) bvars)))
            (if (and (eq? l (cadr expr)) (eq? r (caddr expr)))
                expr
                (list (car expr) l r))))
         ((NOT)
          (let ((r (rewrite-by-proc/bv proc (cadr expr) bvars)))
            (if (eq? r (cadr expr)) expr (list 'NOT r))))
         ((FORALL FORSOME IOTA)
          (let* ((bv   (cadr  expr))
                 (body (caddr expr))
                 (r    (rewrite-by-proc/bv proc body (cons bv bvars))))
            (if (eq? r body) expr (list (car expr) bv r))))
         ((SEP)
          ;; (SEP bv A p): A is outer scope; p is under bv.
          (let* ((bv (cadr   expr))
                 (A  (caddr  expr))
                 (p  (cadddr expr))
                 (rA (rewrite-by-proc/bv proc A bvars))
                 (rp (rewrite-by-proc/bv proc p (cons bv bvars))))
            (if (and (eq? rA A) (eq? rp p))
                expr
                `(SEP ,bv ,rA ,rp))))
         ((COMP)
          (let* ((bv (cadr  expr))
                 (p  (caddr expr))
                 (rp (rewrite-by-proc/bv proc p (cons bv bvars))))
            (if (eq? rp p) expr `(COMP ,bv ,rp))))
         ((VNB-LAMBDA)
          (let* ((bind-spec (cadr  expr))
                 (body      (caddr expr))
                 (new-bvars (vnb-lambda-bvars bind-spec))
                 (r         (rewrite-by-proc/bv proc body
                                                (append new-bvars bvars))))
            (if (eq? r body) expr `(VNB-LAMBDA ,bind-spec ,r))))
         (else expr))))))

;;; -----------------------------------------------------------------------
;;; cartesian-decompose: procedural macete.
;;;
;;; Rewrites (IN x (CARTESIAN A_1 ... A_n)) at any position reached by
;;; descending through propositional connectives and binders, into the
;;; nested existential chain
;;;
;;;   (FORSOME a_1 (AND (IN a_1 A_1)
;;;     ... (FORSOME a_n (AND (IN a_n A_n) (= x (LIST a_1 ... a_n)))) ...))
;;;
;;; with each a_i fresh w.r.t. x, all A_j, surrounding bound vars, and
;;; previously-generated a_k.

(define (build-cartesian-witness x classes #!optional bvars)
  (let* ((bvars      (if (default-object? bvars) '() bvars))
         (avoid-base (append bvars (cons x classes)))
         (fresh-names
          (let collect ((cs classes) (used '()))
            (cond
              ((null? cs) (reverse used))
              (else
               (collect (cdr cs)
                        (cons (apply fresh-var 'a
                                     (append used avoid-base))
                              used)))))))
    (let nest ((vars fresh-names) (cs classes))
      (cond
        ((null? vars)
         `(= ,x (LIST ,@fresh-names)))
        (else
         `(FORSOME ,(car vars)
            (AND (IN ,(car vars) ,(car cs))
                 ,(nest (cdr vars) (cdr cs)))))))))

(define (cartesian-decompose-fire expr bvars)
  (and (pair? expr) (eq? (car expr) 'IN)
       (let ((x    (cadr  expr))
             (prod (caddr expr)))
         (and (pair? prod) (eq? (car prod) 'CARTESIAN)
              (let ((classes (cdr prod)))
                (and (pair? classes)
                     (build-cartesian-witness x classes bvars)))))))

(install-macete!
  'cartesian-decompose
  (lambda (sqn)
    (let* ((asms (sequent-node-assumptions sqn))
           (goal (sequent-node-assertion   sqn))
           (g    (wff-formula goal))
           (dg   (sqn-dg sqn))
           (new  (rewrite-by-proc cartesian-decompose-fire g)))
      (cond
        ((alpha-equiv? new g) #f)
        (else
         (dg-apply-rule! dg 'cartesian-decompose
           (list (make-sequent asms (wff-child goal new)))
           sqn))))))

;;; -----------------------------------------------------------------------
;;; tuple-equality-decompose: procedural macete.
;;;
;;; Rewrites (= (LIST a_1 ... a_n) (LIST b_1 ... b_n)) to the conjunction
;;;   (AND (= a_1 b_1) (AND (= a_2 b_2) ... (= a_n b_n)))
;;; when both sides are LIST forms of equal length n.  Doesn't fire when
;;; lengths differ — that's a separate fact (two distinct-length tuples
;;; cannot be equal) and isn't this macete's job.  n=0 → TRUTH; n=1 →
;;; just (= a_1 b_1).  Bvars unused (no fresh vars needed).
;;;
;;; Procedural rather than declarative because the parallel rest-vars and
;;; zip-aware splice needed to express this in the macete engine would be
;;; more general infrastructure than warranted by one macete.

(define (build-tuple-equality as bs)
  (cond
    ((null? as)        'TRUTH)
    ((null? (cdr as))  `(= ,(car as) ,(car bs)))
    (else
     `(AND (= ,(car as) ,(car bs))
           ,(build-tuple-equality (cdr as) (cdr bs))))))

(define (tuple-equality-decompose-fire expr bvars)
  (and (pair? expr) (eq? (car expr) '=)
       (let ((lhs (cadr expr)) (rhs (caddr expr)))
         (and (pair? lhs) (eq? (car lhs) 'LIST)
              (pair? rhs) (eq? (car rhs) 'LIST)
              (let ((as (cdr lhs)) (bs (cdr rhs)))
                (and (= (length as) (length bs))
                     (build-tuple-equality as bs)))))))

(install-macete!
  'tuple-equality-decompose
  (lambda (sqn)
    (let* ((asms (sequent-node-assumptions sqn))
           (goal (sequent-node-assertion   sqn))
           (g    (wff-formula goal))
           (dg   (sqn-dg sqn))
           (new  (rewrite-by-proc tuple-equality-decompose-fire g)))
      (cond
        ((alpha-equiv? new g) #f)
        (else
         (dg-apply-rule! dg 'tuple-equality-decompose
           (list (make-sequent asms (wff-child goal new)))
           sqn))))))
