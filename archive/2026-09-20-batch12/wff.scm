;;; wff.scm -- the <wff> record type (well-formed formula in a theory)
;;;
;;; A <wff> carries its raw S-expression formula and the name of its base
;;; theory.
;;;
;;; It used to carry a third field, a snapshot of the active local-context
;;; stack, which start-proof dissolved into root sequent assumptions.  The
;;; local-context facility was removed on 2026-07-29 (see contexts.scm) and
;;; the field went with it: nothing had populated it but make-wff, and
;;; nothing outside start-proof read it.

;;; The third field is a CACHE, not data: the alpha-invariant digest of the
;;; formula (expressions.scm), filled on first demand and never again.  A <wff>
;;; is immutable in its other two fields, so the digest cannot go stale.
;;;
;;; It exists because `wff-equiv?' is the hottest comparison in the prover --
;;; `context-add-assumption' calls it once per assumption on every assumption
;;; added, and `dg-find-sequent-node' called it once per node in the graph on
;;; every sequent posted -- and almost every one of those calls is a MISMATCH
;;; that alpha-equiv? has to walk into before it can say so.  Comparing two
;;; cached fixnums first rejects a mismatch in one machine word.
(define-record-type <wff>
  (%%make-concrete-wff formula theory digest)
  concrete-wff?
  (formula   concrete-wff-formula)
  (theory    concrete-wff-theory)
  (digest    concrete-wff-digest set-concrete-wff-digest!))

;;; The two-argument constructor every caller uses; the digest starts unfilled.
(define (%make-concrete-wff formula theory)
  (%%make-concrete-wff formula theory #f))

(define wff? concrete-wff?)

;;; The wff's alpha-invariant digest, computed once.
;;; (alpha-equiv? f1 f2) => equal digests; equal digests mean "now compare
;;; properly", never "equal".  See formula-hash in expressions.scm.
(define (wff-hash w)
  (or (concrete-wff-digest w)
      (let ((h (formula-hash (concrete-wff-formula w))))
        (set-concrete-wff-digest! w h)
        h)))

(define (wff-formula w)
  (if (concrete-wff? w)
      (concrete-wff-formula w)
      (error "wff-formula: not a wff" w)))

(define (wff-theory w)
  (if (concrete-wff? w)
      (concrete-wff-theory w)
      (error "wff-theory: not a wff" w)))

;;; Create a wff directly in a named theory.
;;; Used by start-proof and primitive inferences.
(define (wff-in-theory raw-formula theory-name)
  (%make-concrete-wff raw-formula theory-name))

;;; Create a derived wff inheriting its theory from a parent.
;;; Used inside primitive inferences to wrap subformulas.
(define (wff-child parent raw-formula)
  (%make-concrete-wff raw-formula (wff-theory parent)))

;;; Two wffs are equivalent when they share the same theory and their
;;; formulas are alpha-equivalent.  (Kind is implied by the formula
;;; structure, so a kind check would be redundant.)
;;; NOTE the digest is deliberately NOT consulted here.  A `(= (wff-hash w1)
;;; (wff-hash w2))' prefilter ahead of the alpha-equivalence test was built and
;;; removed on 2026-08-21: it made a wrong digest able to turn a #t into a #f,
;;; which is a silent wrong answer in the prover's hottest comparison, in
;;; exchange for a few percent.  `alpha-equiv?' stays the only thing that
;;; decides.  See dg-find-sequent-node (deduction-graphs.scm) for the
;;; measurements and the argument.
(define (wff-equiv? w1 w2)
  (or (eq? w1 w2)
      (and (equal? (wff-theory w1) (wff-theory w2))
           (alpha-equiv? (wff-formula w1) (wff-formula w2)))))

;;; wff->sexp: extract the raw S-expression from a wff.
;;; Synonym for wff-formula, provided as a user-facing name.
(define wff->sexp wff-formula)

;;; -----------------------------------------------------------------------
;;; expand-destructuring-quantifiers
;;;
;;; Rewrites surface forms of FORALL/FORSOME:
;;;   (FORALL  (IN var class) body)   =>  (FORALL  var (IMPLIES (IN var class) body))
;;;   (FORSOME (IN var class) body)   =>  (FORSOME var (AND     (IN var class) body))
;;;   (FORALL  (x y ...) body)        =>  (FORALL  x (FORALL  y (... body)))
;;;   (FORSOME (x y ...) body)        =>  (FORSOME x (FORSOME y (... body)))
;;;   (FORALL  x y ... body)          =>  (FORALL  x (FORALL  y (... body)))   [4+ args]
;;;   (FORSOME x y ... body)          =>  (FORSOME x (FORSOME y (... body)))   [4+ args]
;;; Bare-symbol quantifiers are left unchanged.  Called from make-wff
;;; before validate-wff!, so the rest of the system only ever sees the
;;; single-variable form.
;;;
;;; ... and the one non-quantifier rewrite, which is here because it is the
;;; same sugar (a binder list carrying its own domains) one head over:
;;;   (VNB-LAMBDA ((IN v1 A1) ... (IN vn An)) body)
;;;                                   =>  (VNB-LAMBDA (LIST v1 ... vn)
;;;                                                   (CARTESIAN A1 ... An) body)
;;;   (VNB-LAMBDA ((IN v A)) body)    =>  (VNB-LAMBDA v A body)
;;; See the clause itself for why this cannot change an accepted formula.

(define (all-symbols? lst)
  (or (null? lst)
      (and (symbol? (car lst)) (all-symbols? (cdr lst)))))

;;; Predicates for the binding-list quantifier syntax:
;;;   (FORALL ((b1) (b2) ...) body)
;;; Each bi is one of:
;;;   (var)                — unrestricted single variable
;;;   (IN var A)           — variable restricted to class A
;;;   (IN (LIST sym...) A) — tuple destructuring

(define (binding-spec? b)
  (cond
    ((not (pair? b)) #f)
    ((eq? (car b) 'IN)
     (and (= (length b) 3)
          (or (symbol? (cadr b))
              (and (pair? (cadr b))
                   (eq? (car (cadr b)) 'LIST)
                   (all-symbols? (cdr (cadr b)))))))
    ;; (var) or (var1 var2 ...) — non-empty list of symbols; 'in-headed lists
    ;; are handled above, so a leading 'in here would be a parse error.
    (else (and (not (null? b)) (not (eq? (car b) 'in)) (all-symbols? b)))))

;;; Every element is a TYPED single-variable binding (IN var A).  This is the
;;; strict half of `binding-spec?': no bare variables, no tuple destructuring.
;;; It decides whether a VNB-LAMBDA binder list carries its domains with it (see
;;; the VNB-LAMBDA clause of expand-destructuring-quantifiers) -- a list that is
;;; only PARTLY typed is left alone, because there is no honest reading of
;;; `[a in nn, x]' as a domain.
(define (all-typed-binder-specs? lst)
  (and (pair? lst)
       (let loop ((l lst))
         (or (null? l)
             (and (pair? (car l))
                  (eq? (car (car l)) 'IN)
                  (= (length (car l)) 3)
                  (symbol? (cadr (car l)))
                  (loop (cdr l)))))))

(define (all-binding-specs? lst)
  (and (pair? lst)
       (let loop ((l lst))
         (or (null? l)
             (and (binding-spec? (car l)) (loop (cdr l)))))))

(define (nest-quantifiers q vars body)
  (if (null? vars)
      body
      `(,q ,(car vars) ,(nest-quantifiers q (cdr vars) body))))

;;; -----------------------------------------------------------------------
;;; Binder lists scope LEFT TO RIGHT, and a guard may only mention binders to
;;; its LEFT.  `forall([s in CARR(r), r], FUBA(s))' expands to
;;;
;;;     (FORALL s (IMPLIES (IN s (CARR r)) (FORALL r (FUBA s))))
;;;
;;; so the `r' in the guard sits OUTSIDE the scope of the `forall r' that
;;; follows it: that `r' is FREE, and the later binder binds a different
;;; variable of the same name.  When the body mentions `r' too, one formula
;;; ends up carrying two distinct variables both spelled `r', and the printer
;;; round-trips the whole thing faithfully, so nothing on screen shows it.
;;;
;;; Nothing here is ill-formed, and `validate-wff!' already warns -- "symbol r
;;; is both bound (in some binder) and free in this formula", at the foot of
;;; this file.  But that warning names no binder, gives no reason, and fires on
;;; the ASSEMBLED formula, by which point the shape that caused it is gone.
;;; This one fires at binding-list expansion -- so on typed input as well as on
;;; installed forms -- and names both positions.  Warn-only, deliberately: the
;;; form has a meaning, it is simply almost never the intended one.
;;;
;;; `free-vars' rather than a symbol scan, so a guard that binds the name
;;; itself -- `s in {r | p(r)}' -- is not a false positive.

(define (binding-spec-vars b)
  (cond ((and (pair? b) (not (null? b)) (all-symbols? b) (not (eq? (car b) 'in)))
         b)                                            ; (v) or (v1 v2 ...)
        ((and (pair? b) (= (length b) 3) (eq? (car b) 'IN) (symbol? (cadr b)))
         (list (cadr b)))                              ; (IN v A)
        ((and (pair? b) (= (length b) 3) (eq? (car b) 'IN)
              (pair? (cadr b)) (eq? (car (cadr b)) 'LIST))
         (cdr (cadr b)))                               ; (IN (LIST v1 ...) A)
        (else '())))

(define (binding-spec-guard b)
  (and (pair? b) (= (length b) 3) (eq? (car b) 'IN) (caddr b)))

;;; The findings, as DATA: a list of (guarded-var guarded-pos offending-var
;;; binding-pos).  Returned rather than only printed, so the check is testable
;;; and callable -- `warn-forward-guard-reference!' is just its renderer.
(define (binding-list-forward-refs specs)
  (let loop ((ss specs) (i 1) (acc '()))
    (if (null? ss)
        (reverse acc)
        (let ((guard (binding-spec-guard (car ss)))
              (mine  (binding-spec-vars  (car ss))))
          (loop (cdr ss) (+ i 1)
                (if (not guard)
                    acc
                    (let per-var ((vs (free-vars guard)) (a acc))
                      (if (null? vs)
                          a
                          (per-var
                           (cdr vs)
                           ;; where, if anywhere, is this var bound LATER?
                           (let scan ((rest (cdr ss)) (j (+ i 1)))
                             (cond
                               ((null? rest) a)
                               ((memq (car vs) (binding-spec-vars (car rest)))
                                (cons (list (if (null? mine) '? (car mine))
                                            i (car vs) j)
                                      a))
                               (else (scan (cdr rest) (+ j 1))))))))))))))

(define (warn-forward-guard-reference! specs)
  (for-each
   (lambda (r)
     (let ((guarded (car r)) (i (cadr r)) (v (caddr r)) (j (cadddr r)))
       (display ";; warning: binder-list scope: the guard of ")
       (write guarded) (display " (binder ") (display i)
       (display ") mentions ") (write v) (newline)
       (display ";;   which is bound LATER, at binder ") (display j)
       (display ".  Binder lists scope left to right, so")  (newline)
       (display ";;   THIS ") (write v)
       (display " is FREE and binder ") (display j)
       (display " binds a different variable of the") (newline)
       (display ";;   same name.  Move ") (write v)
       (display " left of ") (write guarded)
       (display " if they were meant to be the same.") (newline)))
   (binding-list-forward-refs specs)))


;;; The NAME a destructuring binder's fresh variable gets.
;;;
;;; Default: the initials of the class name -- METRIC-SPACE gives `ms',
;;; TOP-SPACE gives `ts', MEASURE-SPACE gives `ms' too (and the collision is
;;; handled, since `fresh-var/bare' falls back to numbering).  A non-symbol
;;; class -- `cartesian(nn,nn)' -- has no name to work from and keeps `t'.
;;;
;;; Override: set `*destructuring-hint*' to a symbol and that is used instead,
;;; for every destructuring binder until it is set back to #f.  This is the
;;; manual control the user asked for; it is deliberately a plain global so it
;;; can be `set!' from the REPL or from Emacs mid-proof.
(define *destructuring-hint* #f)

(define (destructuring--hint class)
  (cond
    (*destructuring-hint* *destructuring-hint*)
    ((not (symbol? class)) 't)
    (else
     (let loop ((cs (string->list (symbol->string class))) (take #t) (acc '()))
       (cond ((null? cs)
              (if (null? acc) 't (string->symbol (list->string (reverse acc)))))
             ((char=? (car cs) #\-) (loop (cdr cs) #t acc))
             (take (loop (cdr cs) #f (cons (car cs) acc)))
             (else (loop (cdr cs) #f acc)))))))

;;; -----------------------------------------------------------------------
;;; WHAT A DESTRUCTURING BINDER PROJECTS WITH, and why it is not always NTH.
;;;
;;; `forall([[x,d] in metric-space], ...)' binds a fresh t ranging over the
;;; class and replaces x and d by the projections of t.  Until 2026-08-18 those
;;; projections were always `(NTH 1 t)' and `(NTH 2 t)', which is CORRECT --
;;; accessors are literally those projections -- and almost unusable, because
;;; every theorem in the library is stated with the accessor names.  The user
;;; who hit it put the objection exactly:
;;;
;;;     "no normal person will remember that the accessors for a metric space
;;;      are PTS and DIST."
;;;
;;; And the mismatch is a ONE-WAY street: the accessor macete rewrites
;;; `(DIST s)' to `(NTH 2 s)' and there is deliberately no reverse (a bare
;;; `NTH 2 s' could be a metric space's DIST or a group's OPR -- firing it back
;;; automatically would be a guess).  `slot-h' resolves instance macetes for a
;;; CONCRETE structure and finds none for a variable, so a destructured
;;; hypothesis could not be rewritten into accessor form at all.  The binder
;;; produced a goal that no library theorem could match and no tactic could
;;; bridge.
;;;
;;; The fix belongs here rather than in a tactic: the binder already NAMES the
;;; class, so when the class is a declared structure the expander can use its
;;; declared slot accessors and produce the shape the library is stated in.  A
;;; reader gets to write the destructuring form -- which is the notation they
;;; actually want -- and the machine supplies the accessor names they should not
;;; have to memorise.
;;;
;;; `*structure-slot-names-hook*' is set by structures.scm, which loads ~120
;;; files after this one.  A HOOK rather than a forward reference because the
;;; expander runs during that load too, so the lookup has to degrade cleanly to
;;; NTH rather than fail; and because an `environment-bound?' guard is not
;;; available -- the prover does not load into `system-global-environment', so
;;; asking that environment reports #f and silently disables the feature.
(define *structure-slot-names-hook* #f)

;;; The projections for a destructuring binder over CLASS with N variables,
;;; bound to the fresh variable T.  Slot accessors when CLASS is a declared
;;; structure of matching arity, positional NTH otherwise.
;;;
;;; An ARITY MISMATCH is an ERROR, not a silent fall-back to NTH: `[x,d,e] in
;;; metric-space' is a reader's mistake about the structure, and quietly giving
;;; them (NTH 3 t) of a two-slot tuple buries it.
(define (destructuring-projections class n t)
  (let ((slots (and *structure-slot-names-hook*
                    (symbol? class)
                    (*structure-slot-names-hook* class))))
    (cond
      ((not slots) (let loop ((i 1)) (if (> i n) '() (cons `(NTH ,i ,t) (loop (+ i 1))))))
      ((= (length slots) n) (map (lambda (a) `(,a ,t)) slots))
      (else
       (error (string-append
               "expand-binding-list: destructuring `" (symbol->string class)
               "' expects " (number->string (length slots)) " component(s), given "
               (number->string n))
              slots)))))

(define (expand-destructuring-quantifiers expr)
  (cond
    ((not (pair? expr)) expr)
    (else
     (let ((mapped (cons (car expr)
                         (map expand-destructuring-quantifiers (cdr expr)))))
       (cond
         ;; (FORALL (IN (LIST x1 ... xn) A) body) — tuple destructuring
         ;; Introduces a fresh tuple var t; substitutes xi -> (NTH i t) in body.
         ((and (memq (car mapped) '(FORALL FORSOME))
               (= (length mapped) 3)
               (pair? (cadr mapped))
               (eq? (car (cadr mapped)) 'IN)
               (= (length (cadr mapped)) 3)
               (pair? (cadr (cadr mapped)))
               (eq? (car (cadr (cadr mapped))) 'LIST)
               (all-symbols? (cdr (cadr (cadr mapped)))))
          (let* ((q     (car mapped))
                 (vars  (cdr (cadr (cadr mapped))))
                 (class (caddr (cadr mapped)))
                 (body  (caddr mapped))
                 (t     (fresh-var 't `(dummy ,class ,body ,@vars)))
                 (subst-body
                  (let loop ((vs vars) (i 1) (b body))
                    (if (null? vs)
                        b
                        (loop (cdr vs) (+ i 1)
                              (subst-free (car vs) `(NTH ,i ,t) b))))))
            (case q
              ((FORALL)  `(FORALL  ,t (IMPLIES (IN ,t ,class) ,subst-body)))
              ((FORSOME) `(FORSOME ,t (AND     (IN ,t ,class) ,subst-body))))))
         ;; (FORALL (IN var class) body) — guarded-quantifier sugar
         ((and (memq (car mapped) '(FORALL FORSOME))
               (= (length mapped) 3)
               (pair? (cadr mapped))
               (eq? (car (cadr mapped)) 'IN)
               (= (length (cadr mapped)) 3)
               (symbol? (cadr (cadr mapped))))
          (let ((q     (car mapped))
                (var   (cadr  (cadr mapped)))
                (class (caddr (cadr mapped)))
                (body  (caddr mapped)))
            (case q
              ((FORALL)  `(FORALL  ,var (IMPLIES (IN ,var ,class) ,body)))
              ((FORSOME) `(FORSOME ,var (AND     (IN ,var ,class) ,body))))))
         ;; (FORALL ((b1) (b2) ...) body) — new binding-list syntax.
         ;; Each binding is (var), (sym1 sym2...), (IN var A), or (IN (LIST...) A).
         ((and (memq (car mapped) '(FORALL FORSOME))
               (= (length mapped) 3)
               (pair? (cadr mapped))
               (all-binding-specs? (cadr mapped)))
          (let* ((q     (car mapped))
                 (specs (cadr mapped))
                 (body  (caddr mapped)))
            (warn-forward-guard-reference! specs)
            (let loop ((ss (reverse specs)) (acc body))
              (if (null? ss)
                  acc
                  (let ((b (car ss)))
                    (loop (cdr ss)
                          (cond
                            ;; (var) or (var1 var2 ...) — unrestricted, possibly grouped
                            ;; Note: 'in is a symbol too; exclude it from this branch.
                            ((and (not (null? b)) (all-symbols? b) (not (eq? (car b) 'in)))
                             (let inner ((vs (reverse b)) (a acc))
                               (if (null? vs) a (inner (cdr vs) `(,q ,(car vs) ,a)))))
                            ;; (IN var A) — restricted
                            ((and (= (length b) 3) (eq? (car b) 'IN) (symbol? (cadr b)))
                             (case q
                               ((FORALL)  `(FORALL  ,(cadr b) (IMPLIES (IN ,(cadr b) ,(caddr b)) ,acc)))
                               ((FORSOME) `(FORSOME ,(cadr b) (AND     (IN ,(cadr b) ,(caddr b)) ,acc)))))
                            ;; (IN (LIST sym...) A) — tuple destructuring
                            ((and (= (length b) 3) (eq? (car b) 'IN)
                                  (pair? (cadr b)) (eq? (car (cadr b)) 'LIST))
                             (let* ((vars  (cdr (cadr b)))
                                    (class (caddr b))
                                    (t     (fresh-var/bare (destructuring--hint class)
                                                           `(dummy ,class ,acc ,@vars)))
                                    (projs (destructuring-projections class (length vars) t))
                                    (subst-acc
                                     (let sub ((vs vars) (ps projs) (a acc))
                                       (if (null? vs)
                                           a
                                           (sub (cdr vs) (cdr ps)
                                                (subst-free (car vs) (car ps) a))))))
                               (case q
                                 ((FORALL)  `(FORALL  ,t (IMPLIES (IN ,t ,class) ,subst-acc)))
                                 ((FORSOME) `(FORSOME ,t (AND     (IN ,t ,class) ,subst-acc))))))
                            (else (error "expand-binding-list: bad spec" b q)))))))))
         ;; (FORALL (x y ...) body) — list-of-vars sugar
         ((and (memq (car mapped) '(FORALL FORSOME))
               (= (length mapped) 3)
               (pair? (cadr mapped))
               (all-symbols? (cadr mapped))
               (not (null? (cadr mapped))))
          (nest-quantifiers (car mapped) (cadr mapped) (caddr mapped)))
         ;; (FORALL x y ... body) — variadic sugar (4+ total elements)
         ((and (memq (car mapped) '(FORALL FORSOME))
               (>= (length mapped) 4)
               (all-symbols? (reverse (cdr (reverse (cdr mapped))))))
          (let* ((args  (cdr mapped))
                 (vars  (reverse (cdr (reverse args))))
                 (body  (car (reverse args))))
            (nest-quantifiers (car mapped) vars body)))
         ;; (VNB-LAMBDA ((IN v1 A1) ... (IN vn An)) body) -- the binder list
         ;; carries its own domains and there is no separate DOMAIN argument.
         ;; This is the quantifiers' `forall([p in NN, q in NN], ...)' spelling
         ;; applied to a lambda, and a user who has just written the one will
         ;; write the other.  It desugars to the canonical form:
         ;;
         ;;   n > 1  ->  (VNB-LAMBDA (LIST v1 ... vn) (CARTESIAN A1 ... An) body)
         ;;   n = 1  ->  (VNB-LAMBDA v1 A1 body)
         ;;
         ;; -- the SAME S-expression the explicit spelling produces, so nothing
         ;; downstream (lam-t's componentwise typing, lam-b, the printer) needs
         ;; to know this syntax exists.  The single-binder case collapses to the
         ;; bare-symbol binder rather than a one-element LIST over a one-factor
         ;; CARTESIAN: that is the form the rest of the machinery expects, and a
         ;; 1-ary product is an object nobody wants to meet.
         ;;
         ;; Adding this could not change any accepted formula: validate-wff!
         ;; requires a VNB-LAMBDA to have a DOMAIN (a domainless lambda does not
         ;; determine a function -- see the VNB-LAMBDA case below and
         ;; docs/lambda-domain.md), so every input matching this pattern was an
         ;; ERROR before, in every path.  A list only PARTLY typed still is.
         ((and (eq? (car mapped) 'VNB-LAMBDA)
               (= (length mapped) 3)
               (pair? (cadr mapped))
               (eq? (car (cadr mapped)) 'LIST)
               (all-typed-binder-specs? (cdr (cadr mapped))))
          (let* ((specs (cdr (cadr mapped)))
                 (vars  (map cadr  specs))
                 (doms  (map caddr specs))
                 (body  (caddr mapped)))
            (if (null? (cdr vars))
                `(VNB-LAMBDA ,(car vars) ,(car doms) ,body)
                `(VNB-LAMBDA (LIST ,@vars) (CARTESIAN ,@doms) ,body))))
         (else mapped))))))

;;; -----------------------------------------------------------------------
;;; validate-wff!: position-typed sanity check
;;;
;;; Walks an S-expression as if it were a wff, ensuring every position
;;; receives an appropriate sub-form.  Numbers in wff positions are
;;; rejected outright.  Term-forming operator heads (CHOICE, UNION, etc.)
;;; in wff position are rejected, and wff-forming heads (AND, FORALL, etc.)
;;; in term position are rejected.  Bare symbols in wff position are
;;; rejected (only TRUTH/FALSITY are valid bare-symbol wffs).  Compound
;;; forms (P arg ...) with an unknown symbol head are accepted as predicate
;;; / function applications.

;;; Term-forming heads: anything that, in wff position with these as the
;;; head, must be rejected ("term-forming operator in wff position" error).
(define *wff-term-form-heads*
  '(UNION INTERSECTION COMPLEMENT-IN CARTESIAN FUN INJECTION IMAGE SEP COMP BIG-UNION POWER
    LIST NTH MAKE-SET LENGTH CHOICE IOTA IF TUPLES SQN
    DOM RES PARTIAL-FUN
    apply-functoid VNB-LAMBDA
    succ_ORD ORD-SEGMENT SUP-ORD ESUP ESUM
    ;; The measure-theory arc (structure-library/extended-arith.scm,
    ;; measure.scm, integral.scm).  Only the two heads that no def-* introduces
    ;; belong here: ETIMES is extended multiplication on [0,+inf], pinned by
    ;; the axioms of extended-arith.scm exactly as EPLUS is by
    ;; extended-reals-pos.scm, and INTEGRAL is the [0,+inf]-valued integral,
    ;; characterised by the supports of integral.scm exactly as ESUM/ESUP are
    ;; by theirs.  Everything else in that arc is a def-functoid or a
    ;; def-predicate and registers itself.
    ETIMES INTEGRAL
    CARD PROD-ORD SUM SUM-SET PROD-SET RING-PROD RING-PROD-N ZERO-RING
    MATRIX SIZE MAT ENTRY INTERVAL MATOF MATMUL
    MATADD MATNEG MATSCALE ZEROMAT IDENTMAT MAT-RING MATUNIT
    ELEM-F ELEM-G ELEM-H SUBMAT BORDER MATACT UNITROW BLOCK SPAN SNOC-COL SNOC-ROW LASTCOEFF-SET
    + - * / recip abs conjugate succ exp sin cos
    ;; MAX, 2026-08-19 -- a TERM constructor (RR x RR -> RR), defined by cases in
    ;; number-systems.scm as `rr-max-def'.  Unregistered it parsed as an applied
    ;; FUNCTION VARIABLE -- `max(a,b)' meaning whatever the caller spelled it --
    ;; which is the silent-application trap, and there is no gate on a goal a
    ;; user types, only on one that gets installed.
    ;;
    ;; MIN, 2026-08-21 -- the same, and added at the same time as its laws.  It
    ;; was WANTED for a year and deliberately not added while it had no
    ;; definition: `*ineq-supply-wanted*' (ineq-supply.scm) recorded "no min
    ;; bounds in the tree ... and `min' has no registered head", and
    ;; `rr-min-pos' sidesteps a minimum with an existential witness.  That is
    ;; the right shape when a proof needs only the bounding property and the
    ;; wrong one when the minimum is a TERM the statement is about.
    max min
    real-part imag-part magnitude
    ;; Added 2026-08-04 by head-registry-sweep (audit.scm), which enumerates
    ;; every applied head in the library against the constant registry instead
    ;; of waiting for the next accident.  Each of these is a TERM constructor
    ;; that no def-* introduced, so free-vars reported the head itself as a free
    ;; variable of every fact about it: `bijection' in the whole inverse-bij
    ;; family and in well-ordering-principle, `pair' in the card-* axioms,
    ;; `difference'/`singleton' in is-field.  `/' was the same omission, found
    ;; the same morning and already fixed above.
    PAIR SINGLETON DIFFERENCE BIJECTION DELETE-AT EPLUS
    binplus bintimes binneg
    ;; CONS (structure-library/list-recursion.scm): the tuple constructor the
    ;; recursive characterization of LENGTH needs, which theory.scm:637 recorded
    ;; as pending.  A TERM former, so it belongs here rather than in a bare
    ;; register-constant! -- see the LIMIT-ORD note below for the difference.
    CONS))

(define *wff-only-heads*
  '(NOT AND OR IMPLIES IFF FORALL FORSOME = == IN <= SUBSET subset))

;;; Seed the constant-head registry (expressions.scm) with every kernel
;;; term-forming head, so subst-free / free-vars never mistake one for an
;;; applied function variable.  Structure accessors and defined functions
;;; are registered later, by def-structure and theory-add-definition!.
(for-each (lambda (h) (register-constant! h 'operator))
          *wff-term-form-heads*)

;;; LIMIT-ORD is a PREDICATE constant, not a term-forming one: `limit-ord-iff'
;;; (structure-library/ordinals.scm) states (IFF (LIMIT-ORD lambda) ...), the
;;; tfi3 rule builds (AND (LIMIT-ORD var) ...) as a wff, and def-by-ord-recursion
;;; guards its limit equation with it.  It nevertheless sat in
;;; *wff-term-form-heads* -- pasted in with succ_ORD / ORD-SEGMENT / SUP-ORD,
;;; which are terms -- so `make-wff' rejected EVERY goal mentioning it
;;; ("term-forming operator in wff position").  A statement about limit ordinals
;;; could be installed with `support' (which does not validate) but could never
;;; be the subject of a proof.  It still needs the CONSTANT registration below,
;;; so free-vars / subst-free do not mistake its head for a function variable.
(register-constant! 'LIMIT-ORD 'operator)

;;; Same treatment, same reason, for the three PREDICATE heads the sweep found
;;; unregistered (2026-08-04): the ordinal order relations and IS-FUN.  They must
;;; NOT go in *wff-term-form-heads* -- that is the LIMIT-ORD mistake above, and
;;; it would make make-wff reject every goal that mentions them -- but they are
;;; constants, and free-vars must not read `ord-le' as a function variable.
(for-each (lambda (h) (register-constant! h 'predicate))
          '(ord-le ord-lt is-fun))

;;; RESTVAR and SPLICE are the macete engine's variadic syntax (macetes.scm:42),
;;; not mathematical vocabulary: they occur in exactly four installed formulas
;;; (union-decompose, intersection-decompose and their -rev companions).  The
;;; engine recognises them by an eq? test long before any registry lookup, so
;;; registering them is inert there -- but it is what the walkers need, and it
;;; takes head-registry-sweep to zero, which is the only count a gate can use.
(for-each (lambda (h) (register-constant! h 'operator))
          '(RESTVAR SPLICE))

;;; Warn when a binder's variable has the name of a registered operator,
;;; defined function, or functoid: an application (v ...) in the body then
;;; refers to that constant, not the bound variable -- almost always a
;;; mistake.
;;;
;;; This is the WEAKER of two guards, and it no longer sets the policy.  It used
;;; to exempt ACCESSORS, on the grounds that binding an element variable `a`
;;; while `A` was a carrier accessor was a routine pattern.  That rationale died
;;; when the accessors were renamed (A -> CARR, X -> CARR/PTS, D -> DIST,
;;; ID -> IDEN): nothing routine binds `carr` or `mul` now, and a wff that does
;;; -- e.g. quantifying a ring open as (FORALL carr (FORALL add ... )) and then
;;; writing add(mul(q,b),r) -- is exactly the scope-blind hazard.  The live gate
;;; is warn-constant-binders! (macetes.scm), fired from make-wff via
;;; contexts.scm, which warns on EVERY registered-constant kind including
;;; accessors, and constant-binder-audit re-checks the whole theorem table at
;;; load.  Keep this one aligned with them rather than exempting anything.
(define (warn-binder-shadowing v)
  (let ((kind (constant-head? v)))
    ;; `primitive' is the kind `notation!' gives a head no def-* introduced --
    ;; the kernel relations =, ==, IN, <=, >, >=, SUBSET.  A binder named for one
    ;; of those is the same hazard as a binder named for an accessor.
    (if (memq kind '(operator defined-fn functoid accessor predicate primitive))
        (begin
          (display ";VNB warning: binder variable ")
          (display v)
          (display " has the name of a registered ") (display kind)
          (display " -- an application (") (display v)
          (display " ...) in its scope refers to that ") (display kind)
          (display ", not the bound variable.")
          (newline)))))

(define (validate-wff! expr)
  ;; term-syms: FREE symbols seen in term position.
  ;; bound-syms: every symbol that appears in any binder anywhere (for warning).
  ;; Within a binder body, the bound variable is checked locally and is
  ;; NOT recorded in the global free sets.
  (let ((term-syms  '())
        (bound-syms '()))

    (define (note-bound! s) (set! bound-syms (cons s bound-syms)))

    ;; bound-env: alist of (sym . 'term) bindings currently in scope.
    ;; All standard binders (FORALL, FORSOME, IOTA, SEP, lambda, lambdoid) bind
    ;; class variables, so the role is uniformly 'term.

    (define (walk-wff e bound-env)
      (cond
        ((number? e)
         (error "make-wff: number in wff position" e))
        ((symbol? e)
         (cond
           ((or (eq? e 'TRUTH) (eq? e 'FALSITY)) #t)
           ((assq e bound-env)
            (error "make-wff: bound class variable used in wff position" e))
           (else
            (error "make-wff: bare symbol in wff position (not a valid wff)" e))))
        ((pair? e)
         (case (car e)
           ((NOT)
            (or (= (length e) 2) (error "make-wff: NOT arity" e))
            (walk-wff (cadr e) bound-env))
           ((AND OR IMPLIES IFF)
            (or (= (length e) 3) (error "make-wff: connective arity" e))
            (walk-wff (cadr e) bound-env)
            (walk-wff (caddr e) bound-env))
           ((= == IN <= SUBSET subset)
            (or (= (length e) 3) (error "make-wff: predicate arity" e))
            (walk-term (cadr e) bound-env)
            (walk-term (caddr e) bound-env))
           ((FORALL FORSOME)
            (or (= (length e) 3) (error "make-wff: quantifier arity" e))
            (or (symbol? (cadr e)) (error "make-wff: bound variable not a symbol" e))
            (note-bound! (cadr e))
            (warn-binder-shadowing (cadr e))
            (walk-wff (caddr e) (cons (cons (cadr e) 'term) bound-env)))
           (else
            (cond
              ((memq (car e) *wff-term-form-heads*)
               (error "make-wff: term-forming operator in wff position" e))
              (else
               ;; Predicate application (P arg ...): args are terms.  A nullary
               ;; one is rejected for the reason a nullary TERM application is:
               ;; (P) prints as `P', so it cannot be told from the head itself.
               (or (>= (length e) 2)
                   (error "make-wff: predicate application with no arguments" e))
               (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))))))
        (else
         (error "make-wff: unrecognized expression in wff position" e))))

    (define (walk-term e bound-env)
      (cond
        ((number? e) #t)
        ((symbol? e)
         (cond
           ((or (eq? e 'TRUTH) (eq? e 'FALSITY))
            (error "make-wff: TRUTH/FALSITY in term position" e))
           ((assq e bound-env)
            ;; Bound class variable used in term position — fine.
            #t)
           (else (set! term-syms (cons e term-syms)))))
        ;; Functoid record: validate each domain and the body
        ((functoid? e)
         (let* ((bindings (functoid-bindings e))
                (bvars    (map car bindings))
                (env*     (fold-left (lambda (env bv)
                                       (note-bound! bv)
                                       (cons (cons bv 'term) env))
                                     bound-env bvars)))
           (for-each (lambda (b) (walk-term (cdr b) bound-env)) bindings)
           (walk-term (functoid-body e) env*)))
        ((pair? e)
         (case (car e)
           ((UNION INTERSECTION)
            ;; n-ary (>= 2 args) per manual ch-expressions: union/intersection
            ;; promised as n-ary constructors; the kernel rules
            ;; pi-union-intro!/pi-union-elim! and pi-intersection-intro!/-elim!
            ;; already handle arbitrary arity.  See REVIEW.md D-6.
            (or (>= (length e) 3) (error "make-wff: union/intersection needs >= 2 args" e))
            (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))
           ((COMPLEMENT-IN)
            ;; Relative complement A \ B; binary.  See REVIEW.md D-6.
            (or (= (length e) 3) (error "make-wff: COMPLEMENT-IN arity" e))
            (walk-term (cadr e) bound-env)
            (walk-term (caddr e) bound-env))
           ((FUN)
            (cond
              ((= (length e) 2)                          ; (FUN A) — domain only
               (walk-term (cadr e) bound-env))
              ((= (length e) 3)                          ; (FUN A B) — domain + codomain
               (walk-term (cadr e) bound-env)
               (walk-term (caddr e) bound-env))
              (else (error "make-wff: FUN takes 1 or 2 arguments" e))))
           ((CHOICE TUPLES MAKE-SET LENGTH)
            (or (= (length e) 2) (error "make-wff: unary term arity" e))
            (walk-term (cadr e) bound-env))
           ((POWER)
            (cond
              ((= (length e) 2) (walk-term (cadr e) bound-env))
              ((= (length e) 3)
               (walk-term (cadr e) bound-env)
               (walk-term (caddr e) bound-env))
              (else (error "make-wff: POWER arity (1 = power set, 2 = exponent)" e))))
           ;; LIST is the ONE nullary-legal term constructor: (LIST) is [], the
           ;; empty tuple, which `empty-in-tuples' and `length-of-empty' are
           ;; about.  Every other head needs at least one argument -- see the
           ;; nullary-application note in parser.scm.  This check is here as
           ;; well as there because `support' and `theory-add-axiom!' install a
           ;; raw S-expression that never meets the parser; install-grading runs
           ;; validate-wff! over all of them.
           ((LIST)
            (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))
           ((CARTESIAN)
            (or (>= (length e) 2)
                (error "make-wff: CARTESIAN with no arguments" e))
            (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))
           ((NTH)
            (or (= (length e) 3) (error "make-wff: NTH arity" e))
            (walk-term (cadr e) bound-env)
            (walk-term (caddr e) bound-env))
           ((SEP)
            (or (= (length e) 4) (error "make-wff: SEP arity" e))
            (or (symbol? (cadr e)) (error "make-wff: SEP bound var not symbol" e))
            (note-bound! (cadr e))
            (let ((env* (cons (cons (cadr e) 'term) bound-env)))
              (walk-term (caddr e) env*)
              (walk-wff  (cadddr e) env*)))
           ((BIG-UNION)
            ;; (BIG-UNION z A body) — body is a term (the set f(z)), unlike SEP.
            (or (= (length e) 4) (error "make-wff: BIG-UNION arity" e))
            (or (symbol? (cadr e)) (error "make-wff: BIG-UNION bound var not symbol" e))
            (note-bound! (cadr e))
            (let ((env* (cons (cons (cadr e) 'term) bound-env)))
              (walk-term (caddr e)  bound-env)   ; A in outer scope
              (walk-term (cadddr e) env*)))      ; body sees bound var
           ((COMP)
            (or (= (length e) 3) (error "make-wff: COMP arity" e))
            (or (symbol? (cadr e)) (error "make-wff: COMP bound var not symbol" e))
            (note-bound! (cadr e))
            (walk-wff (caddr e) (cons (cons (cadr e) 'term) bound-env)))
           ((IOTA)
            (or (= (length e) 3) (error "make-wff: IOTA arity" e))
            (or (symbol? (cadr e)) (error "make-wff: IOTA bound var not symbol" e))
            (note-bound! (cadr e))
            (walk-wff (caddr e) (cons (cons (cadr e) 'term) bound-env)))
           ((IF)
            ;; (IF p a b) — p is a wff (the condition), a/b are terms.
            ;; Non-binding: the branches see the same environment.
            (or (= (length e) 4) (error "make-wff: IF arity" e))
            (walk-wff  (cadr e)   bound-env)
            (walk-term (caddr e)  bound-env)
            (walk-term (cadddr e) bound-env))
           ((VNB-LAMBDA)
            ;; (VNB-LAMBDA bind-spec A body) -- A is the DOMAIN, and it is
            ;; required.  A lambda without one does not determine a function:
            ;; the kernel's lambda-type rule was free to certify one and the
            ;; same domainless term into FUN(A,B) for every A, which with
            ;; fun-domain-apply-def ("defined exactly on A") proves FALSITY.
            ;; See docs/lambda-domain.md.  A is walked in the OUTER env; only
            ;; the body sees the bound variables.
            (or (= (length e) 4)
                (error "make-wff: VNB-LAMBDA arity -- expected (VNB-LAMBDA bind-spec DOMAIN body)" e))
            (walk-term (caddr e) bound-env)
            (let ((bvars (vnb-lambda-bvars (cadr e))))
              (for-each (lambda (bv)
                          (or (symbol? bv)
                              (error "make-wff: VNB-LAMBDA bound var not symbol" e))
                          (note-bound! bv))
                        bvars)
              (let ((env* (fold-left (lambda (env bv) (cons (cons bv 'term) env))
                                     bound-env bvars)))
                (walk-term (cadddr e) env*))))
           ((apply-functoid)
            ;; (apply-functoid f arg ...) — f is a functoid or term; all are terms
            (or (>= (length e) 3) (error "make-wff: apply-functoid arity" e))
            (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))
           ((+ - * recip abs conjugate succ)
            (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))
           ;; Wff-forming heads in term position are an error.
           ((NOT AND OR IMPLIES IFF FORALL FORSOME = == IN <= SUBSET subset)
            (error "make-wff: wff-forming operator in term position" e))
           (else
            ;; Function application (f arg ...).  If the head is itself a
            ;; pair (e.g. ((MUL m) a b)) it is also a term and must be
            ;; walked, so any free symbol in head position is detected.
            (or (>= (length e) 2)
                (error "make-wff: application with no arguments" e))
            (let ((h (car e)))
              (when (pair? h) (walk-term h bound-env)))
            (for-each (lambda (a) (walk-term a bound-env)) (cdr e)))))
        (else
         (error "make-wff: unrecognized expression in term position" e))))

    ;; Top-level: must be a wff.
    (walk-wff expr '())

    ;; Warning: any name that is both bound somewhere and free elsewhere.
    (let ((warned '()))
      (for-each (lambda (s)
                  (when (and (memq s term-syms) (not (memq s warned)))
                    (display ";; warning: symbol ")
                    (write s)
                    (display " is both bound (in some binder) and free in this formula\n")
                    (set! warned (cons s warned))))
                bound-syms))))
