;;; zz-bezout-proof.scm -- BEZOUT on the integers, from the Euclidean-ring core.
;;;
;;; The lever is euclidean-ideal-has-generator (theorem-library/euclidean-ideal-
;;; generator-proof.scm): every ideal of a Euclidean ring has a generator inside
;;; it.  ZZ-RING is a Euclidean ring, so all that is needed to get Bezout is to
;;; exhibit { x*a + y*b } as an IDEAL -- and then the generator, being a member,
;;; IS a Bezout combination, while a and b, being members, are its multiples.
;;;
;;;   zz-bezout-set-is-ideal   IS-IDEAL(ZZ-RING, ZZ-BEZOUT-SET(a,b))
;;;   zz-bezout                exists d in ZZ-BEZOUT-SET(a,b). d | a and d | b
;;;
;;; NOT here yet: that d is a GREATEST common divisor (ZZ-IS-GCD), and Euclid's
;;; lemma.  Both reduce to one equational CHAIN --
;;;     c = c*1 = c*(x*a + y*b) = x*a*c + y*(b*c) = x*a*c + y*(a*k)
;;;       = a*(x*c + y*k)
;;; -- using the two hypotheses 1 = x*a + y*b and b*c = a*k.  No SINGLE tactic
;;; does that: `subst' rewrites only LITERAL occurrences in the goal and rewrites
;;; ALL of them (so introducing c*1 also hits the c inside the witness term), and
;;; `crs' decides ring identities but cannot consume a hypothesis.
;;;
;;; `calc' (calc.scm, load.scm:425) IS that step, and it closes this chain: five
;;; links, three by `crs' and two by an explicit (subst H) justification.
;;; Verified 2026-07-27.  So what is left here is the ORDINARY work of stating
;;; ZZ-IS-GCD / Euclid's lemma and doing the surrounding unfolding -- not a
;;; missing mechanism, as an earlier version of this comment claimed.
;;;
;;; HOW THE ACCESSORS GET OUT OF THE WAY.  IS-IDEAL is stated over an abstract
;;; ring: ((ADD s) u v), (ZERO s), (CARR s).  `surface-goal!' (transport.scm)
;;; rewrites those at ZZ-RING down to (+ u v), 0, ZZ, after which every closure
;;; condition is a ring identity over typed integer generators -- which is
;;; exactly what `crs' decides.  No abstract-ring normalizer is needed, and none
;;; exists; that is why this file is about ZZ and not about a general s.

;;; --- helpers -------------------------------------------------------------

;; Focus N only if it is STILL an open leaf; #f (and no move) otherwise.  Every
;; loop below walks a SNAPSHOT of leaves (`zb-conjuncts!', `dk-opened'), and
;; `in-rr' ends with an `ass-all' that grounds every assumption-closable node in
;; the graph -- so typing one conjunct `u in ZZ' closes its sibling `a in ZZ'
;; before the loop reaches it.  `dk-focus!' on that grounded node moves the
;; focus and records NOTHING (it is not in proof-open-leaves, driver-kit.scm:164),
;; and the `(ass)' `in-rr' then runs on it IS recorded -- a step the printed page
;; replays against whatever leaf the engine had chosen.  One such step shifted
;; every later `name-witness!' number by one and the page-audit gate reported
;; zz-bezout with three leaves open (2026-09-15).  Skip what is no longer a leaf.
(define (zb-focus-live! n)
  (and (not (sequent-node-grounded? n))
       (null? (sequent-node-in-arrows n))
       (begin (dk-focus! n) #t)))

;; split the focused goal's whole AND-tower; return the atomic leaves.
(define (zb-conjuncts!)
  (let loop ((todo (list (proof-state-focus *ps*))) (acc '()))
    (if (null? todo)
        (reverse acc)
        (begin
          (dk-focus! (car todo))
          (if (eq? (car (dk-goal)) 'AND)
              (loop (append (dk-opened (lambda () (di))) (cdr todo)) acc)
              (loop (cdr todo) (cons (car todo) acc)))))))

;; peel a guarded-FORALL / IMPLIES prefix, guarding on PROGRESS (`di' only WARNS
;; when it cannot decompose, so "while the head is FORALL" spins forever).
(define (zb-peel!)
  (let loop ((fuel 12))
    (let ((before (dk-goal)))
      (if (and (> fuel 0) (memq (car before) '(FORALL IMPLIES)))
          (begin (di)
                 (if (equal? (dk-goal) before)
                     (error "zb-peel!: di made no progress on" before)
                     (loop (- fuel 1))))))))

;; Unfold (IN v (ZZ-BEZOUT-SET a b)) in the CONTEXT, skolemizing both
;; coefficients, and return them as (list x y); the equation
;; (= v (+ (* x a) (* y b))) is left in context.  The coefficient names are read
;; off that EQUATION, never guessed -- they are engine-chosen eigenvariables.
;;; The operation a closure goal is about.  A slot application
;;; ((VNB-LAMBDA (LIST x_ y_) (CARTESIAN ZZ ZZ) (+ x_ y_)) u v) is about `+';
;;; a bare (+ u v) is too.  Reading the head off the lambda BODY lets the
;;; dispatch below run before anything has been rewritten.
(define (zb--slot-op tm)
  (if (and (pair? tm) (pair? (car tm)) (eq? (caar tm) 'VNB-LAMBDA))
      (car (cadddr (car tm)))
      (car tm)))

(define (zb-open! v)
  (let loop ((parts (dk-split!
                      (dk-landed-1
                        (lambda () (mac-h 'zz-bezout-set-membership
                                          `(IN ,v (ZZ-BEZOUT-SET a b))))))))
    (let ((ex (any-pred (dk-head? 'FORSOME) parts)))
      (if ex
          (loop (dk-split! (dk-landed-1 (lambda () (ai ex)))))
          (let ((eq (or (any-pred (dk-head? '=) parts)
                        (error "zb-open!: no Bezout equation among" parts))))
            (list (cadr (cadr (caddr eq)))        ; x from (* x a)
                  (cadr (caddr (caddr eq)))))))))  ; y from (* y b)

;; Prove a goal (IN <term> (ZZ-BEZOUT-SET a b)) by exhibiting the coefficients
;; XT, YT and rewriting each named member equation into the goal before handing
;; the residue to `crs'.  MEMBERS is the list of members whose equations must be
;; substituted away.
(define (zb-witness! xt yt members)
  (mac 'zz-bezout-set-membership)
  (for-each
    (lambda (leaf)
     (when (zb-focus-live! leaf)
      (let ((g (dk-goal)))
        (cond ((eq? (car g) 'IN) (zb-type!))
              ((eq? (car g) 'FORSOME)
               (ew xt)
               (for-each
                 (lambda (l2)
                  (when (zb-focus-live! l2)
                   (let ((g2 (dk-goal)))
                     (cond ((eq? (car g2) 'IN) (zb-type!))
                           (else
                            (ew yt)
                            (for-each
                              (lambda (l3)
                               (when (zb-focus-live! l3)
                                (if (eq? (car (dk-goal)) 'IN)
                                    (zb-type!)
                                    (begin
                                      (for-each (lambda (m) (subst (zb-eq-of m))) members)
                                      (crs)))))
                              (dk-opened (lambda () (di)))))))))
                 (dk-opened (lambda () (di)))))
              (else (error "zb-witness!: unexpected conjunct" g))))))
    (dk-opened (lambda () (di)))))

;; close a typing goal (IN <term> ZZ): `in-rr' types an arithmetic APPLICATION
;; structurally, but a bare numeral is not an application -- that is `arith'.
(define (zb-type!)
  (if (number? (cadr (dk-goal))) (arith) (in-rr)))

;; the context equation defining member M as a Bezout combination
(define (zb-eq-of m)
  (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) '=) (equal? (cadr f) m)))
                (dk-asms))
      (error "zb-eq-of: no Bezout equation for" m)))

;;; --- (1) the Bezout set is an ideal --------------------------------------

(sp (make-wff (forall-guarded '(a b) '((IN a ZZ) (IN b ZZ))
                '(IS-IDEAL ZZ-RING (ZZ-BEZOUT-SET a b)))))
(zb-peel!)
(mac 'is-ideal)
(quietly (lambda () (surface-goal! 'ZZ-RING)))

(for-each
  (lambda (leaf)
   (when (zb-focus-live! leaf)
    (let ((g (dk-goal)))
      (cond
        ;; ZZ-RING is a commutative ring -- an instance axiom.
        ((eq? (car g) 'IS-COMMUTATIVE-RING)
         (ta 'zz-is-commutative-ring) (ass))
        ;; the set sits inside ZZ, because it is a SEP over ZZ.
        ((eq? (car g) 'SUBSET)
         (mac 'subset-def)
         (di)
         (dk-split! (dk-landed-1 (lambda () (mac-h 'zz-bezout-set-membership
                                                   '(IN x (ZZ-BEZOUT-SET a b))))))
         (ass))
        ;; 0 = 0*a + 0*b.
        ((and (eq? (car g) 'IN) (eqv? (cadr g) 0))
         (zb-witness! 0 0 '()))
        ;; closure: the shape of the peeled goal names which one it is.
        (else
         (zb-peel!)
         ;; ZZ-RING's ADD/MUL/NEG slots hold tupled VNB-LAMBDAs since 2026-08-29
         ;; (the shared constant `binplus' was the inconsistency -- see
         ;; numeric-instances.scm), so the peeled goal arrives as a lambda
         ;; APPLICATION rather than as `u + v'.
         ;;
         ;; The operation is read off the lambda's BODY rather than rewritten
         ;; away first, and the order matters: the read-off macete is guarded on
         ;; the arguments being typed in ZZ, and here they are typed in
         ;; ZZ-BEZOUT-SET(a,b) instead.  `zb-open!' is what lands `u in ZZ' (it
         ;; unfolds zz-bezout-set-membership, whose first conjunct is exactly
         ;; that), so the saturation has to come AFTER the opens, not before.
         (let* ((tm   (cadr (dk-goal)))
                (op   (zb--slot-op tm))
                (args (cdr tm))
                (sat  (lambda ()
                        (dk-saturate-slot-ops!
                         'ZZ '((+ . zz-add-closed)
                               (* . zz-mul-closed)
                               (- . zz-neg-closed))))))
           (case op
             ((+)                              ; u + v
              (let* ((u (car args)) (v (cadr args))
                     (cu (zb-open! u)) (cv (zb-open! v)))
                (sat)
                (zb-witness! (list '+ (car cu) (car cv))
                             (list '+ (cadr cu) (cadr cv))
                             (list u v))))
             ((-)                              ; -u
              (let* ((u (car args)) (cu (zb-open! u)))
                (sat)
                (zb-witness! (list '- (car cu)) (list '- (cadr cu)) (list u))))
             ((*)                              ; r * u
              (let* ((r (car args)) (u (cadr args)) (cu (zb-open! u)))
                (sat)
                (zb-witness! (list '* r (car cu)) (list '* r (cadr cu)) (list u))))
             (else (error "zz-bezout: unexpected closure goal" (dk-goal))))))))))
  (zb-conjuncts!))
(for-each (lambda (n)
            (display ";; ZB-OPEN-LEAF: ")
            (display (expression->string (wff-formula (sequent-node-assertion n))))
            (newline))
          (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-open-goals *ps*)))
(qed 'zz-bezout-set-is-ideal)

;;; --- (2) Bezout ----------------------------------------------------------
;;; A generator of that ideal is a common divisor of a and b which is itself a
;;; combination x*a + y*b.  Both halves come straight out of "generator": it is a
;;; MEMBER of the set (hence a combination), and a and b are members (take the
;;; coefficient pairs (1,0) and (0,1)), hence multiples of it.

;; close a goal (ZZ-DIVIDES d v), given (= v (* r d)) in the context.
(define (zb-divides! r v)
  (mac 'zz-divides)
  (for-each
    (lambda (leaf)
     (when (zb-focus-live! leaf)
      (let ((g (dk-goal)))
        (cond ((eq? (car g) 'IN) (zb-type!))
              ((eq? (car g) 'FORSOME)
               (ew r)
               (for-each (lambda (l2)
                          (when (zb-focus-live! l2)
                           (if (eq? (car (dk-goal)) 'IN)
                               (zb-type!)
                               (begin
                                 (subst (zb-eq-of v))
                                 ;; ZZ-RING's MUL slot is a tupled VNB-LAMBDA
                                 ;; since 2026-08-29, so the substituted goal can
                                 ;; still hold slot APPLICATIONS; crs decides ring
                                 ;; identities over the SURFACE operators, not
                                 ;; over lambda applications.
                                 (dk-saturate-slot-ops!
                                  'ZZ '((+ . zz-add-closed)
                                        (* . zz-mul-closed)
                                        (- . zz-neg-closed)))
                                 (crs)))))
                         (dk-opened (lambda () (di)))))
              (else (error "zb-divides!: unexpected conjunct" g))))))
    (zb-conjuncts!)))

(sp (make-wff (forall-guarded '(a b) '((IN a ZZ) (IN b ZZ))
   '(FORSOME d (AND (IN d (ZZ-BEZOUT-SET a b))
                    (AND (ZZ-DIVIDES d a) (ZZ-DIVIDES d b)))))))
(zb-peel!)

;; a and b are themselves combinations -- coefficients (1,0) and (0,1).
(have! '(IN a (ZZ-BEZOUT-SET a b)) (lambda () (zb-witness! 1 0 '())))
(have! '(IN b (ZZ-BEZOUT-SET a b)) (lambda () (zb-witness! 0 1 '())))

;; the ideal has a generator (euclidean-ideal-has-generator at ZZ-RING).
(ta 'zz-is-euclidean-ring)
(fact 'zz-bezout-set-is-ideal 'a 'b)
;; NOT one dk-landed-1 around both steps: `fact' lands its WHOLE instantiation
;; chain (the theorem, each partly-peeled form, the detached result), so the
;; diff sees five assumptions, not one.  dk-fact! takes the deepest; `ai' then
;; skolemizes exactly that one.
(define zb-exists
  (dk-fact! 'euclidean-ideal-has-generator 'ZZ-RING '(ZZ-BEZOUT-SET a b)))
(define zb-gen (dk-split! (dk-landed-1 (lambda () (ai zb-exists)))))
(define zb-d   (cadr (car (filter (dk-head? 'IN) zb-gen))))     ; the generator
(define zb-div (car (filter (dk-head? 'FORALL) zb-gen)))        ; every member is a multiple

;; From "v is a multiple of d" in the PRINCIPAL-IDEAL language to (= v (* r d))
;; in the ZZ surface language, and thence to ZZ-DIVIDES.  tr--surface-assumption!
;; (transport.scm) is the assumption-side twin of surface-goal!: it drives the
;; instance's own accessor macetes with mac-h, so the kernel redoes each rewrite.
(define (zb-multiple! v)
  (let* ((mem  (dk-deepest (lambda () (inst+ zb-div v))))
         (unf  (dk-landed-1 (lambda () (mac-h 'principal-ideal-membership mem))))
         (surf (tr--surface-assumption! 'ZZ-RING unf))
         (parts (dk-split! surf))
         (ex   (or (any-pred (dk-head? 'FORSOME) parts)
                   (error "zb-multiple!: no witness clause" parts)))
         (inner (dk-split! (dk-landed-1 (lambda () (ai ex)))))
         (eq   (or (any-pred (dk-head? '=) inner)
                   (error "zb-multiple!: no multiple equation" inner))))
    (cadr (caddr eq))))                       ; the cofactor r from (= v (* r d))

;; The generator is an integer -- it is a member of a SEP over ZZ.  Needed by
;; `crs' below, which certifies each generator of a ring identity from context;
;; without it the commutativity step (* r d) = (* d r) does not close.  mac-h
;; REPLACES, so the unfold happens inside the side branch only and the main
;; branch keeps (IN d (ZZ-BEZOUT-SET a b)).
(have! `(IN ,zb-d ZZ)
       (lambda ()
         (dk-split! (dk-landed-1
                      (lambda () (mac-h 'zz-bezout-set-membership
                                        `(IN ,zb-d (ZZ-BEZOUT-SET a b))))))
         (ass)))

(ew zb-d)
(for-each
  (lambda (leaf)
   (when (zb-focus-live! leaf)
    (let ((g (dk-goal)))
      (if (eq? (car g) 'IN)
          (ass)                                ; d is a member: that is what it is
          (for-each (lambda (l2)
                     (when (zb-focus-live! l2)
                      (let* ((v (caddr (dk-goal)))        ; (ZZ-DIVIDES d v)
                             (r (zb-multiple! v)))
                        (zb-divides! r v))))
                    (zb-conjuncts!))))))
  (dk-opened (lambda () (di))))
(qed 'zz-bezout)
