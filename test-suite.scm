;;; test-suite.scm -- VNB system regression and demonstration tests
;;;
;;; Run with:  (load "test-suite.scm")  (after loading load.scm)
;;; or:        mit-scheme --quiet --load test-suite.scm
;;;
;;; Organised by feature area.  Each section is self-contained and
;;; serves as a worked example for the manual appendix.

(load "load.scm")

;;; -----------------------------------------------------------------------
;;; Helpers

(define *pass-count* 0)
(define *fail-count* 0)

(define (check label thunk expected)
  (let ((got (thunk)))
    (if (equal? got expected)
        (begin (set! *pass-count* (+ *pass-count* 1))
               (display "  PASS  ") (display label) (newline))
        (begin (set! *fail-count* (+ *fail-count* 1))
               (display "  FAIL  ") (display label)
               (display " -- expected ") (write expected)
               (display " got ") (write got) (newline)))))

(define (check-true  label thunk) (check label thunk #t))
(define (check-false label thunk) (check label thunk #f))

(define (check-error label thunk)
  ;; Pass when thunk returns a <vnb-error> (i.e. input was rejected).
  (let ((result (thunk)))
    (if (vnb-error? result)
        (begin (set! *pass-count* (+ *pass-count* 1))
               (display "  PASS  ") (display label) (newline))
        (begin (set! *fail-count* (+ *fail-count* 1))
               (display "  FAIL  ") (display label)
               (display " -- expected error, got ") (write result) (newline)))))

(define (check-proof label thunk)
  ;; Pass when thunk completes without raising.
  (call-with-current-continuation
    (lambda (k)
      (with-exception-handler
        (lambda (e)
          (set! *fail-count* (+ *fail-count* 1))
          (display "  FAIL  ") (display label)
          (display " -- exception: ")
          (display (condition/report-string e)) (newline)
          (k #f))
        thunk)
      (set! *pass-count* (+ *pass-count* 1))
      (display "  PASS  ") (display label) (newline))))

;;; wff-str: extract the display string from a wff (strips surrounding quotes).
(define (wff-str w)
  (let ((s (wff->string w)))
    (substring s 1 (- (string-length s) 1))))

;;; macete-str: apply a named macete to a formula given as a string.
;;; Returns the resulting display string, or #f if the macete doesn't fire.
(define (macete-str name str)
  (let ((r (apply-macete name (make-wff-from-string str))))
    (and r (wff-str r))))

;;; roundtrip: parse a formula string and print it back.
(define (roundtrip str)
  (let ((w (make-wff-from-string str)))
    (if (vnb-error? w) #f (wff-str w))))

;;; -----------------------------------------------------------------------
;;; 1. Ground arithmetic evaluation
;;;
;;; Arithmetic facts decided by the built-in evaluator without the
;;; proof kernel.

(display "\n=== 1. Ground arithmetic ===\n")

(check-true  "0 in NN"        (lambda () (arith-membership-check 0   'NN)))
(check-true  "1 in NN"        (lambda () (arith-membership-check 1   'NN)))
(check-true  "100 in NN"      (lambda () (arith-membership-check 100 'NN)))
(check-false "-1 not in NN"   (lambda () (arith-membership-check -1  'NN)))
(check-false "1/2 not in NN"  (lambda () (arith-membership-check 1/2 'NN)))

(check-true  "0 in ZZ"        (lambda () (arith-membership-check 0   'ZZ)))
(check-true  "-3 in ZZ"       (lambda () (arith-membership-check -3  'ZZ)))
(check-false "1/2 not in ZZ"  (lambda () (arith-membership-check 1/2 'ZZ)))

(check-true  "1/3 in QQ"      (lambda () (arith-membership-check 1/3 'QQ)))
(check-false "1/3 not in ZZ"  (lambda () (arith-membership-check 1/3 'ZZ)))

(check-true  "0 in RR"        (lambda () (arith-membership-check 0   'RR)))
(check-true  "0 in CC"        (lambda () (arith-membership-check 0   'CC)))
(check-true  "-5 in CC"       (lambda () (arith-membership-check -5  'CC)))

(check "2 + 3 = 5"            (lambda () (arith-eval-term '(+ 2 3)))      5)
(check "3 * 4 = 12"           (lambda () (arith-eval-term '(* 3 4)))      12)
(check "10 + (-3) = 7"        (lambda () (arith-eval-term '(+ 10 (- 3))))  7)
(check "succ(0) = 1"          (lambda () (arith-eval-term '(succ 0)))     1)
(check "succ(4) = 5"          (lambda () (arith-eval-term '(succ 4)))     5)
(check "succ_ORD(0) = 1"      (lambda () (arith-eval-term '(succ_ORD 0))) 1)
(check "succ_ORD(succ(2))=4"  (lambda () (arith-eval-term '(succ_ORD (succ 2)))) 4)
(check "power(2,0) = 1"       (lambda () (arith-eval-term '(power 2 0)))  1)
(check "power(2,3) = 8"       (lambda () (arith-eval-term '(power 2 3)))  8)
(check "power(3,4) = 81"      (lambda () (arith-eval-term '(power 3 4)))  81)

;; n-ary kiddie arithmetic: the parser emits flat (+ a b c ...) etc.
(check "2+3+5 = 10 (n-ary +)"  (lambda () (arith-eval-term '(+ 2 3 5)))     10)
(check "1+2+3+4+5 = 15"        (lambda () (arith-eval-term '(+ 1 2 3 4 5))) 15)
(check "2*3*5 = 30 (n-ary *)"  (lambda () (arith-eval-term '(* 2 3 5)))     30)
(check "10-4 = 6 (binary -)"   (lambda () (arith-eval-term '(- 10 4)))       6)
(check "10-4-3 = 3 (chained -)" (lambda () (arith-eval-term '(- 10 4 3)))     3)
(check "-(7) = -7 (unary - kept)" (lambda () (arith-eval-term '(- 7)))       -7)
(check "2+3*5 = 17 (precedence)" (lambda () (arith-eval-term '(+ 2 (* 3 5)))) 17)

(check-true  "= 2+3 5"        (lambda () (arith-eval-formula '(= (+ 2 3) 5))))
(check-false "= 2+3 6"        (lambda () (arith-eval-formula '(= (+ 2 3) 6))))
(check-true  "<= 0 5"         (lambda () (arith-eval-formula '(<= 0 5))))
(check-false "<= 5 0"         (lambda () (arith-eval-formula '(<= 5 0))))
(check-true  "IN 0 NN"        (lambda () (arith-eval-formula '(IN 0 NN))))
(check-false "IN -1 NN"       (lambda () (arith-eval-formula '(IN -1 NN))))
(check-true  "power(2,0)=1"   (lambda () (arith-eval-formula '(= (power 2 0) 1))))

(check "simplify term: power(2,10)"
       (lambda () (arith-simplify-term '(power 2 10)))
       1024)
(check "simplify term: +(power(2,10),x) partial"
       (lambda () (arith-simplify-term '(+ (power 2 10) x)))
       '(+ 1024 x))
(check "simplify term: number unchanged"
       (lambda () (arith-simplify-term 5))
       5)
(check "simplify formula: = power(2,10) x"
       (lambda () (arith-simplify-formula '(= (power 2 10) x)))
       '(= 1024 x))
(check "simplify formula: IN power(2,10) NN"
       (lambda () (arith-simplify-formula '(IN (power 2 10) NN)))
       '(IN 1024 NN))
(check "simplify formula: AND with ground subterm"
       (lambda () (arith-simplify-formula '(AND (IN (power 2 10) NN) (= (power 2 10) x))))
       '(AND (IN 1024 NN) (= 1024 x)))
(check "simplify formula: no-op on free variable"
       (lambda () (arith-simplify-formula '(= x y)))
       '(= x y))

(check "forsome-witness: 2^10 in NN"
       (lambda () (arith-forsome-witness
                   '(FORSOME x (AND (IN x NN) (= (power 2 10) x)))))
       1024)
(check "forsome-witness: symmetric = x EXPR"
       (lambda () (arith-forsome-witness
                   '(FORSOME x (AND (IN x NN) (= x (power 2 10))))))
       1024)
(check-false "forsome-witness: EXPR not ground"
             (lambda () (arith-forsome-witness
                         '(FORSOME x (AND (IN x NN) (= (+ y 1) x))))))
(check-false "forsome-witness: value not in class"
             (lambda () (arith-forsome-witness
                         '(FORSOME x (AND (IN x NN) (= -1 x))))))

;;; -----------------------------------------------------------------------
;;; 2. Axioms installed
;;;
;;; Every installed axiom is simultaneously a theorem (available for
;;; backchaining) and a macete entry.

(display "\n=== 2. Axioms installed ===\n")

(define (axiom-present? name)
  (if (hash-table-ref/default *theorem-table* name #f) #t #f))

(for-each (lambda (name)
            (check-true (symbol->string name)
                        (lambda () (axiom-present? name))))
  '(;; set theory
    membership-implies-sethood extensionality
    empty-set-is-set empty-set-has-no-members
    pairing pairing-membership
    power-set power-set-membership
    union-set-closure intersection-set-closure
    fun-set-iff fun-elements-are-sets
    fun-domain-elements-are-sets fun-domain-apply-def
    fun-domain-extensionality fun-codomain-iff
    cartesian-set-iff tuples-sethood
    make-set-membership make-set-sethood make-set-empty
    length-of-empty length-in-nn nth-in-range
    ;; NN
    nn-is-set nn-zero-in nn-succ-closed
    nn-add-closed nn-mul-closed
    nn-add-comm nn-mul-comm
    nn-add-assoc nn-mul-assoc
    nn-distributive nn-one-mul nn-add-zero
    nn-subset-zz
    ;; power
    power-typing-nonneg power-zero power-succ power-neg
    ;; ZZ, QQ, RR, CC
    zz-is-set zz-zero-in zz-one-in
    qq-is-set rr-is-set cc-is-set
    nn-subset-zz zz-subset-qq qq-subset-rr rr-subset-cc
    ;; ordinals
    burali-forti nn-subset-ord ord-succ-in transfinite-induction))

;;; ZZplus must be completely absent
(check-false "zzplus-is-set absent"
             (lambda () (axiom-present? 'zzplus-is-set)))

;;; -----------------------------------------------------------------------
;;; 3. Parser: string syntax
;;;
;;; make-wff-from-string accepts the surface syntax; wff-str recovers
;;; the canonical printed form.

(display "\n=== 3. Parser ===\n")

;;; Basic predicates
(check "n in nn"           (lambda () (roundtrip "n in nn"))           "n in nn")
(check "n = m"             (lambda () (roundtrip "n = m"))             "n = m")
(check "n <= m"            (lambda () (roundtrip "n <= m"))            "n <= m")
(check "truth"             (lambda () (roundtrip "truth"))             "truth")
(check "falsity"           (lambda () (roundtrip "falsity"))           "falsity")

;;; Arithmetic in formulas
(check "n + m = m + n"     (lambda () (roundtrip "n + m = m + n"))     "n + m = m + n")
(check "n * m = m * n"     (lambda () (roundtrip "n * m = m * n"))     "n * m = m * n")

;;; Connectives
(check "A and B"           (lambda () (roundtrip "n in nn and m in nn"))
                           "n in nn and m in nn")
(check "A or B"            (lambda () (roundtrip "n in nn or m in nn"))
                           "n in nn or m in nn")
(check "A implies B"       (lambda () (roundtrip "n in nn implies n in zz"))
                           "n in nn implies n in zz")
(check "not A"             (lambda () (roundtrip "not(n in nn)"))
                           "not(n in nn)")

;;; Quantifiers (parse accepts; print may vary — just check non-error)
(check-true "forall bare"
            (lambda () (wff? (make-wff-from-string "forall([x], x in nn implies x in zz)"))))
(check-true "forall restricted"
            (lambda () (wff? (make-wff-from-string "forall([x in nn], x in zz)"))))
(check-true "forsome"
            (lambda () (wff? (make-wff-from-string "forsome([x in nn], x = 0)"))))
(check-true "forall multi-var"
            (lambda () (wff? (make-wff-from-string "forall([x in nn, y in nn], x + y = y + x)"))))

;;; Functional notation for terms
(check-true "succ(n)"     (lambda () (wff? (make-wff-from-string "succ(0) in nn"))))
(check-true "power(x,n)"  (lambda () (wff? (make-wff-from-string "power(2, 3) = 8"))))
(check-true "nth(1,t)"    (lambda () (wff? (make-wff-from-string "nth(1, t) in a"))))

;;; Set/brace notation
(check-true "set literal {a,b}"
            (lambda () (wff? (make-wff-from-string "x in {a, b}"))))
(check-true "sep {x in A: p}"
            (lambda () (wff? (make-wff-from-string "z in {x in a | x in nn}"))))

;;; -----------------------------------------------------------------------
;;; 4. Wff validation
;;;
;;; The validator rejects formulas that are syntactically malformed.
;;; vnb-guard returns a <vnb-error> value on failure.

(display "\n=== 4. Wff validation ===\n")

;;; Valid formulas that should be accepted
(check-true "TRUTH accepted"     (lambda () (wff? (make-wff-from-string "truth"))))
(check-true "IN accepted"        (lambda () (wff? (make-wff-from-string "n in nn"))))
(check-true "IMPLIES accepted"   (lambda () (wff? (make-wff-from-string "n in nn implies n in zz"))))
(check-true "AND accepted"       (lambda () (wff? (make-wff-from-string "n in nn and m in nn"))))
(check-true "OR accepted"        (lambda () (wff? (make-wff-from-string "n in nn or m in nn"))))
(check-true "IFF accepted"       (lambda () (wff? (make-wff-from-string "n = m iff m = n"))))
(check-true "NOT accepted"       (lambda () (wff? (make-wff-from-string "not(n in nn)"))))
(check-true "FORALL accepted"    (lambda () (wff? (make-wff-from-string "forall([x in nn], x in zz)"))))
(check-true "FORSOME accepted"   (lambda () (wff? (make-wff-from-string "forsome([x in nn], x = 0)"))))

;;; Invalid: bare number in wff position
(check-error "bare number rejected"
             (lambda () (make-wff-from-string "1")))

;;; Invalid: term-forming head in wff position
(check-error "union in wff position rejected"
             (lambda () (make-wff '(UNION x y))))

;;; -----------------------------------------------------------------------
;;; 5. apply-macete: local context (Monk 1988)
;;;
;;; apply-macete takes a wff and returns a rewritten wff (or #f).
;;; Conditions extracted from the theorem must be satisfied by the
;;; local context that accumulates as the rewriter descends.

(display "\n=== 5. apply-macete: local context ===\n")

;;; 5a. Unconditional IFF macete (no conditions — fires anywhere)
(install-theorem! 'eq-symm
  (make-wff-from-string "forall([x, y], x = y iff y = x)"))

(check "eq-symm: 3+5=8 -> 8=3+5"
       (lambda () (macete-str 'eq-symm "3 + 5 = 8"))
       "8 = 3 + 5")

(check "eq-symm: n=m implies truth -> m=n implies truth"
       (lambda () (macete-str 'eq-symm "n = m implies truth"))
       "m = n implies truth")

(check "eq-symm: no match on n in nn"
       (lambda () (macete-str 'eq-symm "n in nn"))
       #f)

(check "eq-symm: both sides of = rewritten"
       (lambda () (macete-str 'eq-symm "n = m and m = k"))
       "m = n and k = m")

;;; Unconditional IFF macete: and-comm
(install-theorem! 'and-comm-iff
  '(FORALL p (FORALL q (IFF (AND p q) (AND q p)))))

(check "and-comm: (A and B) -> (B and A)"
       (lambda () (macete-str 'and-comm-iff "n in nn and m in nn"))
       "m in nn and n in nn")

(check "and-comm: fires inside IMPLIES antecedent"
       (lambda () (macete-str 'and-comm-iff "n in nn and m in nn implies truth"))
       "m in nn and n in nn implies truth")

(check "and-comm: no AND to rewrite"
       (lambda () (macete-str 'and-comm-iff "n in nn"))
       #f)

;;; 5b. Conditional macetes — require local context
;;;
;;; nn-add-comm: forall([a,b in NN], a+b = b+a)
;;; Without context the rewrite must NOT fire.

(check "nn-add-comm: no fire on bare sum"
       (lambda () (macete-str 'nn-add-comm "n + m = 0"))
       #f)

;;; Inside IMPLIES: antecedent (AND (IN n NN) (IN m NN)) is flattened
;;; into local context when entering the consequent.
(check "nn-add-comm: fires inside IMPLIES consequent"
       (lambda () (macete-str 'nn-add-comm
                              "n in nn and m in nn implies n + m = m + n"))
       "n in nn and m in nn implies m + n = n + m")

;;; nn-add-zero: forall([n in NN], n + 0 = n)
(check "nn-add-zero: no fire without context"
       (lambda () (macete-str 'nn-add-zero "n + 0 = 5"))
       #f)

(check "nn-add-zero: fires inside IMPLIES consequent"
       (lambda () (macete-str 'nn-add-zero "n in nn implies n + 0 = 5"))
       "n in nn implies n = 5")

;;; AND: entering the right conjunct adds the left conjunct to context.
(check "nn-add-zero: fires in right conjunct of AND"
       (lambda () (macete-str 'nn-add-zero "k in nn and k + 0 = 5"))
       "k in nn and k = 5")

;;; Wrong order: condition follows the expression — no context available.
(check "nn-add-zero: no fire when condition is right conjunct"
       (lambda () (macete-str 'nn-add-zero "k + 0 = 5 and k in nn"))
       #f)

;;; OR: entering the right disjunct adds (NOT left-disjunct) to context.
;;; (nn-add-zero condition (IN n NN) is not (NOT something), so still no fire)
(check "nn-add-zero: no fire in right disjunct of OR"
       (lambda () (macete-str 'nn-add-zero "truth or n + 0 = 5"))
       #f)

;;; nn-add-closed: forall([a,b in NN], a+b in NN) — rewrites to TRUTH
(check "nn-add-closed: fires inside IMPLIES, rewrites to truth"
       (lambda () (macete-str 'nn-add-closed
                              "n in nn and m in nn implies n + m in nn"))
       "n in nn and m in nn implies truth")

(check "nn-add-closed: no fire without context"
       (lambda () (macete-str 'nn-add-closed "n + m in nn"))
       #f)

;;; power-zero: forall([x in CC], power(x,0) = 1)
(check "power-zero: fires inside IMPLIES"
       (lambda () (macete-str 'power-zero "z in cc implies power(z, 0) = w"))
       "z in cc implies 1 = w")

(check "power-zero: no fire without context"
       (lambda () (macete-str 'power-zero "power(z, 0) = 1"))
       #f)

;;; power-succ: forall([x in CC, n in NN], power(x,succ(n)) = x*power(x,n))
(check "power-succ: fires inside IMPLIES with two conditions"
       (lambda () (macete-str 'power-succ
                              "z in cc and k in nn implies power(z, succ(k)) = w"))
       "z in cc and k in nn implies z * z ^ k = w")

;;; apply-macete returns a wff object
(check-true "apply-macete returns wff"
            (lambda () (wff? (apply-macete 'eq-symm
                                           (make-wff-from-string "n = m")))))

;;; apply-macete returns #f on no match
(check-false "apply-macete returns #f on no match"
             (lambda () (apply-macete 'eq-symm
                                      (make-wff-from-string "n in nn"))))

;;; 5h. REVIEW.md S-5 — lc-drop-shadowed: ctx assumptions referencing a
;;; binder's variable must be dropped before descending under the binder.
(check "lc-drop-shadowed: drops asm mentioning the bvar"
  (lambda () (lc-drop-shadowed '(x) '((= x 0) (IN y NN))))
  '((IN y NN)))

(check "lc-drop-shadowed: keeps all when no shadowing"
  (lambda () (lc-drop-shadowed '(z) '((= x 0) (IN y NN))))
  '((= x 0) (IN y NN)))

(check "lc-drop-shadowed: drops on any of multiple bvars"
  (lambda () (lc-drop-shadowed '(p q) '((IN p A) (IN y NN) (= q 0))))
  '((IN y NN)))

;;; The audit's exact macete witness: a conditional rewrite that USED to
;;; fire spuriously under a FORALL that shadowed the condition's variable.
;;; Without the lc-drop-shadowed fix, this would rewrite
;;;   IMPLIES (= x 0) (FORALL x (= (foo x) (g x)))
;;; to (IMPLIES (= x 0) (FORALL x (= x (g x)))) -- using the OUTER (= x 0)
;;; to discharge a condition that semantically refers to the inner x.
(install-theorem! 'foo-zero-cond
  '(FORALL y (IMPLIES (= y 0) (= (foo y) y))))

(check "S-5 witness: macete must NOT fire under shadowing FORALL"
  (lambda ()
    (let* ((wif (make-wff '(IMPLIES (= x 0)
                              (FORALL x (= (foo x) (g x))))))
           (r   (apply-macete 'foo-zero-cond wif)))
      ;; Should be #f -- no rewrite under the shadowing FORALL x.
      ;; (Before fix: would have produced (IMPLIES (= x 0) (FORALL x (= x (g x)))))
      r))
  #f)

(check "S-5 control: same macete still fires when NOT shadowed"
  (lambda ()
    (let* ((wif (make-wff '(IMPLIES (= z 0) (= (foo z) (g z)))))
           (r   (apply-macete 'foo-zero-cond wif)))
      (and r (wff-formula r))))
  '(IMPLIES (= z 0) (= z (g z))))

;;; -----------------------------------------------------------------------
;;; 6. Proof commands
;;;
;;; Each sub-test proves a simple theorem using one or two rules.
;;; check-proof verifies completion without exception.

(display "\n=== 6. Proof commands ===\n")

;;; 6a. Arithmetic (arith) — ground facts
(check-proof "arith: 0 in NN"
  (lambda () (sp (make-wff-from-string "0 in nn")) (arith)))
(check-proof "arith: 2 + 3 = 5"
  (lambda () (sp (make-wff-from-string "2 + 3 = 5")) (arith)))
(check-proof "arith: power(2,3) = 8"
  (lambda () (sp (make-wff-from-string "power(2, 3) = 8")) (arith)))
(check-proof "arith: -5 in ZZ"
  (lambda () (sp (make-wff-from-string "-5 in zz")) (arith)))
(check-proof "arith: 1/3 in QQ"
  (lambda () (sp (make-wff-from-string "1/3 in qq")) (arith)))

;;; 6b. Reflexivity (rfl) and quasi-reflexivity (qrfl)
(check-proof "rfl: n = n"
  (lambda () (sp (make-wff-from-string "n = n")) (rfl)))
(check-proof "qrfl: n == n"
  (lambda () (sp (make-wff-from-string "n == n")) (qrfl)))

;;; 6c. Direct inference (di) — split conjunction, introduce implication
(check-proof "di + ass: A implies A"
  (lambda ()
    (sp (make-wff-from-string "n in nn implies n in nn"))
    (di) (ass)))

(check-proof "di + ass: A and B implies A"
  (lambda ()
    (sp (make-wff-from-string "n in nn and m in nn implies n in nn"))
    (di) (ass)))

(check-proof "di + ai: prove A and B from A, B"
  (lambda ()
    (sp (make-wff-from-string "n in nn and m in nn implies m in nn and n in nn"))
    (di)
    (ai (make-wff-from-string "n in nn and m in nn"))
    (di) (ass) (ass)))

;;; 6d. Weakening (wk) — generalize assumption
(check-proof "wk: A implies (A or B)"
  (lambda ()
    (sp (make-wff-from-string "n in nn implies n in nn or m in nn"))
    (di) (oi-l) (ass)))

;;; 6e. OR introduction (oi-l, oi-r)
(check-proof "oi-r: A implies (B or A)"
  (lambda ()
    (sp (make-wff-from-string "n in nn implies m in nn or n in nn"))
    (di) (oi-r) (ass)))

;;; 6f. Theorem assumption (ta) + universal instantiation (ui)
(check-proof "ta + ui: succ(0) in NN"
  (lambda ()
    (sp (make-wff-from-string "0 in nn implies succ(0) in nn"))
    (di)
    (ta 'nn-succ-closed) (ui "0") (ass)))

(check-proof "ta + ui: n+m in NN"
  (lambda ()
    (sp (make-wff-from-string "n in nn and m in nn implies n + m in nn"))
    (di) (ta 'nn-add-closed) (ui "n") (ui "m") (ass)))

(check-proof "ta + ui: n+0 = n"
  (lambda ()
    (sp (make-wff-from-string "n in nn implies n + 0 = n"))
    (di) (ta 'nn-add-zero) (ui "n") (ass)))

(check-proof "ta + ui: n+m = m+n"
  (lambda ()
    (sp (make-wff-from-string "n in nn and m in nn implies n + m = m + n"))
    (di) (ta 'nn-add-comm) (ui "n") (ui "m") (ass)))

(check-proof "ta + ui: n in NN => n in ZZ"
  (lambda ()
    (sp (make-wff-from-string "n in nn implies n in zz"))
    (di) (ta 'nn-subset-zz) (ui "n") (ass)))

(check-proof "ta + ui: power(x,succ n)"
  (lambda ()
    (sp (make-wff-from-string
          "x in cc and n in nn implies power(x, succ(n)) = x * power(x, n)"))
    (di) (ta 'power-succ) (ui "x") (ui "n") (ass)))

;;; 6g. Backchain (bc) -- bc takes an IMPLIES *formula* in context, NOT a
;;; theorem name.  Bring in the theorem with (ta) and instantiate first.
(check-proof "bc: n in NN and m in NN"
  (lambda ()
    (sp (make-wff-from-string "n in nn and m in nn implies n + m in nn"))
    (di) (ai (make-wff-from-string "n in nn and m in nn"))
    (ta 'nn-add-closed)
    (inst '(FORALL n (FORALL m (IMPLIES (AND (IN n NN) (IN m NN)) (IN (+ n m) NN)))) 'n)
    (inst '(FORALL m (IMPLIES (AND (IN n NN) (IN m NN)) (IN (+ n m) NN))) 'm)
    (bc '(IMPLIES (AND (IN n NN) (IN m NN)) (IN (+ n m) NN)))
    (ass) (ass) (ass)
    (unless (proof-done? *ps*) (error "bc test: proof did not close"))))

;;; 6h. Proof by contradiction (pbc)
(check-proof "pbc: classic double negation"
  (lambda ()
    (sp (make-wff-from-string "not(not(n in nn)) implies n in nn"))
    (di)
    (pbc)
    (ass)))

;;; 6i. Macete inside a proof (mac)
(check-proof "mac: eq-symm rewrites goal"
  (lambda ()
    (sp (make-wff-from-string "n = m implies m = n"))
    (di)
    (mac 'eq-symm)
    (ass)))

;;; 6j. Exists-witness (ew)
(check-proof "ew: exists x in NN. x = 0"
  (lambda ()
    (sp (make-wff-from-string "forsome([x in nn], x = 0)"))
    (ew "0")
    (arith)
    (arith)))

;;; 6k. Cut (cut)
(check-proof "cut: introduce intermediate fact"
  (lambda ()
    (sp (make-wff-from-string "n in nn implies n + 0 = n"))
    (di)
    (cut (make-wff-from-string "n in nn implies n + 0 = n"))
    (di) (ta 'nn-add-zero) (ui "n") (ass)
    (di) (ass)))

;;; 6k-eq. Equality substitution (subst) -- Leibniz schema.
;;; From a context equality k = 0, rewrite succ(k) to succ(0) in the goal.
;;; The eigenvariable name is snapshotted from *fresh-counter* before (di).
(check-proof "subst: context equality k=0 rewrites the goal"
  (lambda ()
    (sp (make-wff-from-string
         "forall([k in nn], k = 0 implies succ(k) = succ(0))"))
    (let ((kk (string->symbol
               (string-append "k_" (number->string *fresh-counter*)))))
      (di) (di)
      (subst (list '= kk 0))   ; succ(k) = succ(0)  -->  succ(0) = succ(0)
      (rfl))))

;;; subst is usable in either orientation: 0 = k in context still lets
;;; (subst (= k 0)) fire (the rule looks for the equality symmetrically).
(check-proof "subst: equality usable in reverse orientation"
  (lambda ()
    (sp (make-wff-from-string
         "forall([k in nn], 0 = k implies succ(k) = succ(0))"))
    (let ((kk (string->symbol
               (string-append "k_" (number->string *fresh-counter*)))))
      (di) (di)
      (subst (list '= kk 0))
      (rfl))))

;;; 6l. Functoid beta reduction (beta)
(check-proof "beta: lambda([x in nn], x+1)(3) = 3+1"
  (lambda ()
    (sp (make-wff-from-string "lambda([x in nn], x + 1)(3) = 3 + 1"))
    (beta)
    (rfl)))

;;; 6m. cmd-qed must discharge root context assumptions (REVIEW.md S-2).
;;; A theorem proved as Gamma |- phi must be installed as the universally
;;; closed implication, NOT as the bare phi.  Without discharge, the
;;; installed theorem would be unsoundly usable in any context.
(check "qed: discharges root context (theorem is universal closure)"
  (lambda ()
    (declare-local-context '(IN x_qedctx NN) 'qedctx-test)
    (sp (make-wff-from-string "x_qedctx in nn"))
    (ass)
    (qed 'qedctx-discharge-test)
    (undeclare-local-context 'qedctx-test)
    (let ((thm (theory-get-theorem *current-theory* 'qedctx-discharge-test)))
      ;; Expect the universal closure, not the bare formula.
      (equal? thm '(FORALL x_qedctx (IMPLIES (IN x_qedctx NN) (IN x_qedctx NN))))))
  #t)

(check "qed: no contexts -> formula installed verbatim"
  (lambda ()
    (sp (make-wff-from-string "0 in nn"))
    (arith)
    (qed 'qed-bare-formula-test)
    (equal? (theory-get-theorem *current-theory* 'qed-bare-formula-test)
            '(IN 0 NN)))
  #t)

;;; 6n. REVIEW.md S-3 / S-12 — compound heads in subst-free / free-vars.
;;; A free variable in COMPOUND head position (as in ((MUL m) a b)) must be
;;; visible to free-vars and substitutable by subst-free; otherwise
;;; instantiating an axiom over m leaves head-position occurrences
;;; uneliminable.  Symbol heads are intentionally pass-through (operator
;;; names like MUL/A/E that case-fold to bound variable names would
;;; otherwise be wrongly substituted -- see expressions.scm comments).
(check "free-vars: ((MUL m) a b) reports m via compound head"
  (lambda () (sort (free-vars '((MUL m) a b)) symbol<?))
  '(a b m))

(check "subst-free: m -> r in ((MUL m) a b) -- compound head"
  (lambda () (subst-free 'm 'r '((MUL m) a b)))
  '((MUL r) a b))

(check "subst-free: m -> r in axiom-shape head-position formula"
  (lambda ()
    (subst-free 'm 'r
                '(= ((MUL m) a b) ((MUL m) b a))))
  '(= ((MUL r) a b) ((MUL r) b a)))

(check "alpha-equiv: ((MUL m) a b) ~ ((MUL m) a b)"
  (lambda () (alpha-equiv? '((MUL m) a b) '((MUL m) a b)))
  #t)

;;; 6o. REVIEW.md S-4 / S-13 — symbolic VNB-LAMBDA must be a binder.
;;; Live axioms in algebraic.scm, complex.scm, sequences.scm use the raw
;;; (VNB-LAMBDA <bind> body) form.  Without binder treatment, free-vars
;;; reports the bound variables as free and subst-free corrupts the binder.
(check "free-vars: (VNB-LAMBDA i (g i)) hides i, exposes function variable g"
  ;; `i` is bound; `g` is an unregistered symbol head -- an applied function
  ;; variable -- so it is free (constant-head registry: g is not a constant).
  (lambda () (free-vars '(VNB-LAMBDA i (g i))))
  '(g))

(check "free-vars: (VNB-LAMBDA (LIST p q) ((ADD X) p q)) hides p,q; exposes X via compound head"
  ;; ADD is a symbol head -> treated as constant.  X is INSIDE the
  ;; compound head (ADD X) -> exposed via compound-head recursion.
  (lambda () (free-vars '(VNB-LAMBDA (LIST p q) ((ADD X) p q))))
  '(X))

(check "subst-free: i -> 99 in (VNB-LAMBDA i (+ i 1)) leaves binder intact"
  (lambda () (subst-free 'i 99 '(VNB-LAMBDA i (+ i 1))))
  '(VNB-LAMBDA i (+ i 1)))

(check "subst-free: r -> s in (VNB-LAMBDA i ((MUL r) a (f i))) -- compound head"
  ;; `r` inside the compound head (MUL r) gets substituted; the bound `i`
  ;; and the symbol head `f` are untouched.
  (lambda () (subst-free 'r 's '(VNB-LAMBDA i ((MUL r) a (f i)))))
  '(VNB-LAMBDA i ((MUL s) a (f i))))

(check "alpha-equiv: (VNB-LAMBDA x x) ~ (VNB-LAMBDA y y)"
  (lambda () (alpha-equiv? '(VNB-LAMBDA x x) '(VNB-LAMBDA y y)))
  #t)

(check "alpha-equiv: (VNB-LAMBDA (LIST p q) (f p q)) ~ (VNB-LAMBDA (LIST u v) (f u v))"
  (lambda () (alpha-equiv? '(VNB-LAMBDA (LIST p q) (f p q))
                           '(VNB-LAMBDA (LIST u v) (f u v))))
  #t)

(check "alpha-equiv: (VNB-LAMBDA x (f x)) ~ (VNB-LAMBDA (LIST y) (f y)) -- cross-shape"
  (lambda () (alpha-equiv? '(VNB-LAMBDA x (f x))
                           '(VNB-LAMBDA (LIST y) (f y))))
  #t)

(check "subst-free: capture avoidance — y -> y_replacement in (VNB-LAMBDA y body) leaves bound"
  (lambda () (subst-free 'y 'foo '(VNB-LAMBDA y (+ y x))))
  '(VNB-LAMBDA y (+ y x)))

;;; 6p. REVIEW.md S-6 — fresh-var must avoid free vars of the substitution's
;;; replacement (otherwise the renamed binder can recapture a free var the
;;; replacement was carrying).  The witness construct: subst-free `x` with a
;;; replacement that contains a name like `y_<n>` matching what fresh-var
;;; would naively produce.  We can't predict the counter, so test with a
;;; structurally-tight version:
(check "fresh-var: result avoids free vars of every avoid arg"
  (lambda ()
    (let* ((y (fresh-var 'y '(IN y_999 NN) '(IN y_998 NN))))
      ;; Both y_999 and y_998 are forbidden; result must be neither.
      (and (not (eq? y 'y_999)) (not (eq? y 'y_998)))))
  #t)

;;; This is the audit's exact rename-branch witness for S-6.  We force the
;;; global *fresh-counter* to a value that, WITHOUT the fix, would make
;;; fresh-var return `y_42` -- the same name carried in the replacement,
;;; causing the new binder to capture the replacement's free `y_42`.
(check "subst-free: fresh rename does not capture replacement's free var"
  (lambda ()
    (set! *fresh-counter* 42)
    (let* ((r       (subst-free 'x '(+ y y_42) '(FORALL y (= x z))))
           (new-bv  (cadr r)))
      (not (eq? new-bv 'y_42))))
  #t)

;;; 6q. REVIEW.md S-7 — pi-theorem-assumption! takes a NAME and looks it up
;;; itself; refuses unknown names.  Previously accepted any raw S-expression.
(check "pi-theorem-assumption!: returns #f on unknown name (no kernel bypass)"
  (lambda ()
    (sp (make-wff-from-string "0 in nn"))
    (let ((sqn (proof-state-focus *ps*)))
      ;; Should refuse: this name is not in *theorem-table*.
      (pi-theorem-assumption! sqn 'nonexistent-theorem-zzz-xyz)))
  #f)

(check "pi-theorem-assumption!: works on known name"
  (lambda ()
    (sp (make-wff-from-string "0 in nn"))
    (let ((sqn (proof-state-focus *ps*)))
      (let ((r (pi-theorem-assumption! sqn 'nn-zero-in)))
        (and r #t))))
  #t)

;;; 6r. REVIEW.md S-8 — pi-functoid-beta! must use PARALLEL substitution.
;;; Witness: f = (lambda (x y) (LIST x y)), apply to (y, 0).
;;;   sequential x:=y -> (LIST y y), then y:=0 -> (LIST 0 0)  -- WRONG
;;;   parallel: result is (LIST y 0)                          -- CORRECT
(check "pi-functoid-beta!: parallel substitution"
  (lambda ()
    (let* ((ftd  (make-functoid 'lambda
                                (list (cons 'x 'NN) (cons 'y 'NN))
                                '(LIST x y)))
           (expr `(apply-functoid ,ftd y 0)))
      (reduce-functoid-in-expr expr)))
  '(LIST y 0))

;;; 6s. REVIEW.md S-10 — theorem->elementary-macete returns an INERT macete
;;; (always returns #f) when schema-vars appear in conditions or replacement
;;; but NOT in source.  The theorem stays in *theorem-table* (usable via
;;; theorem-assumption); the broken rewrite is silently skipped.
(check "S-10: rogue schema-var detected"
  (lambda () (theorem-rogue-schema-vars '(n k) '((IN k NN)) '(foo n) 'n))
  '(k))

(check "S-10: clean theorem -> no rogue vars"
  (lambda () (theorem-rogue-schema-vars '(n) '((IN n NN)) '(foo n) 'n))
  '())

(check "S-10: rogue theorem -> inert macete (returns #f when applied)"
  (lambda ()
    ;; Suppress the warning printout by redirecting stdout briefly.
    (let ((m (with-output-to-string
               (lambda ()
                 (theorem->elementary-macete
                   '(FORALL n (FORALL k (IMPLIES (IN k NN) (= (foo n) n)))))))))
      ;; The macete itself: install it and try to apply.
      (let ((macete (theorem->elementary-macete
                      '(FORALL n (FORALL k (IMPLIES (IN k NN) (= (foo n) n)))))))
        ;; Apply against a sequent: should be #f (inert).
        (sp (make-wff-from-string "(foo 0) = 0"))
        (macete (proof-state-focus *ps*)))))
  #f)

;;; 6t. REVIEW.md D-6 — n-ary UNION/INTERSECTION accepted; COMPLEMENT-IN
;;; installed as a binary constructor with sethood-closure and membership-iff
;;; axioms.  Per-arity sethood for n-ary UNION/INTERSECTION follows from the
;;; binary axiom by induction; n-ary semantics in proofs is provided by the
;;; pre-existing kernel rules pi-union-intro!/-elim! and pi-intersection-*.

(display "\n=== 6t. REVIEW.md D-6: n-ary set operators + COMPLEMENT-IN ===\n")

;; Validator now accepts (UNION A B C) and (INTERSECTION A B C).
(check-true "make-wff accepts (UNION A B C)"
  (lambda () (wff? (make-wff '(IN x (UNION A B C))))))

(check-true "make-wff accepts (INTERSECTION A B C D)"
  (lambda () (wff? (make-wff '(IN x (INTERSECTION A B C D))))))

(check-true "make-wff accepts (COMPLEMENT-IN A B)"
  (lambda () (wff? (make-wff '(IN x (COMPLEMENT-IN A B))))))

(check-error "(UNION A) (1 arg) rejected"
  (lambda () (make-wff '(IN x (UNION A)))))

(check-error "(COMPLEMENT-IN A) (wrong arity) rejected"
  (lambda () (make-wff '(IN x (COMPLEMENT-IN A)))))

;; Free-vars / subst-free / alpha-equiv treat COMPLEMENT-IN as a binary term.
(check "free-vars (COMPLEMENT-IN A B) = (A B)"
  (lambda () (free-vars '(COMPLEMENT-IN A B)))
  '(A B))

(check "subst-free A->X in (COMPLEMENT-IN A B) = (COMPLEMENT-IN X B)"
  (lambda () (subst-free 'A 'X '(COMPLEMENT-IN A B)))
  '(COMPLEMENT-IN X B))

(check-true "alpha-equiv (COMPLEMENT-IN A B) ~ itself"
  (lambda () (alpha-equiv? '(COMPLEMENT-IN A B) '(COMPLEMENT-IN A B))))

;; New axioms are installed and looked up.
(check-true "union-membership axiom installed"
  (lambda () (and (lookup-theorem 'union-membership) #t)))

(check-true "intersection-membership axiom installed"
  (lambda () (and (lookup-theorem 'intersection-membership) #t)))

(check-true "complement-in-set-closure axiom installed"
  (lambda () (and (lookup-theorem 'complement-in-set-closure) #t)))

(check-true "complement-in-membership axiom installed"
  (lambda () (and (lookup-theorem 'complement-in-membership) #t)))

;;; 6u. Bonus fix surfaced while doing D-6: unary (FUN A) used to crash the
;;; binary FUN dispatch in free-vars / subst-free / alpha-equiv-under? /
;;; match-expr / rewrite-subexpressions.  fun-domain-apply-def, -extensionality,
;;; -elements-are-sets, and fun-codomain-iff all use (FUN A) and silently
;;; failed to install their macetes (vnb-guard caught the car-of-() error).
;;; Now both arities are handled; macetes install (and S-10 flags the
;;; symbol-head schema-vars, which is the correct downstream behaviour).

(display "\n=== 6u. Unary (FUN A) handled by free-vars/subst-free/alpha-equiv ===\n")

(check "free-vars (FUN A) = (A)"
  (lambda () (free-vars '(FUN A)))
  '(A))

(check "free-vars (FUN A B) = (A B)"
  (lambda () (free-vars '(FUN A B)))
  '(A B))

(check "subst-free A->X in (FUN A) = (FUN X)"
  (lambda () (subst-free 'A 'X '(FUN A)))
  '(FUN X))

(check "subst-free A->X in (FUN A B) = (FUN X B)"
  (lambda () (subst-free 'A 'X '(FUN A B)))
  '(FUN X B))

(check-true "alpha-equiv (FUN A) ~ itself"
  (lambda () (alpha-equiv? '(FUN A) '(FUN A))))

(check-false "alpha-equiv (FUN A) !~ (FUN A B)"
  (lambda () (alpha-equiv? '(FUN A) '(FUN A B))))

;; All four fun-* axioms now register in the theorem table.
(check-true "fun-domain-apply-def in theorem table"
  (lambda () (and (lookup-theorem 'fun-domain-apply-def) #t)))

(check-true "fun-domain-extensionality in theorem table"
  (lambda () (and (lookup-theorem 'fun-domain-extensionality) #t)))

(check-true "fun-domain-elements-are-sets in theorem table"
  (lambda () (and (lookup-theorem 'fun-domain-elements-are-sets) #t)))

(check-true "fun-codomain-iff in theorem table"
  (lambda () (and (lookup-theorem 'fun-codomain-iff) #t)))

;;; 6v. REVIEW.md D-7 — SEP, COMP, IOTA, VNB-LAMBDA, 2-arg POWER characterized.
;;; SEP/COMP/IOTA/VNB-LAMBDA via primitive inferences (because the body
;;; formula is genuinely a schema and can't appear in a FOL axiom);
;;; 2-arg POWER via the definitional equation (POWER A B) = (FUN B A).

(display "\n=== 6v. REVIEW.md D-7: SEP/COMP/IOTA/VNB-LAMBDA/POWER ===\n")

;; --- SEPARATION ---
(check-proof "pi-sep-sethood: (IN (SEP x A p) SET) reduces to (IN A SET)"
  (lambda ()
    (sp (make-wff '(IN (SEP x A (IN x NN)) SET)))
    (let ((sqn (proof-state-focus *ps*)))
      (let ((r (pi-sep-sethood! sqn)))
        (or r (error "pi-sep-sethood! failed"))))))

(check-proof "pi-sep-mem-intro: (IN 0 (SEP x NN (= x 0))) splits"
  (lambda ()
    (sp (make-wff '(IN 0 (SEP x NN (= x 0)))))
    (let ((sqn (proof-state-focus *ps*)))
      (let ((r (pi-sep-mem-intro! sqn)))
        (or r (error "pi-sep-mem-intro! failed"))))))

(check-proof "pi-sep-mem-elim: assumption (IN 0 (SEP x NN p)) splits ctx"
  (lambda ()
    (declare-local-context '(IN 0 (SEP x NN (= x 0))) 'sep-mem-elim-ctx)
    (sp (make-wff 'TRUTH))
    (let ((sqn (proof-state-focus *ps*)))
      (let ((r (pi-sep-mem-elim! sqn '(IN 0 (SEP x NN (= x 0))))))
        (undeclare-local-context 'sep-mem-elim-ctx)
        (or r (error "pi-sep-mem-elim! failed"))))))

;; pi-sep-sethood does NOT fire on a non-SEP goal
(check "pi-sep-sethood: refuses (IN 0 NN)"
  (lambda ()
    (sp (make-wff '(IN 0 NN)))
    (pi-sep-sethood! (proof-state-focus *ps*)))
  #f)

;; --- COMPREHENSION ---
(check-proof "pi-comp-mem-intro: (IN 0 (COMP x p)) splits"
  (lambda ()
    (sp (make-wff '(IN 0 (COMP x (IN x NN)))))
    (let ((sqn (proof-state-focus *ps*)))
      (let ((r (pi-comp-mem-intro! sqn)))
        (or r (error "pi-comp-mem-intro! failed"))))))

(check-proof "pi-comp-mem-elim: assumption (IN 0 (COMP x p)) splits ctx"
  (lambda ()
    (declare-local-context '(IN 0 (COMP x (IN x NN))) 'comp-mem-elim-ctx)
    (sp (make-wff 'TRUTH))
    (let ((sqn (proof-state-focus *ps*)))
      (let ((r (pi-comp-mem-elim! sqn '(IN 0 (COMP x (IN x NN))))))
        (undeclare-local-context 'comp-mem-elim-ctx)
        (or r (error "pi-comp-mem-elim! failed"))))))

;; --- IOTA ---
(check-proof "pi-iota-def: posts existence-uniqueness + defprop subgoals"
  (lambda ()
    (sp (make-wff '(= 0 0)))
    (let ((sqn (proof-state-focus *ps*)))
      (let ((r (pi-iota-def! sqn '(IOTA x (= x 0)))))
        (or r (error "pi-iota-def! failed"))))))

(check "pi-iota-def: refuses non-IOTA argument"
  (lambda ()
    (sp (make-wff '(= 0 0)))
    (pi-iota-def! (proof-state-focus *ps*) 'not-an-iota))
  #f)

;; --- VNB-LAMBDA: typing ---
(check-proof "pi-lambda-type: (IN (VNB-LAMBDA x x) (FUN NN NN)) reduces"
  (lambda ()
    (sp (make-wff '(IN (VNB-LAMBDA x x) (FUN NN NN))))
    (let ((sqn (proof-state-focus *ps*)))
      (let ((r (pi-lambda-type! sqn)))
        (or r (error "pi-lambda-type! failed"))))))

;; --- VNB-LAMBDA: beta reduction ---
(check "reduce-lambda-in-expr: ((VNB-LAMBDA x (+ x 1)) 5) -> (+ 5 1)"
  (lambda () (reduce-lambda-in-expr '((VNB-LAMBDA x (+ x 1)) 5)))
  '(+ 5 1))

(check "reduce-lambda-in-expr: ((VNB-LAMBDA (LIST x y) (+ x y)) 3 4) -> (+ 3 4)"
  (lambda () (reduce-lambda-in-expr '((VNB-LAMBDA (LIST x y) (+ x y)) 3 4)))
  '(+ 3 4))

;; Parallel substitution (analogous to S-8 for functoid-beta):
;;   ((VNB-LAMBDA (LIST x y) (LIST x y)) y 0)
;; sequential x:=y -> (LIST y y), then y:=0 -> (LIST 0 0)        WRONG
;; parallel: (LIST y 0)                                          CORRECT
(check "reduce-lambda-in-expr: parallel substitution"
  (lambda () (reduce-lambda-in-expr '((VNB-LAMBDA (LIST x y) (LIST x y)) y 0)))
  '(LIST y 0))

;; reduce-lambda-in-expr recurses into subterms
(check "reduce-lambda-in-expr: nested in IN"
  (lambda () (reduce-lambda-in-expr '(IN ((VNB-LAMBDA x x) 7) NN)))
  '(IN 7 NN))

;; --- POWER (2-arg) ---
(check-true "power-exp axiom installed"
  (lambda () (and (lookup-theorem 'power-exp) #t)))

;; The macete (power-exp) should rewrite (POWER A B) to (FUN B A).
(check "power-exp macete: (POWER NN NN) ~> (FUN NN NN)"
  (lambda () (macete-str 'power-exp "power(nn, nn) in set"))
  "fun(nn, nn) in set")

;;; 6w. Variadic pattern matching in the macete engine: RESTVAR in source
;;; patterns and SPLICE in replacement templates.  These let a single macete
;;; rewrite an arbitrary-arity UNION/INTERSECTION membership formula to its
;;; disjunctive/conjunctive expansion.

(display "\n=== 6w. Variadic patterns: RESTVAR + SPLICE ===\n")

;; --- RESTVAR matching ---

(check "RESTVAR captures all UNION args (n=2)"
  (lambda ()
    (let ((m (match-expr '(IN x (UNION (RESTVAR AS)))
                         '(IN x (UNION A B))
                         '(x AS))))
      (and m (restbound-exprs (cdr (assq 'AS m))))))
  '(A B))

(check "RESTVAR captures all UNION args (n=3)"
  (lambda ()
    (let ((m (match-expr '(IN x (UNION (RESTVAR AS)))
                         '(IN x (UNION A B C))
                         '(x AS))))
      (and m (restbound-exprs (cdr (assq 'AS m))))))
  '(A B C))

(check "RESTVAR captures tail after fixed prefix"
  (lambda ()
    (let ((m (match-expr '(IN x (UNION X1 (RESTVAR AS)))
                         '(IN x (UNION A B C D))
                         '(x X1 AS))))
      (and m
           (list (cdr (assq 'X1 m))
                 (restbound-exprs (cdr (assq 'AS m)))))))
  '(A (B C D)))

(check-false "RESTVAR on INTERSECTION does not match UNION expr"
  (lambda ()
    (match-expr '(IN x (INTERSECTION (RESTVAR AS)))
                '(IN x (UNION A B))
                '(x AS))))

(check "RESTVAR with empty tail (UNION has only fixed prefix)"
  (lambda ()
    (let ((m (match-expr '(UNION X1 X2 (RESTVAR AS))
                         '(UNION A B)
                         '(X1 X2 AS))))
      (and m (restbound-exprs (cdr (assq 'AS m))))))
  '())

(check-true "RESTVAR strict-mode: pattern without RESTVAR still requires equal length"
  (lambda ()
    (not (match-expr '(UNION X1 X2)
                     '(UNION A B C)
                     '(X1 X2)))))

;; --- List-aware merge-subst (rest-var bound twice must be alpha-equiv) ---

(check-true "merge-subst accepts two equal restbound bindings"
  (lambda ()
    (let ((s1 (list (cons 'AS (make-restbound '(A B C)))))
          (s2 (list (cons 'AS (make-restbound '(A B C))))))
      (and (merge-subst s1 s2) #t))))

(check-false "merge-subst rejects differing restbound bindings (lengths)"
  (lambda ()
    (let ((s1 (list (cons 'AS (make-restbound '(A B)))))
          (s2 (list (cons 'AS (make-restbound '(A B C))))))
      (merge-subst s1 s2))))

(check-false "merge-subst rejects differing restbound bindings (contents)"
  (lambda ()
    (let ((s1 (list (cons 'AS (make-restbound '(A B)))))
          (s2 (list (cons 'AS (make-restbound '(A C))))))
      (merge-subst s1 s2))))

(check-false "merge-subst rejects mixing restbound with ordinary"
  (lambda ()
    (let ((s1 (list (cons 'AS (make-restbound '(A B)))))
          (s2 (list (cons 'AS 'A))))
      (merge-subst s1 s2))))

;; --- SPLICE expansion ---

(check "SPLICE OR over 3 elements: right-fold"
  (lambda ()
    (apply-subst (list (cons 'x 'a)
                       (cons 'AS (make-restbound '(A B C))))
                 '(SPLICE OR e AS (IN x e))))
  '(OR (IN a A) (OR (IN a B) (IN a C))))

(check "SPLICE OR over 1 element: just the template instance"
  (lambda ()
    (apply-subst (list (cons 'x 'a)
                       (cons 'AS (make-restbound '(A))))
                 '(SPLICE OR e AS (IN x e))))
  '(IN a A))

(check "SPLICE AND mirrors OR shape"
  (lambda ()
    (apply-subst (list (cons 'x 'a)
                       (cons 'AS (make-restbound '(A B C))))
                 '(SPLICE AND e AS (IN x e))))
  '(AND (IN a A) (AND (IN a B) (IN a C))))

;; --- End-to-end: the three decompose macetes, installed by theory.scm ---

(check-true "union-decompose axiom installed"
  (lambda () (and (lookup-theorem 'union-decompose) #t)))

(check-true "intersection-decompose axiom installed"
  (lambda () (and (lookup-theorem 'intersection-decompose) #t)))

(check "union-decompose rewrites x in union(a, b, c)"
  (lambda () (macete-str 'union-decompose "x in union(a, b, c)"))
  "x in a or x in b or x in c")

(check "union-decompose rewrites x in union(a, b)"
  (lambda () (macete-str 'union-decompose "x in union(a, b)"))
  "x in a or x in b")

(check "intersection-decompose rewrites x in intersection(a, b, c)"
  (lambda () (macete-str 'intersection-decompose "x in intersection(a, b, c)"))
  "x in a and x in b and x in c")

(check "intersection-decompose rewrites x in intersection(a, b)"
  (lambda () (macete-str 'intersection-decompose "x in intersection(a, b)"))
  "x in a and x in b")

;; --- cartesian-decompose: procedural macete (theory.scm) ---
;; Compare via alpha-equiv? since the fresh-var names are non-deterministic.

(check-true "cartesian-decompose macete installed"
  (lambda () (and (lookup-macete 'cartesian-decompose) #t)))

(check-true "build-cartesian-witness (n=2): structure matches expected chain"
  (lambda ()
    (alpha-equiv?
      (build-cartesian-witness 'x '(A B))
      '(FORSOME u (AND (IN u A)
         (FORSOME v (AND (IN v B) (= x (LIST u v)))))))))

(check-true "build-cartesian-witness (n=3): structure matches expected chain"
  (lambda ()
    (alpha-equiv?
      (build-cartesian-witness 'x '(A B C))
      '(FORSOME u (AND (IN u A)
         (FORSOME v (AND (IN v B)
            (FORSOME w (AND (IN w C) (= x (LIST u v w)))))))))))

(check-true "build-cartesian-witness (n=1): single FORSOME"
  (lambda ()
    (alpha-equiv?
      (build-cartesian-witness 'x '(A))
      '(FORSOME u (AND (IN u A) (= x (LIST u)))))))

(check-true "build-cartesian-witness avoids x as a fresh-var name"
  (lambda ()
    ;; Pass x=a so the fresh-var would naturally collide with one of the
    ;; class names if it weren't avoided.
    (let ((w (build-cartesian-witness 'a '(A B))))
      ;; The outer bound var must NOT be the symbol 'a' (would shadow x).
      (not (eq? (cadr w) 'a)))))

(check-proof "cartesian-decompose on (IN x (CARTESIAN A B)) at goal top"
  (lambda ()
    (sp (make-wff '(IN x (CARTESIAN A B))))
    (let ((sqn (proof-state-focus *ps*)))
      (or (apply-macete! 'cartesian-decompose sqn)
          (error "cartesian-decompose failed to fire")))))

(check-proof "cartesian-decompose descends through IMPLIES"
  (lambda ()
    (sp (make-wff '(IMPLIES (IN x SET) (IN x (CARTESIAN A B)))))
    (let ((sqn (proof-state-focus *ps*)))
      (or (apply-macete! 'cartesian-decompose sqn)
          (error "cartesian-decompose failed to descend through IMPLIES")))))

;; --- Binder descent: cartesian-decompose fires under FORALL ---

(check-true "cartesian-decompose descends under FORALL; fresh-var avoids bvar"
  (lambda ()
    ;; The bvar `y` is in scope; the rewrite generates fresh `a_i` names
    ;; that must not collide with y (else the result mis-parses y as a
    ;; reference to the FORALL-bound name from outside).
    (let* ((g       '(FORALL y (IN y (CARTESIAN A B))))
           (rewrote (rewrite-by-proc cartesian-decompose-fire g))
           (body    (caddr rewrote))      ; under FORALL y
           (bv1     (cadr body))          ; outer FORSOME bvar
           (inner   (caddr body))         ; AND
           (and-rhs (caddr inner))        ; nested FORSOME
           (bv2     (cadr and-rhs)))
      (and (not (eq? bv1 'y))
           (not (eq? bv2 'y))
           (not (eq? bv1 bv2))))))

;; --- tuple-equality-decompose ---

(check-true "tuple-equality-decompose macete installed"
  (lambda () (and (lookup-macete 'tuple-equality-decompose) #t)))

(check "build-tuple-equality (n=0) → TRUTH"
  (lambda () (build-tuple-equality '() '()))
  'TRUTH)

(check "build-tuple-equality (n=1) → single ="
  (lambda () (build-tuple-equality '(a) '(b)))
  '(= a b))

(check "build-tuple-equality (n=2) → AND chain"
  (lambda () (build-tuple-equality '(a1 a2) '(b1 b2)))
  '(AND (= a1 b1) (= a2 b2)))

(check "build-tuple-equality (n=3) → nested AND"
  (lambda () (build-tuple-equality '(a1 a2 a3) '(b1 b2 b3)))
  '(AND (= a1 b1) (AND (= a2 b2) (= a3 b3))))

(check-proof "tuple-equality-decompose: [a, b] = [c, d] fires"
  (lambda ()
    (sp (make-wff '(= (LIST a b) (LIST c d))))
    (let ((sqn (proof-state-focus *ps*)))
      (or (apply-macete! 'tuple-equality-decompose sqn)
          (error "tuple-equality-decompose failed on n=2")))))

(check-proof "tuple-equality-decompose: [a, b, c] = [d, e, f] fires"
  (lambda ()
    (sp (make-wff '(= (LIST a b c) (LIST d e f))))
    (let ((sqn (proof-state-focus *ps*)))
      (or (apply-macete! 'tuple-equality-decompose sqn)
          (error "tuple-equality-decompose failed on n=3")))))

(check-false "tuple-equality-decompose: refuses unequal lengths"
  (lambda ()
    (tuple-equality-decompose-fire '(= (LIST a b) (LIST c d e)) '())))

(check-false "tuple-equality-decompose: refuses non-LIST sides"
  (lambda ()
    (tuple-equality-decompose-fire '(= x (LIST a b)) '())))

(check-proof "tuple-equality-decompose descends under FORALL"
  (lambda ()
    (sp (make-wff '(FORALL y (IMPLIES (= y 0)
                              (= (LIST y y) (LIST 0 0))))))
    (let ((sqn (proof-state-focus *ps*)))
      (or (apply-macete! 'tuple-equality-decompose sqn)
          (error "tuple-equality-decompose failed under FORALL")))))

;;; -----------------------------------------------------------------------
;;; 7. Number system inclusion chain
;;;
;;; Exercises the chain NN ⊆ ZZ ⊆ QQ ⊆ RR ⊆ CC via the arithmetic
;;; evaluator.

(display "\n=== 7. Number system inclusion chain ===\n")

(for-each
  (lambda (triple)
    (let ((val (car triple)) (sys (cadr triple)) (expected (caddr triple)))
      (check (string-append (number->string val) " in " (symbol->string sys))
             (lambda () (arith-membership-check val sys))
             expected)))
  '((0    NN #t)  (1    NN #t)  (-1   NN #f)  (1/2  NN #f)
    (0    ZZ #t)  (-5   ZZ #t)  (1/2  ZZ #f)
    (1/3  QQ #t)  (-7   QQ #t)  (1/3  ZZ #f)
    (0    RR #t)  (-7   RR #t)
    (0    CC #t)  (-5   CC #t)))

;;; 8. Arithmetic in ZZ / QQ / RR / CC

(display "\n=== 8. Arithmetic in ZZ QQ RR CC ===\n")

(check-proof "arith: 0 in ZZ"
  (lambda () (sp (make-wff-from-string "0 in zz")) (arith)))
(check-proof "arith: -3 in ZZ"
  (lambda () (sp (make-wff-from-string "-3 in zz")) (arith)))
(check-proof "arith: 1/3 in QQ"
  (lambda () (sp (make-wff-from-string "1/3 in qq")) (arith)))
(check-proof "arith: 0 in RR"
  (lambda () (sp (make-wff-from-string "0 in rr")) (arith)))
(check-proof "arith: 0 in CC"
  (lambda () (sp (make-wff-from-string "0 in cc")) (arith)))
(check-proof "arith: 1/3 not in ZZ"
  (lambda ()
    (sp (make-wff-from-string "not(1/3 in zz)"))
    (arith)))

(check "1/3 in zz" (lambda () (arith-eval-formula '(IN 1/3 ZZ)))  #f)
(check "1/3 in qq" (lambda () (arith-eval-formula '(IN 1/3 QQ)))  #t)
(check "1/3 in rr" (lambda () (arith-eval-formula '(IN 1/3 RR)))  #t)
(check "1/3 in cc" (lambda () (arith-eval-formula '(IN 1/3 CC)))  #t)
(check "-3 in zz"  (lambda () (arith-eval-formula '(IN -3 ZZ)))   #t)
(check "-3 in qq"  (lambda () (arith-eval-formula '(IN -3 QQ)))   #t)

;;; -----------------------------------------------------------------------
;;; NN induction: (ni) splits correctly and base/step close

(check-proof "ni: 0=0 base closes by arith"
  (lambda ()
    (sp (make-wff-from-string "forall([n in NN], n = n)"))
    (ni)          ; focus lands on base: 0 = 0
    (arith)       ; closes base
    (focus 1)     ; move to step
    (di) (di)     ; peel forall n, peel implies
    (ass)))       ; n=n follows from assumption n=n

(check-proof "ni: sum-zero fires as theorem-assumption"
  (lambda ()
    (sp (make-wff-from-string
          "forall([r, f], IS-RING(r) implies f in FUN(NN, A(r)) implies SUM(r, f, 0) = ZERO(r)"))
    (di) (di) (di)
    (ta 'sum-zero)
    (ass)))

;;; -----------------------------------------------------------------------
;;; prod-ord-type and sum-type: formal proofs by NN induction
;;;
;;; These theorems are already installed as axioms in sequences.scm for
;;; convenience; the proofs below verify they are derivable by (ni).

(display "\n=== prod-ord-type and sum-type by ni ===\n")

(check-proof "prod-ord-type provable by ni"
  (lambda ()
    (sp (make-wff '(IMPLIES (IS-MONOID m)
                     (IMPLIES (IN f (FUN NN (A m)))
                       (FORALL n (IMPLIES (IN n NN) (IN (PROD-ORD m f n) (A m))))))))
    (di) (di) (ni)
    ;; --- BASE: PROD-ORD(m,f,0) in A(m) ---
    ;; Use eq-subst-membership: (= a b) /\ b in S -> a in S,
    ;; with a = PROD-ORD(m,f,0), b = E(m), S = A(m).
    (ta 'eq-subst-membership)
    (inst '(FORALL a (FORALL b (FORALL S (IMPLIES (AND (= a b) (IN b S)) (IN a S)))))
          '(PROD-ORD m f 0))
    (inst '(FORALL b (FORALL S (IMPLIES (AND (= (PROD-ORD m f 0) b) (IN b S)) (IN (PROD-ORD m f 0) S))))
          '(E m))
    (inst '(FORALL S (IMPLIES (AND (= (PROD-ORD m f 0) (E m)) (IN (E m) S)) (IN (PROD-ORD m f 0) S)))
          '(A m))
    (bc '(IMPLIES (AND (= (PROD-ORD m f 0) (E m)) (IN (E m) (A m))) (IN (PROD-ORD m f 0) (A m))))
    (di)                          ; AND-split -> focus: (= PROD-ORD(m,f,0) E(m))
    ;; Membership conjunct is the last DG node after AND-split.
    ;; Save it now; after (ass) closes equality, focus jumps to STEP.
    (let* ((mem-node (car (reverse (dg-sequent-nodes (proof-state-dg *ps*))))))
      (ta 'prod-ord-zero)
      (inst '(FORALL m (FORALL f (= (PROD-ORD m f 0) (E m)))) 'm)
      (inst '(FORALL f (= (PROD-ORD m f 0) (E m))) 'f)
      (ass)                       ; closes equality; focus jumps to STEP
      (set-proof-state-focus! *ps* mem-node)
      (ta 'monoid-identity-in)
      (inst '(FORALL m (IMPLIES (IS-MONOID m) (IN (E m) (A m)))) 'm)
      (bc '(IMPLIES (IS-MONOID m) (IN (E m) (A m))))
      (ass))                      ; base done; focus -> STEP
    ;; --- STEP: forall n in NN. PROD-ORD(m,f,n) in A(m) -> PROD-ORD(m,f,succ n) in A(m) ---
    (di)    ; peel FORALL n, freshens n -> n_k, adds (IN n_k NN)
    (let* ((n-k (cadr (wff-formula (car (sequent-node-assumptions (proof-state-focus *ps*)))))))
      (di)  ; peel IMPLIES IH, adds PROD-ORD(m,f,n_k) in A(m); focus = PROD-ORD(m,f,succ n_k) in A(m)
      ;; Use eq-subst-membership with a = PROD-ORD(m,f,succ n_k),
      ;;   b = (MUL m)(PROD-ORD m f n_k)(f n_k), S = A(m).
      (ta 'eq-subst-membership)
      (inst '(FORALL a (FORALL b (FORALL S (IMPLIES (AND (= a b) (IN b S)) (IN a S)))))
            `(PROD-ORD m f (succ ,n-k)))
      (inst `(FORALL b (FORALL S (IMPLIES (AND (= (PROD-ORD m f (succ ,n-k)) b) (IN b S))
                                           (IN (PROD-ORD m f (succ ,n-k)) S))))
            `((MUL m) (PROD-ORD m f ,n-k) (f ,n-k)))
      (inst `(FORALL S (IMPLIES (AND (= (PROD-ORD m f (succ ,n-k))
                                        ((MUL m) (PROD-ORD m f ,n-k) (f ,n-k)))
                                    (IN ((MUL m) (PROD-ORD m f ,n-k) (f ,n-k)) S))
                                (IN (PROD-ORD m f (succ ,n-k)) S)))
            '(A m))
      (bc `(IMPLIES (AND (= (PROD-ORD m f (succ ,n-k))
                             ((MUL m) (PROD-ORD m f ,n-k) (f ,n-k)))
                         (IN ((MUL m) (PROD-ORD m f ,n-k) (f ,n-k)) (A m)))
                    (IN (PROD-ORD m f (succ ,n-k)) (A m))))
      (di)  ; AND-split -> focus: (= PROD-ORD(m,f,succ n_k) ...)
      ;; Prove the succ equation from prod-ord-succ.
      (ta 'prod-ord-succ)
      (inst '(FORALL m (FORALL f (FORALL n (IMPLIES (IN n NN)
               (= (PROD-ORD m f (succ n)) ((MUL m) (PROD-ORD m f n) (f n))))))) 'm)
      (inst '(FORALL f (FORALL n (IMPLIES (IN n NN)
               (= (PROD-ORD m f (succ n)) ((MUL m) (PROD-ORD m f n) (f n)))))) 'f)
      (inst '(FORALL n (IMPLIES (IN n NN)
               (= (PROD-ORD m f (succ n)) ((MUL m) (PROD-ORD m f n) (f n))))) n-k)
      (bc `(IMPLIES (IN ,n-k NN)
                    (= (PROD-ORD m f (succ ,n-k)) ((MUL m) (PROD-ORD m f ,n-k) (f ,n-k)))))
      (ass)   ; (IN n_k NN) in context; focus: (IN (MUL m)... A(m))
      ;; Prove (MUL m)(PROD-ORD m f n_k)(f n_k) in A(m) via monoid-carrier-closed-mul.
      (ta 'monoid-carrier-closed-mul)
      (inst '(FORALL m (FORALL a (FORALL b
               (IMPLIES (AND (IS-MONOID m) (AND (IN a (A m)) (IN b (A m))))
                        (IN ((MUL m) a b) (A m)))))) 'm)
      (inst `(FORALL a (FORALL b
               (IMPLIES (AND (IS-MONOID m) (AND (IN a (A m)) (IN b (A m))))
                        (IN ((MUL m) a b) (A m))))) `(PROD-ORD m f ,n-k))
      (inst `(FORALL b
               (IMPLIES (AND (IS-MONOID m) (AND (IN (PROD-ORD m f ,n-k) (A m)) (IN b (A m))))
                        (IN ((MUL m) (PROD-ORD m f ,n-k) b) (A m)))) `(f ,n-k))
      (bc `(IMPLIES (AND (IS-MONOID m)
                         (AND (IN (PROD-ORD m f ,n-k) (A m)) (IN (f ,n-k) (A m))))
                    (IN ((MUL m) (PROD-ORD m f ,n-k) (f ,n-k)) (A m))))
      (di) (ass)   ; IS-MONOID(m) [ass]
      (di) (ass)   ; PROD-ORD(m,f,n_k) in A(m) [IH]
      ;; Prove (f n_k) in A(m) via fun-apply-type.
      (ta 'fun-apply-type)
      (inst '(FORALL f (FORALL A (FORALL B (FORALL x
               (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) 'f)
      (inst '(FORALL A (FORALL B (FORALL x
               (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B))))) 'NN)
      (inst '(FORALL B (FORALL x
               (IMPLIES (AND (IN f (FUN NN B)) (IN x NN)) (IN (f x) B)))) '(A m))
      (inst `(FORALL x (IMPLIES (AND (IN f (FUN NN (A m))) (IN x NN)) (IN (f x) (A m)))) n-k)
      (bc `(IMPLIES (AND (IN f (FUN NN (A m))) (IN ,n-k NN)) (IN (f ,n-k) (A m))))
      (di) (ass) (ass))  ; f in FUN(NN,A(m)) [ass]; n_k in NN [ass]; proof done
    (unless (proof-done? *ps*) (error "prod-ord-type proof incomplete"))))

(check-proof "sum-type provable by ni"
  (lambda ()
    (sp (make-wff '(IMPLIES (IS-RING r)
                     (IMPLIES (IN f (FUN NN (A r)))
                       (FORALL n (IMPLIES (IN n NN) (IN (SUM r f n) (A r))))))))
    (di) (di) (ni)
    ;; --- BASE: SUM(r,f,0) in A(r) ---
    (ta 'eq-subst-membership)
    (inst '(FORALL a (FORALL b (FORALL S (IMPLIES (AND (= a b) (IN b S)) (IN a S)))))
          '(SUM r f 0))
    (inst '(FORALL b (FORALL S (IMPLIES (AND (= (SUM r f 0) b) (IN b S)) (IN (SUM r f 0) S))))
          '(ZERO r))
    (inst '(FORALL S (IMPLIES (AND (= (SUM r f 0) (ZERO r)) (IN (ZERO r) S)) (IN (SUM r f 0) S)))
          '(A r))
    (bc '(IMPLIES (AND (= (SUM r f 0) (ZERO r)) (IN (ZERO r) (A r))) (IN (SUM r f 0) (A r))))
    (di)                          ; AND-split -> focus: (= SUM(r,f,0) ZERO(r))
    (let* ((mem-node (car (reverse (dg-sequent-nodes (proof-state-dg *ps*))))))
      (ta 'sum-zero)
      (inst '(FORALL r (FORALL f (= (SUM r f 0) (ZERO r)))) 'r)
      (inst '(FORALL f (= (SUM r f 0) (ZERO r))) 'f)
      (ass)                       ; closes equality; focus jumps to STEP
      (set-proof-state-focus! *ps* mem-node)
      (ta 'ring-zero-in)
      (inst '(FORALL r (IMPLIES (IS-RING r) (IN (ZERO r) (A r)))) 'r)
      (bc '(IMPLIES (IS-RING r) (IN (ZERO r) (A r))))
      (ass))                      ; base done; focus -> STEP
    ;; --- STEP ---
    (di)    ; peel FORALL n -> n_k
    (let* ((n-k (cadr (wff-formula (car (sequent-node-assumptions (proof-state-focus *ps*)))))))
      (di)  ; peel IMPLIES IH
      (ta 'eq-subst-membership)
      (inst '(FORALL a (FORALL b (FORALL S (IMPLIES (AND (= a b) (IN b S)) (IN a S)))))
            `(SUM r f (succ ,n-k)))
      (inst `(FORALL b (FORALL S (IMPLIES (AND (= (SUM r f (succ ,n-k)) b) (IN b S))
                                           (IN (SUM r f (succ ,n-k)) S))))
            `((ADD r) (SUM r f ,n-k) (f ,n-k)))
      (inst `(FORALL S (IMPLIES (AND (= (SUM r f (succ ,n-k))
                                        ((ADD r) (SUM r f ,n-k) (f ,n-k)))
                                    (IN ((ADD r) (SUM r f ,n-k) (f ,n-k)) S))
                                (IN (SUM r f (succ ,n-k)) S)))
            '(A r))
      (bc `(IMPLIES (AND (= (SUM r f (succ ,n-k))
                             ((ADD r) (SUM r f ,n-k) (f ,n-k)))
                         (IN ((ADD r) (SUM r f ,n-k) (f ,n-k)) (A r)))
                    (IN (SUM r f (succ ,n-k)) (A r))))
      (di)
      (ta 'sum-succ)
      (inst '(FORALL r (FORALL f (FORALL n (IMPLIES (IN n NN)
               (= (SUM r f (succ n)) ((ADD r) (SUM r f n) (f n))))))) 'r)
      (inst '(FORALL f (FORALL n (IMPLIES (IN n NN)
               (= (SUM r f (succ n)) ((ADD r) (SUM r f n) (f n)))))) 'f)
      (inst '(FORALL n (IMPLIES (IN n NN)
               (= (SUM r f (succ n)) ((ADD r) (SUM r f n) (f n))))) n-k)
      (bc `(IMPLIES (IN ,n-k NN)
                    (= (SUM r f (succ ,n-k)) ((ADD r) (SUM r f ,n-k) (f ,n-k)))))
      (ass)
      (ta 'ring-carrier-closed-add)
      (inst '(FORALL r (FORALL a (FORALL b
               (IMPLIES (AND (IS-RING r) (AND (IN a (A r)) (IN b (A r))))
                        (IN ((ADD r) a b) (A r)))))) 'r)
      (inst `(FORALL a (FORALL b
               (IMPLIES (AND (IS-RING r) (AND (IN a (A r)) (IN b (A r))))
                        (IN ((ADD r) a b) (A r))))) `(SUM r f ,n-k))
      (inst `(FORALL b
               (IMPLIES (AND (IS-RING r) (AND (IN (SUM r f ,n-k) (A r)) (IN b (A r))))
                        (IN ((ADD r) (SUM r f ,n-k) b) (A r)))) `(f ,n-k))
      (bc `(IMPLIES (AND (IS-RING r)
                         (AND (IN (SUM r f ,n-k) (A r)) (IN (f ,n-k) (A r))))
                    (IN ((ADD r) (SUM r f ,n-k) (f ,n-k)) (A r))))
      (di) (ass)
      (di) (ass)
      (ta 'fun-apply-type)
      (inst '(FORALL f (FORALL A (FORALL B (FORALL x
               (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B)))))) 'f)
      (inst '(FORALL A (FORALL B (FORALL x
               (IMPLIES (AND (IN f (FUN A B)) (IN x A)) (IN (f x) B))))) 'NN)
      (inst '(FORALL B (FORALL x
               (IMPLIES (AND (IN f (FUN NN B)) (IN x NN)) (IN (f x) B)))) '(A r))
      (inst `(FORALL x (IMPLIES (AND (IN f (FUN NN (A r))) (IN x NN)) (IN (f x) (A r)))) n-k)
      (bc `(IMPLIES (AND (IN f (FUN NN (A r))) (IN ,n-k NN)) (IN (f ,n-k) (A r))))
      (di) (ass) (ass))
    (unless (proof-done? *ps*) (error "sum-type proof incomplete"))))

;;; -----------------------------------------------------------------------
;;; Restrictive ring/field structures (commutative-ring … normed-field)

(check-true "is-commutative-ring-def installed"
  (lambda () (and (lookup-theorem 'is-commutative-ring-def) #t)))
(check-true "is-integral-domain-def installed"
  (lambda () (and (lookup-theorem 'is-integral-domain-def) #t)))
;; FIELD is a shape structure (def-structure-from-clauses), so its IFF
;; axiom is installed under the predicate name IS-FIELD, not is-field-def.
(check-true "IS-FIELD axiom installed"
  (lambda () (and (lookup-theorem 'IS-FIELD) #t)))
(check-true "is-euclidean-ring-def installed"
  (lambda () (and (lookup-theorem 'is-euclidean-ring-def) #t)))
;; NORMED-FIELD is now a shape structure too, so its IFF is installed under
;; the predicate name IS-NORMED-FIELD (matching FIELD's pattern above).
(check-true "IS-NORMED-FIELD axiom installed"
  (lambda () (and (lookup-theorem 'IS-NORMED-FIELD) #t)))
;; The FIELD→INTEGRAL-DOMAIN forgetful relation is installed by the view.
(check-true "FIELD-AS-INTEGRAL-DOMAIN view's typing axiom installed"
  (lambda () (and (lookup-theorem 'FIELD-AS-INTEGRAL-DOMAIN-is-INTEGRAL-DOMAIN) #t)))
(check-true "euclidean-ring-is-integral-domain installed"
  (lambda () (and (lookup-theorem 'euclidean-ring-is-integral-domain) #t)))
(check-true "zz-is-euclidean-ring installed"
  (lambda () (and (lookup-theorem 'zz-is-euclidean-ring) #t)))
(check-true "cc-is-normed-field installed"
  (lambda () (and (lookup-theorem 'cc-is-normed-field) #t)))
;; IS-FIELD's macete unfolds the definition (auto-installed by
;; def-structure-from-clauses under the predicate's own name).
(check-true "IS-FIELD macete unfolds the predicate"
  (lambda ()
    (let ((r (apply-macete 'IS-FIELD (make-wff '(IS-FIELD s)))))
      (and r
           (pair? (wff-formula r))
           (eq? (car (wff-formula r)) 'AND)))))

;;; operation-properties catalog + MATRIX

(check-true "is-associative property installed"
  (lambda () (and (lookup-theorem 'is-associative) #t)))
(check-true "is-commutative property installed"
  (lambda () (and (lookup-theorem 'is-commutative) #t)))
(check-true "is-metric property installed"
  (lambda () (and (lookup-theorem 'is-metric) #t)))
;; IS-GROUP now carries its laws: its definition mentions is-associative.
(check-true "IS-GROUP definition includes the group laws"
  (lambda ()
    (let ((g (lookup-theorem 'IS-GROUP)))
      (and g
           (string-search-forward "is-associative"
                                  (expression->string g) 0)
           #t))))
;; ...and IS-ABELIAN-GROUP additionally includes is-commutative.
(check-true "IS-ABELIAN-GROUP definition includes is-commutative"
  (lambda ()
    (let ((g (lookup-theorem 'IS-ABELIAN-GROUP)))
      (and g
           (string-search-forward "is-commutative"
                                  (expression->string g) 0)
           #t))))

(check-true "matrix-membership installed"
  (lambda () (and (lookup-theorem 'matrix-membership) #t)))
(check-true "matrix-sethood installed"
  (lambda () (and (lookup-theorem 'matrix-sethood) #t)))
(check-true "(IN M (MATRIX S)) accepted as a wff"
  (lambda () (and (make-wff '(IN M (MATRIX S))) #t)))
(check-true "SIZE macete reduces (SIZE M) to [rows, cols]"
  (lambda ()
    (sp (make-wff '(= (SIZE mm) zz)))
    (mac 'SIZE)
    (equal? (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))
            '(= (LIST (LENGTH mm) (LENGTH (NTH 1 mm))) zz))))

;;; RING-PROD and RING-PROD-N

(check-true "ring-prod-is-ring installed"
  (lambda () (and (lookup-theorem 'ring-prod-is-ring) #t)))

(check-true "zero-ring-is-ring installed"
  (lambda () (and (lookup-theorem 'zero-ring-is-ring) #t)))

(check-true "ring-prod-n-zero installed"
  (lambda () (and (lookup-theorem 'ring-prod-n-zero) #t)))

(check-true "ring-prod-n-succ installed"
  (lambda () (and (lookup-theorem 'ring-prod-n-succ) #t)))

(check-true "ring-prod-n-is-ring installed"
  (lambda () (and (lookup-theorem 'ring-prod-n-is-ring) #t)))

;;; -----------------------------------------------------------------------
;;; IS-FUN, DOM, RES, PARTIAL-FUN -- function overhaul (2026-05-16)

(display "\n=== Function overhaul: IS-FUN, DOM, RES, PARTIAL-FUN ===\n")

(check-true "fun-domain-apply-def axiom installed"
  (lambda () (and (lookup-theorem 'fun-domain-apply-def) #t)))

(check-true "is-fun-def axiom installed"
  (lambda () (and (lookup-theorem 'is-fun-def) #t)))

(check-true "dom-membership axiom installed"
  (lambda () (and (lookup-theorem 'dom-membership) #t)))

(check-true "dom-fun-membership axiom installed"
  (lambda () (and (lookup-theorem 'dom-fun-membership) #t)))

(check-true "dom-of-fun axiom installed"
  (lambda () (and (lookup-theorem 'dom-of-fun) #t)))

(check-true "fun-domain-apply-def now iff"
  (lambda ()
    (let ((ax (lookup-theorem 'fun-domain-apply-def)))
      (and ax
           (let walk ((e ax))
             (cond ((not (pair? e)) #f)
                   ((eq? (car e) 'IFF) #t)
                   (else (any walk (cdr e)))))))))

(check-true "(IS-FUN f) accepted in wff position"
  (lambda ()
    (let ((w (make-wff '(IS-FUN f))))
      (and w #t))))

(check-true "(IN x (DOM f)) accepted in wff position"
  (lambda ()
    (let ((w (make-wff '(IN x (DOM f)))))
      (and w #t))))

(check-error "(DOM f) rejected in wff position"
  (lambda () (make-wff '(DOM f))))

(check-true "res-typing axiom installed"
  (lambda () (and (lookup-theorem 'res-typing) #t)))

(check-true "res-apply axiom installed"
  (lambda () (and (lookup-theorem 'res-apply) #t)))

(check-true "res-codomain axiom installed"
  (lambda () (and (lookup-theorem 'res-codomain) #t)))

(check-true "(IN (RES f B) (FUN B)) accepted as wff"
  (lambda () (and (make-wff '(IN (RES f B) (FUN B))) #t)))

(check-error "(RES f B) rejected in wff position"
  (lambda () (make-wff '(RES f B))))

(check-true "partial-fun-membership axiom installed"
  (lambda () (and (lookup-theorem 'partial-fun-membership) #t)))

(check-true "partial-fun-binary-membership axiom installed"
  (lambda () (and (lookup-theorem 'partial-fun-binary-membership) #t)))

(check-true "partial-fun-binary-sethood axiom installed"
  (lambda () (and (lookup-theorem 'partial-fun-binary-sethood) #t)))

(check-true "(IN f (PARTIAL-FUN A)) accepted as wff"
  (lambda () (and (make-wff '(IN f (PARTIAL-FUN A))) #t)))

(check-true "(IN f (PARTIAL-FUN A C)) accepted as wff"
  (lambda () (and (make-wff '(IN f (PARTIAL-FUN A C))) #t)))

(check-error "(PARTIAL-FUN A) rejected in wff position"
  (lambda () (make-wff '(PARTIAL-FUN A))))

;;; -----------------------------------------------------------------------
;;; def-structure NAME-class axiom: associated class is named after structure

(display "\n=== def-structure: associated class is named ===\n")

(check-true "SEMIGROUP-class axiom installed"
  (lambda () (and (lookup-theorem 'SEMIGROUP-class) #t)))

(check-true "MONOID-class axiom installed"
  (lambda () (and (lookup-theorem 'MONOID-class) #t)))

(check-true "GROUP-class axiom installed"
  (lambda () (and (lookup-theorem 'GROUP-class) #t)))

(check-true "RING-class axiom installed"
  (lambda () (and (lookup-theorem 'RING-class) #t)))

(check-true "METRIC-SPACE-class axiom installed"
  (lambda () (and (lookup-theorem 'METRIC-SPACE-class) #t)))

(check-true "(IN r RING) accepted as wff (structure name as class)"
  (lambda () (and (make-wff '(IN r RING)) #t)))

(check-true "forall([s in RING], TRUTH) parses bounded quant over RING"
  (lambda ()
    (and (make-wff-from-string "forall([s in RING], TRUTH)") #t)))

;;; -----------------------------------------------------------------------
;;; BIG-UNION (notes-16 step 1): union over a family of sets
;;;   (BIG-UNION z A body) = union_{z in A} body
;;;   A binder constructor with a bound class variable in body.

(display "\n=== BIG-UNION (notes-16 step 1) ===\n")

;; --- Validation ---
(check-true "(BIG-UNION z A body) accepted as term in IN goal"
  (lambda () (and (make-wff '(IN x (BIG-UNION z NN z))) #t)))

(check-error "BIG-UNION rejected in wff position"
  (lambda () (make-wff '(BIG-UNION z NN z))))

(check-error "BIG-UNION arity rejected"
  (lambda () (make-wff '(IN x (BIG-UNION z NN)))))

(check-error "BIG-UNION non-symbol bound var rejected"
  (lambda () (make-wff '(IN x (BIG-UNION 0 NN NN)))))

;; --- Free variables (z bound in body, free in A) ---
(check "free-vars: z in body is bound; A is free"
  (lambda () (sort (free-vars '(BIG-UNION z A z))
                   (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
  '(A))

(check "free-vars: vars only in A are free"
  (lambda () (sort (free-vars '(BIG-UNION z (UNION A B) z))
                   (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
  '(A B))

;; --- Substitution (capture-avoiding) ---
(check "subst-free: leaves body alone when bound var = subst var"
  (lambda () (subst-free 'z 'w '(BIG-UNION z A z)))
  '(BIG-UNION z A z))

(check "subst-free: substitutes into A"
  (lambda () (subst-free 'A 'NN '(BIG-UNION z A z)))
  '(BIG-UNION z NN z))

;; Capture-avoiding: substituting w for q in (BIG-UNION z A (PAIR z q)) where
;; w = z would otherwise capture; expect alpha-renamed binder.
(check-true "subst-free: renames bound var to avoid capture"
  (lambda ()
    (let ((result (subst-free 'q 'z '(BIG-UNION z A (PAIR z q)))))
      ;; result must NOT have raw `z` paired with itself; the binder is renamed
      (and (pair? result) (eq? (car result) 'BIG-UNION)
           ;; bound var should NOT be z (it would capture)
           (not (eq? (cadr result) 'z))))))

;; --- Alpha-equivalence ---
(check-true "alpha-equiv: (BIG-UNION x A x) ~ (BIG-UNION y A y)"
  (lambda () (alpha-equiv? '(BIG-UNION x A x) '(BIG-UNION y A y))))

(check-false "alpha-equiv: differs in A"
  (lambda () (alpha-equiv? '(BIG-UNION x A x) '(BIG-UNION y B y))))

;; --- Primitive inferences ---
(check-proof "pi-big-union-sethood: posts (IN A SET) + family-of-sets subgoal"
  (lambda ()
    (sp (make-wff '(IN (BIG-UNION z NN NN) SET)))
    (let ((sqn (proof-state-focus *ps*)))
      (let ((r (pi-big-union-sethood! sqn)))
        (or r (error "pi-big-union-sethood! failed"))))))

(check-proof "pi-big-union-mem-intro: witness reduces to two subgoals"
  (lambda ()
    (sp (make-wff '(IN 0 (BIG-UNION z NN NN))))
    (let ((sqn (proof-state-focus *ps*)))
      (let ((r (pi-big-union-mem-intro! sqn '0)))
        (or r (error "pi-big-union-mem-intro! failed"))))))

(check-proof "pi-big-union-mem-elim: eigenvariable gains two new assumptions"
  (lambda ()
    (declare-local-context '(IN 0 (BIG-UNION z NN NN)) 'big-union-mem-elim-ctx)
    (sp (make-wff 'TRUTH))
    (let ((sqn (proof-state-focus *ps*)))
      (let ((r (pi-big-union-mem-elim! sqn '(IN 0 (BIG-UNION z NN NN)))))
        (undeclare-local-context 'big-union-mem-elim-ctx)
        (or r (error "pi-big-union-mem-elim! failed"))))))

(check "pi-big-union-sethood: refuses non-BIG-UNION goal"
  (lambda ()
    (sp (make-wff '(IN 0 NN)))
    (pi-big-union-sethood! (proof-state-focus *ps*)))
  #f)

;;; -----------------------------------------------------------------------
;;; COMM-MONOID + SUM-SET + PROD-SET (notes-16 step 2)

(display "\n=== COMM-MONOID structure (notes-16 step 2) ===\n")

(check-true "IS-COMM-MONOID axiom installed"
  (lambda () (and (lookup-theorem 'IS-COMM-MONOID) #t)))

(check-true "COMM-MONOID-class axiom installed"
  (lambda () (and (lookup-theorem 'COMM-MONOID-class) #t)))

(check-true "comm-monoid-is-monoid (subtype) axiom installed"
  (lambda () (and (lookup-theorem 'comm-monoid-is-monoid) #t)))

(check-true "comm-monoid-mul-comm axiom installed"
  (lambda () (and (lookup-theorem 'comm-monoid-mul-comm) #t)))

(check-true "(IN cm COMM-MONOID) accepted as wff"
  (lambda () (and (make-wff '(IN cm COMM-MONOID)) #t)))

(display "\n=== ABELIAN-GROUP structure (analysis-trajectory step 1) ===\n")

(check-true "IS-ABELIAN-GROUP axiom installed"
  (lambda () (and (lookup-theorem 'IS-ABELIAN-GROUP) #t)))

(check-true "ABELIAN-GROUP-class axiom installed"
  (lambda () (and (lookup-theorem 'ABELIAN-GROUP-class) #t)))

(check-true "abelian-group-is-group (subtype) axiom installed"
  (lambda () (and (lookup-theorem 'abelian-group-is-group) #t)))

(check-true "abelian-group-mul-comm axiom installed"
  (lambda () (and (lookup-theorem 'abelian-group-mul-comm) #t)))

(check-true "(IN ag ABELIAN-GROUP) accepted as wff"
  (lambda () (and (make-wff '(IN ag ABELIAN-GROUP)) #t)))

(display "\n=== SUM-SET (notes-16 step 2) ===\n")

(check-true "sum-set-empty axiom installed"
  (lambda () (and (lookup-theorem 'sum-set-empty) #t)))

(check-true "sum-set-singleton axiom installed"
  (lambda () (and (lookup-theorem 'sum-set-singleton) #t)))

(check-true "sum-set-disjoint-union axiom installed"
  (lambda () (and (lookup-theorem 'sum-set-disjoint-union) #t)))

(check-true "sum-set-type axiom installed"
  (lambda () (and (lookup-theorem 'sum-set-type) #t)))

(check-true "(SUM-SET r S f) accepted in term position"
  (lambda () (and (make-wff '(IN (SUM-SET r S f) (A r))) #t)))

(check-error "SUM-SET rejected in wff position"
  (lambda () (make-wff '(SUM-SET r S f))))

(display "\n=== PROD-SET (notes-16 step 2) ===\n")

(check-true "prod-set-empty axiom installed"
  (lambda () (and (lookup-theorem 'prod-set-empty) #t)))

(check-true "prod-set-singleton axiom installed"
  (lambda () (and (lookup-theorem 'prod-set-singleton) #t)))

(check-true "prod-set-disjoint-union axiom installed"
  (lambda () (and (lookup-theorem 'prod-set-disjoint-union) #t)))

(check-true "prod-set-type axiom installed"
  (lambda () (and (lookup-theorem 'prod-set-type) #t)))

(check-true "(PROD-SET cm S f) accepted in term position"
  (lambda () (and (make-wff '(IN (PROD-SET cm S f) (A cm))) #t)))

(check-error "PROD-SET rejected in wff position"
  (lambda () (make-wff '(PROD-SET cm S f))))

(display "\n=== SUM-AG (analysis-trajectory step 2) ===\n")

(check-true "sum-ag-zero axiom installed"
  (lambda () (and (lookup-theorem 'sum-ag-zero) #t)))

(check-true "sum-ag-succ axiom installed"
  (lambda () (and (lookup-theorem 'sum-ag-succ) #t)))

(check-true "sum-ag-type axiom installed"
  (lambda () (and (lookup-theorem 'sum-ag-type) #t)))

(check-true "sum-ag-singleton axiom installed"
  (lambda () (and (lookup-theorem 'sum-ag-singleton) #t)))

;;; Library theorems proved at load time (proven-theorems.scm).
(check-true "delete-at-in-fun axiom installed"
  (lambda () (and (lookup-theorem 'delete-at-in-fun) #t)))

;; ord-segment-succ-monotone, ag-mul-rearrange, and sum-ag-splice-out were
;; intermediate lemmas ARCHIVED (deliberately not PSS-promoted) in the
;; 2026-05-27 triage -- "pure technical machinery with no anticipated
;; standalone use" (see archive/proven-theorems-archive.scm).  Their old
;; "proved + installed" checks were removed here: lookup-theorem throws on
;; an unknown name, so a stale check aborted the entire suite.  The headline
;; result they fed, sum-ag-permutation-invariance, is PSS-promoted and tested
;; below.

(check-true "sum-ag-permutation-invariance proved + installed"
  (lambda () (and (lookup-theorem 'sum-ag-permutation-invariance) #t)))

(check-true "(SUM-AG ag f n) accepted in term position"
  (lambda () (and (make-wff '(IN (SUM-AG ag f n) (A ag))) #t)))

(check-true "group-identity-in installed"
  (lambda () (and (lookup-theorem 'group-identity-in) #t)))

(check-true "enum-fam-in-fun proved + installed"
  (lambda () (and (lookup-theorem 'enum-fam-in-fun) #t)))

(check-true "fin-enum-is-bijection proved + installed"
  (lambda () (and (lookup-theorem 'fin-enum-is-bijection) #t)))

(check-true "(FINSUM ag f S) accepted in term position"
  (lambda () (and (make-wff '(IN (FINSUM ag f S) (A ag))) #t)))

(check-true "finsum-well-defined proved + installed"
  (lambda () (and (lookup-theorem 'finsum-well-defined) #t)))

(check-true "union-empty-left proved + installed"
  (lambda () (and (lookup-theorem 'union-empty-left) #t)))

;; Prenex fix (macetes.scm prenex-positive): pairing-membership buries its
;; FORALL x under the IMPLIES; theorem->elementary-macete must prenex-normalize
;; before strip-foralls so the membership IFF still yields a real rewrite.
(check-true "pairing-membership yields a working macete (prenex fix)"
  (lambda ()
    (let ((r (apply-macete 'pairing-membership
              (make-wff '(IMPLIES (AND (IN a SET) (IN b SET))
                                  (IN c (PAIR a b)))))))
      (and r
           (equal? (wff-formula r)
                   '(IMPLIES (AND (IN a SET) (IN b SET))
                             (OR (= c a) (= c b))))))))

(check-true "card-singleton proved + installed"
  (lambda () (and (lookup-theorem 'card-singleton) #t)))

(check-true "finsum-empty proved + installed"
  (lambda () (and (lookup-theorem 'finsum-empty) #t)))

(check-true "finsum-singleton proved + installed"
  (lambda () (and (lookup-theorem 'finsum-singleton) #t)))

(check-true "finsum-type proved + installed"
  (lambda () (and (lookup-theorem 'finsum-type) #t)))

;; finsum-congruence was dropped 2026-05-27 as a redundant special case of
;; fun-domain-extensionality.  No replacement check: callers should cite
;; fun-domain-extensionality directly.

(display "\n=== BIJECTION + INVERSE-BIJ (analysis-trajectory step 3a/b) ===\n")

(check-true "bijection-membership-iff axiom installed"
  (lambda () (and (lookup-theorem 'bijection-membership-iff) #t)))

(check-true "bijection-set-iff axiom installed"
  (lambda () (and (lookup-theorem 'bijection-set-iff) #t)))

(check-true "bijection-in-fun axiom installed"
  (lambda () (and (lookup-theorem 'bijection-in-fun) #t)))

(check-true "bijection-injective axiom installed"
  (lambda () (and (lookup-theorem 'bijection-injective) #t)))

(check-true "bijection-surjective axiom installed"
  (lambda () (and (lookup-theorem 'bijection-surjective) #t)))

(check-true "inverse-bij-in-fun axiom installed"
  (lambda () (and (lookup-theorem 'inverse-bij-in-fun) #t)))

(check-true "inverse-bij-left axiom installed"
  (lambda () (and (lookup-theorem 'inverse-bij-left) #t)))

(check-true "inverse-bij-right axiom installed"
  (lambda () (and (lookup-theorem 'inverse-bij-right) #t)))

(check-true "inverse-bij-is-bijection axiom installed"
  (lambda () (and (lookup-theorem 'inverse-bij-is-bijection) #t)))

(check-true "bijection-compose axiom installed"
  (lambda () (and (lookup-theorem 'bijection-compose) #t)))

(check-true "bijection-identity axiom installed"
  (lambda () (and (lookup-theorem 'bijection-identity) #t)))

(check-true "(IN phi (BIJECTION X Y)) accepted as wff"
  (lambda () (and (make-wff '(IN phi (BIJECTION X Y))) #t)))

(check-true "(IN (INVERSE-BIJ phi X Y) (FUN Y X)) accepted as wff"
  (lambda () (and (make-wff '(IN (INVERSE-BIJ phi X Y) (FUN Y X))) #t)))

(check-true "delete-at-below-k axiom installed"
  (lambda () (and (lookup-theorem 'delete-at-below-k) #t)))

(check-true "delete-at-above-k axiom installed"
  (lambda () (and (lookup-theorem 'delete-at-above-k) #t)))

(check-true "delete-at-is-bijection axiom installed"
  (lambda () (and (lookup-theorem 'delete-at-is-bijection) #t)))

(check-true "((DELETE-AT h k) i) accepted in term position"
  (lambda () (and (make-wff '(= ((DELETE-AT h k) i) (h i))) #t)))

;;; -----------------------------------------------------------------------
;;; Basic rings (notes-16 steps 3+4): officialize ZZ/QQ/RR/CC as rings

(display "\n=== Basic rings (notes-16 steps 3+4) ===\n")

;; --- Binary operator apply axioms ---
(check-true "binplus-apply installed"
  (lambda () (and (lookup-theorem 'binplus-apply) #t)))
(check-true "bintimes-apply installed"
  (lambda () (and (lookup-theorem 'bintimes-apply) #t)))
(check-true "binneg-apply installed"
  (lambda () (and (lookup-theorem 'binneg-apply) #t)))

;; --- Typing axioms: binplus, bintimes in all 5 domains; binneg in 4 ---
(check-true "binplus-in-fun-nn installed"
  (lambda () (and (lookup-theorem 'binplus-in-fun-nn) #t)))
(check-true "binplus-in-fun-cc installed"
  (lambda () (and (lookup-theorem 'binplus-in-fun-cc) #t)))
(check-true "bintimes-in-fun-rr installed"
  (lambda () (and (lookup-theorem 'bintimes-in-fun-rr) #t)))
(check-true "binneg-in-fun-zz installed"
  (lambda () (and (lookup-theorem 'binneg-in-fun-zz) #t)))

;; --- Ring instance definitions ---
(check-true "zz-ring-def installed"
  (lambda () (and (lookup-theorem 'zz-ring-def) #t)))
(check-true "qq-ring-def installed"
  (lambda () (and (lookup-theorem 'qq-ring-def) #t)))
(check-true "rr-ring-def installed"
  (lambda () (and (lookup-theorem 'rr-ring-def) #t)))
(check-true "cc-ring-def installed"
  (lambda () (and (lookup-theorem 'cc-ring-def) #t)))

;; --- IS-RING(*-RING): only the genuine 6-tuples ZZ/QQ ---
(check-true "zz-is-ring installed"
  (lambda () (and (lookup-theorem 'zz-is-ring) #t)))
(check-true "qq-is-ring installed"
  (lambda () (and (lookup-theorem 'qq-is-ring) #t)))
;; RR-RING/CC-RING are 7-tuple NORMED-FIELDs: asserting the length-6 IS-RING
;; on them was a flat contradiction (6 = 7).  These must stay REMOVED.
;; lookup-theorem raises on an absent name, so probe the axiom store directly.
(check-true "rr-is-ring removed (was length 6=7 unsound)"
  (lambda () (not (assq 'rr-is-ring (theory-axioms *current-theory*)))))
(check-true "cc-is-ring removed (was length 6=7 unsound)"
  (lambda () (not (assq 'cc-is-ring (theory-axioms *current-theory*)))))
(check-true "qq-is-field removed (QQ-RING is 6-tuple, FIELD is 8-slot)"
  (lambda () (not (assq 'qq-is-field (theory-axioms *current-theory*)))))
(check-true "normed-field-is-commutative-ring removed (7=>6 unsound)"
  (lambda () (not (assq 'normed-field-is-commutative-ring (theory-axioms *current-theory*)))))
;; Sound replacements: RR/CC as normed fields; QQ as the 8-tuple QQ-FIELD;
;; ring-world access for RR/CC via the NORMED-FIELD-AS-* view projections.
(check-true "rr-is-normed-field installed"
  (lambda () (and (lookup-theorem 'rr-is-normed-field) #t)))
(check-true "cc-is-normed-field installed"
  (lambda () (and (lookup-theorem 'cc-is-normed-field) #t)))
(check-true "qq-field-is-field installed (8-tuple QQ-FIELD)"
  (lambda () (and (lookup-theorem 'qq-field-is-field) #t)))
(check-true "(IN QQ-FIELD FIELD) accepted as wff"
  (lambda () (and (make-wff '(IN QQ-FIELD FIELD)) #t)))

;; --- Enfranchised refinement classes: NAME-class axioms + bounded membership ---
(check-true "commutative-ring-class installed"
  (lambda () (and (lookup-theorem 'commutative-ring-class) #t)))
(check-true "integral-domain-class installed"
  (lambda () (and (lookup-theorem 'integral-domain-class) #t)))
(check-true "euclidean-ring-class installed"
  (lambda () (and (lookup-theorem 'euclidean-ring-class) #t)))
(check-true "(IN ZZ-RING COMMUTATIVE-RING) accepted as wff"
  (lambda () (and (make-wff '(IN ZZ-RING COMMUTATIVE-RING)) #t)))

;; --- MPOW: monoid power x^n, and its ZZ extension on abelian groups ---
(check-true "abelian-group-as-monoid view installed"
  (lambda () (and (lookup-theorem 'abelian-group-as-monoid-is-monoid) #t)))
(for-each
  (lambda (n)
    (check-true (string-append (symbol->string n) " installed")
      (lambda () (and (lookup-theorem n) #t))))
  '(mpow-zero mpow-succ mpow-one mpow-type mpow-add mpow-mult
    zz-act-nonneg zz-act-neg zz-act-zero zz-act-one zz-act-type
    zz-act-neg-sign zz-act-add zz-act-distrib zz-act-assoc))
(check-true "(MPOW M X N) accepted as wff"
  (lambda () (and (make-wff '(IN (MPOW M X N) (A M))) #t)))
(check-true "(ZZ-ACT G K A) accepted as wff"
  (lambda () (and (make-wff '(IN (ZZ-ACT G K A) (A G))) #t)))

;; --- NN as comm-monoid under addition ---
(check-true "nn-add-monoid-def installed"
  (lambda () (and (lookup-theorem 'nn-add-monoid-def) #t)))
(check-true "nn-add-monoid-is-comm-monoid installed"
  (lambda () (and (lookup-theorem 'nn-add-monoid-is-comm-monoid) #t)))

;; --- Wff validation of the new symbols ---
(check-true "(binplus x y) accepted as term"
  (lambda () (and (make-wff '(IN (binplus x y) NN)) #t)))
(check-true "(IN ZZ-RING RING) accepted as wff"
  (lambda () (and (make-wff '(IN ZZ-RING RING)) #t)))

;; --- specialize-structure transports generic ring theorems to ZZ-RING ---
(check-true "specialize-structure ZZ-RING brings ring-add-comm-zz-ring"
  (lambda ()
    (specialize-structure 'ZZ-RING 'RING 'zz-is-ring)
    (and (lookup-theorem 'ring-add-comm-zz-ring) #t)))

;;; -----------------------------------------------------------------------
;;; Extended reals RR* (notes-16 step 6)

(display "\n=== Extended reals RR* (notes-16 step 6) ===\n")

(check-true "rr-star-membership installed"
  (lambda () (and (lookup-theorem 'rr-star-membership) #t)))
(check-true "rr-subset-rr-star installed"
  (lambda () (and (lookup-theorem 'rr-subset-rr-star) #t)))
(check-true "pos-inf-in-rr-star installed"
  (lambda () (and (lookup-theorem 'pos-inf-in-rr-star) #t)))
(check-true "neg-inf-in-rr-star installed"
  (lambda () (and (lookup-theorem 'neg-inf-in-rr-star) #t)))
(check-true "pos-inf-neq-neg-inf installed"
  (lambda () (and (lookup-theorem 'pos-inf-neq-neg-inf) #t)))
(check-true "pos-inf-not-in-rr installed"
  (lambda () (and (lookup-theorem 'pos-inf-not-in-rr) #t)))
(check-true "neg-inf-not-in-rr installed"
  (lambda () (and (lookup-theorem 'neg-inf-not-in-rr) #t)))
(check-true "pos-inf-upper-bound installed"
  (lambda () (and (lookup-theorem 'pos-inf-upper-bound) #t)))
(check-true "neg-inf-lower-bound installed"
  (lambda () (and (lookup-theorem 'neg-inf-lower-bound) #t)))

;; --- Wff validation: RR*, POS-INF, NEG-INF accepted as terms/constants ---
(check-true "(IN POS-INF RR*) accepted as wff"
  (lambda () (and (make-wff '(IN POS-INF RR*)) #t)))
(check-true "(IN NEG-INF RR*) accepted as wff"
  (lambda () (and (make-wff '(IN NEG-INF RR*)) #t)))
(check-true "(<= NEG-INF POS-INF) accepted as wff"
  (lambda () (and (make-wff '(<= NEG-INF POS-INF)) #t)))

;;; -----------------------------------------------------------------------
;;; Metric completeness (IS-CAUCHY-SEQ / CONVERGES / IS-COMPLETE) and the
;;; normed-field -> metric-space bridge.

(display "\n=== Metric completeness + normed-field metric bridge ===\n")

;; Vocabulary registered.
(check-true "is-cauchy-seq defined"
  (lambda () (and (assq 'is-cauchy-seq (theory-definitions *current-theory*)) #t)))
(check-true "converges-to defined"
  (lambda () (and (assq 'converges-to (theory-definitions *current-theory*)) #t)))
(check-true "is-complete defined"
  (lambda () (and (assq 'is-complete (theory-definitions *current-theory*)) #t)))
(check-true "complete-cauchy-converges installed"
  (lambda () (and (lookup-theorem 'complete-cauchy-converges) #t)))
(check-true "rr-complete = IS-COMPLETE(RR-MS) installed"
  (lambda () (and (lookup-theorem 'rr-complete) #t)))
(check-true "cc-complete = IS-COMPLETE(CC-MS) installed"
  (lambda () (and (lookup-theorem 'cc-complete) #t)))
(check-true "nf-metric-space-is-metric-space installed"
  (lambda () (and (lookup-theorem 'nf-metric-space-is-metric-space) #t)))

;; The IS-COMPLETE definition fires on a goal: completeness criterion.
(check-proof "is-complete criterion: metric space where every Cauchy seq converges is complete"
  (lambda ()
    (sp (make-wff '(FORALL s (IMPLIES (AND (IS-METRIC-SPACE s)
                                           (FORALL f (IMPLIES (IS-CAUCHY-SEQ s f)
                                                              (CONVERGES s f))))
                                      (IS-COMPLETE s)))))
    (di) (di)
    (mac 'is-complete)
    (ass)
    (unless (proof-done? *ps*) (error "is-complete criterion: proof did not close"))))

;; IS-COMPLETE used in a real backchain: every Cauchy sequence in RR-MS
;; converges, via rr-complete + complete-cauchy-converges.
(check-proof "RR-MS complete: Cauchy seq converges (uses IS-COMPLETE)"
  (lambda ()
    (sp (make-wff '(FORALL f (IMPLIES (IS-CAUCHY-SEQ RR-MS f) (CONVERGES RR-MS f)))))
    (di) (di)
    (bc* 'complete-cauchy-converges)
    (ta 'rr-complete) (ass)
    (ass)
    (unless (proof-done? *ps*) (error "RR-MS complete: proof did not close"))))

;;; -----------------------------------------------------------------------
;;; Commutative ring-simplify (crs): multiset-monomial normal form.

(display "\n=== Commutative ring-simplify (crs) ===\n")

;; crs peels the typed FORALL chain itself -- no prior (di) needed.
(check-proof "crs closes commutativity x*y = y*x over ZZ"
  (lambda ()
    (sp (make-wff '(FORALL x (IMPLIES (IN x ZZ)
                    (FORALL y (IMPLIES (IN y ZZ)
                      (= (* x y) (* y x))))))))
    (crs)
    (unless (proof-done? *ps*) (error "crs: commutativity did not close"))))

(check-proof "crs closes (x+y)*(x+y) = x*x + 2*x*y + y*y over ZZ"
  (lambda ()
    (sp (make-wff '(FORALL x (IMPLIES (IN x ZZ)
                    (FORALL y (IMPLIES (IN y ZZ)
                      (= (* (+ x y) (+ x y))
                         (+ (* x x) (+ (* 2 (* x y)) (* y y))))))))))
    (crs)
    (unless (proof-done? *ps*) (error "crs: distributive expansion did not close"))))

(check-true "comm-ring-simplify warrant recorded"
  (lambda () (and (warrant-of 'comm-ring-simplify) #t)))

;;; -----------------------------------------------------------------------
;;; Metric topology: open sets + open-preimage characterisation of continuity.

(display "\n=== Metric topology: open sets + open-preimage ===\n")

(check-true "IS-OPEN predicate installed"
  (lambda () (and (lookup-theorem 'IS-OPEN) #t)))
(check-true "PREIMAGE membership installed"
  (lambda () (and (lookup-theorem 'preimage-membership) #t)))
(check-true "empty-is-open support installed"
  (lambda () (and (lookup-theorem 'empty-is-open) #t)))
(check-true "carrier-is-open support installed"
  (lambda () (and (lookup-theorem 'carrier-is-open) #t)))
(check-true "ball-is-open support installed"
  (lambda () (and (lookup-theorem 'ball-is-open) #t)))
(check-true "union-of-opens-open support installed"
  (lambda () (and (lookup-theorem 'union-of-opens-open) #t)))
(check-true "inter-of-opens-open support installed"
  (lambda () (and (lookup-theorem 'inter-of-opens-open) #t)))
(check-true "continuous-implies-open-preimage support installed"
  (lambda () (and (lookup-theorem 'continuous-implies-open-preimage) #t)))
(check-true "open-preimage-implies-continuous support installed"
  (lambda () (and (lookup-theorem 'open-preimage-implies-continuous) #t)))
(check-true "ball-is-open carries a warrant"
  (lambda () (and (warrant-of 'ball-is-open) #t)))

;;; -----------------------------------------------------------------------
;;; describe-structure cards: instances vs refinement classes

(display "\n=== describe-structure cards (instance vs refinement) ===\n")

(define (card-str name)
  (with-output-to-string (lambda () (structure-card-md name))))

;; Instance cards: labelled "Instance", show membership witness + tuple, and
;; must NOT fall back to the empty "no stored characteristic law" line.
(check-true "qq-field card rendered as Instance"
  (lambda () (and (string-search-forward "Instance" (card-str 'qq-field) 0) #t)))
(check-true "qq-field card shows membership witness qq-field-is-field"
  (lambda () (and (string-search-forward "qq-field-is-field" (card-str 'qq-field) 0) #t)))
(check-false "qq-field card has no empty-law fallback"
  (lambda () (and (string-search-forward "no stored characteristic law"
                                         (card-str 'qq-field) 0) #t)))
;; RR-RING's card shows normed-field membership and NOT a (removed) ring one.
(check-true "rr-ring card: member of normed-field"
  (lambda () (and (string-search-forward "is-normed-field" (card-str 'rr-ring) 0) #t)))
(check-false "rr-ring card: not a ring member (soundness fix, visible)"
  (lambda () (and (string-search-forward "is-ring" (card-str 'rr-ring) 0) #t)))
;; Refinement classes still render as refinements (unchanged branch).
(check-true "commutative-ring card still a refinement"
  (lambda () (and (string-search-forward "refinement" (card-str 'commutative-ring) 0) #t)))

;;; -----------------------------------------------------------------------
;;; IF -- conditional term former and its two kernel reduction rules

(display "\n=== IF: conditional term ===\n")

(check-true "(IF p a b) accepted as a term"
  (lambda () (and (make-wff '(= (IF (IN x NN) x 0) y)) #t)))

(check-error "(IF p a b) rejected in wff position"
  (lambda () (make-wff '(IF (IN x NN) x 0))))

(check-true "if-true: condition holds, reduces to then-branch"
  (lambda ()
    (sp (make-wff '(IMPLIES (IN x NN) (= (IF (IN x NN) x 0) x))))
    (di)
    (if-true '(IF (IN x NN) x 0))
    (let ((use (car (reverse (dg-sequent-nodes (proof-state-dg *ps*))))))
      (ass)
      (set-proof-state-focus! *ps* use)
      (ass))
    (null? (dg-ungrounded-nodes (proof-state-dg *ps*)))))

(check-true "if-false: condition fails, reduces to else-branch"
  (lambda ()
    (sp (make-wff '(IMPLIES (NOT (IN x NN)) (= (IF (IN x NN) x 0) 0))))
    (di)
    (if-false '(IF (IN x NN) x 0))
    (let ((use (car (reverse (dg-sequent-nodes (proof-state-dg *ps*))))))
      (ass)
      (set-proof-state-focus! *ps* use)
      (ass))
    (null? (dg-ungrounded-nodes (proof-state-dg *ps*)))))

;;; -----------------------------------------------------------------------
;;; bc* -- matching backchain (interactive.scm)

(check-true "bc*: applies a single-implication theorem (handler form)"
  (lambda ()
    (sp (make-wff '(IMPLIES (IS-ABELIAN-GROUP gg) (IS-GROUP gg))))
    (di)
    (bc* 'abelian-group-is-group () (ass))
    (proof-done? *ps*)))

(check-true "bc*: nested-implication theorem, subgoals dispatched in tree order"
  (lambda ()
    (sp (make-wff
         '(IMPLIES (IN nn0 NN)
          (IMPLIES (IS-GROUP gg0)
          (IMPLIES (IN ph0 (FUN (ORD-SEGMENT nn0) ss0))
          (IMPLIES (IN ff0 (FUN ss0 (A gg0)))
            (IN (ENUM-FAM gg0 ff0 ph0 nn0) (FUN NN (A gg0)))))))))
    (di) (di) (di) (di)
    ;; S occurs only in the antecedents, so it must be supplied explicitly.
    (bc* 'enum-fam-in-fun ((S 'ss0)) (ass) (ass) (ass) (ass))
    (proof-done? *ps*)))

(check-true "bc*: conclusion mismatch warns and leaves the proof open"
  (lambda ()
    (sp (make-wff '(IN (succ 0) NN)))
    (bc* 'abelian-group-is-group)
    (not (proof-done? *ps*))))

;; Variable-headed conclusion: fun-apply-type's (IN (f x) B) has f a schema
;; var.  bc* matches it via *match-var-head* (macetes.scm).
(check-true "bc*: applies a variable-headed-conclusion theorem (fun-apply-type)"
  (lambda ()
    (sp (make-wff '(IMPLIES (AND (IN ff (FUN aa bb)) (IN xx aa))
                            (IN (ff xx) bb))))
    (di)
    (ai '(AND (IN ff (FUN aa bb)) (IN xx aa)))
    (bc* 'fun-apply-type ((A 'aa)) (begin (di) (ass-all)))
    (proof-done? *ps*)))

;;; -----------------------------------------------------------------------
;;; Summary

(newline)
(display "=== SUMMARY: ")
(display *pass-count*) (display " passed, ")
(display *fail-count*) (display " failed ===\n")
