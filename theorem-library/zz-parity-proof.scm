;;; zz-parity-proof.scm -- parity on the INTEGERS, lifted from NN.
;;;
;;; The engine is theorem-library/nn-parity-proof.scm: on the naturals, every
;;; number is 2k or succ(2k) (nn-parity), and 2x is never succ(2y)
;;; (nn-parity-exclusive).  This file carries both to ZZ, where the extra case is
;;; the negatives -- and that is exactly what zz-generated-by-nn (every integer
;;; is n or -n, structure-library/zz-arith.scm) delivers.
;;;
;;;   EVEN(x)  :=  forsome k in ZZ. x = 2*k
;;;   ODD(x)   :=  forsome k in ZZ. x = 2*k + 1
;;;
;;;   zz-parity           every integer is EVEN or ODD          (dichotomy)
;;;   zz-not-even-and-odd  no integer is both                    (exclusivity)
;;;   zz-even-iff-not-odd  EVEN(x) <=> not ODD(x)               (the two together)
;;;   zz-odd-mul-odd       ODD(x) and ODD(y) => ODD(x*y)         (crs)
;;;   zz-even-mul          EVEN(x) => EVEN(x*y)                  (crs)
;;;   zz-odd-sq-odd        ODD(x) => ODD(x*x)                    (instance)
;;;   zz-even-sq-even      EVEN(x*x) => EVEN(x)                  (contrapositive)
;;;
;;; The multiplicative facts are ring identities over typed generators, so `crs'
;;; decides each in one move -- including the negatives, since crs speaks the `-'
;;; surface (checked: -(2k+1) = 2(-k-1)+1).

(define (zp-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (zp-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (zp-any pred lst)
  (let loop ((l lst)) (cond ((null? l) #f) ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (zp-goalof s) (wff-formula (sequent-node-assertion s)))

(define (zp-from-context!)
  (let ((g (zp-goal)))
    (cond
      ((and (pair? g) (eq? (car g) 'AND))
       (for-each (lambda (k) (dk-focus! k) (zp-from-context!)) (dk-opened (lambda () (di)))))
      ((and (pair? g) (eq? (car g) 'IN) (number? (cadr g))) (arith))  ; ground IN, any domain
      (else (ass)))))

;; (zp-close2! a b AX) -- given (IN a ZZ),(IN b ZZ) reachable from context, land
;; (IN (a OP b) ZZ) via closure axiom AX, returning focus to the main branch.
;; Kills the AND-antecedent friction: cut the conjunction, close it from context
;; (ground pieces self-prove), then the closure fact detaches in one go.
(define (zp-close2! a b ax)
  (zp-cut! (list 'AND (list 'IN a 'ZZ) (list 'IN b 'ZZ)))
  (fact ax a b))

(define (zp-cut! form #!optional thunk)
  (let* ((new  (dk-opened (lambda () (cut form))))
         (side (or (zp-any (lambda (s) (alpha-equiv? (zp-goalof s) form)) new)
                   (error "zp-cut!: no side goal for" form)))
         (main (or (zp-any (lambda (s) (not (eq? s side))) new)
                   (error "zp-cut!: no main branch for" form))))
    (dk-focus! side)
    (if (default-object? thunk) (zp-from-context!) (thunk))
    (dk-focus! main)
    main))

(define (zp-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** zz-parity: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (zp-goalof l))) (newline)
                    (for-each (lambda (w) (display "      | ")
                                (display (expression->string (wff-formula w))) (newline))
                              (list-head (sequent-node-assumptions l)
                                         (min 6 (length (sequent-node-assumptions l))))))
                  (proof-open-goals *ps*))
        (error "zz-parity: unfinished" name))))

;;; -----------------------------------------------------------------------
(def-predicate 'EVEN '(x) '(FORSOME k (AND (IN k ZZ) (= x (* 2 k)))))
(def-predicate 'ODD  '(x) '(FORSOME k (AND (IN k ZZ) (= x (+ (* 2 k) 1)))))
;; def-predicate registers the definition but installs no CITEABLE macete (it
;; goes to theory-definitions, not *theorem-table*), so mac-h 'EVEN cannot find
;; it.  Install the defining IFF as a named theorem -- definitional provenance,
;; so it carries no debt -- and cite THAT for both mac (goals) and mac-h (hyps).
(fluid-let ((*current-provenance* 'definitional))
  (install-theorem! 'even-def
    '(FORALL x (IFF (EVEN x) (FORSOME k (AND (IN k ZZ) (= x (* 2 k)))))))
  (install-theorem! 'odd-def
    '(FORALL x (IFF (ODD x) (FORSOME k (AND (IN k ZZ) (= x (+ (* 2 k) 1))))))))

;;; =======================================================================
;;; zz-parity : every integer is EVEN or ODD.
;;;
;;; a = n or a = -n (zz-generated-by-nn).  In the positive case nn-parity makes n
;;; even or odd as a NATURAL; we push that witness up to ZZ (NN <= ZZ) and copy
;;; the equation.  In the negative case an even n gives an even -n
;;; (-(2k) = 2(-k)), and an odd n gives an odd -n up to a shift
;;; (-(2k+1) = 2(-k-1)+1) -- both `crs' identities.
(sp (make-wff '(FORALL a (IMPLIES (IN a ZZ) (OR (EVEN a) (ODD a))))))
(di)(di)
(fact 'zz-generated-by-nn 'a)            ; forsome n in NN. a = n or a = -n
(define zp-gen
  (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (zp-asms))
      (error "zz-parity: generator fact did not land")))
(ai zp-gen)                              ; skolemize n
(define zp-nconj
  (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                               (pair? (caddr f)) (eq? (car (caddr f)) 'OR))) (zp-asms))
      (error "zz-parity: n-body did not land")))
(ai zp-nconj)                            ; (IN n NN) and (a = n or a = -n)
(define zp-nn
  (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'NN))) (zp-asms))
      (error "zz-parity: no (IN n NN)")))
(define zp-n (cadr zp-nn))               ; the eigenvariable n
(define zp-nor
  (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'OR))) (zp-asms))
      (error "zz-parity: no a=n / a=-n split")))
;; n in ZZ, and (from nn-parity) n is 2w or succ(2w) as a natural.
(fact 'nn-subset-zz zp-n)
(fact 'nn-parity zp-n)
(define zp-par
  (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (zp-asms))
      (error "zz-parity: nn-parity did not land")))
(ai zp-par)                              ; skolemize the witness w
(define zp-wconj
  (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                               (pair? (caddr f)) (eq? (car (caddr f)) 'OR))) (zp-asms))
      (error "zz-parity: w-body did not land")))
(ai zp-wconj)
(define zp-wor
  (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'OR)
                               (not (eq? f zp-nor)))) (zp-asms))
      (error "zz-parity: no 2w / succ(2w) split")))
(define zp-w (caddr (caddr (cadr zp-wor))))     ; the w in n = 2*w
(fact 'nn-subset-zz zp-w)                        ; w in ZZ
;;; Typings, established once (each closure axiom has an AND antecedent that
;;; `fact' will not split, so cut the AND and close it from context):
;;;   (IN (2*w) NN)     -- for nn-succ-plus-one
;;;   (IN (- w) ZZ)     -- the even-negative witness
;;;   (IN (- (w+1)) ZZ) -- the odd-negative witness  (-(2w+1) = 2(-(w+1))+1)
(zp-cut! (list 'AND '(IN 2 NN) (list 'IN zp-w 'NN)))
(fact 'nn-mul-closed 2 zp-w)             ; (IN (2*w) NN)
(fact 'zz-neg-closed zp-w)               ; (IN (- w) ZZ)
(zp-cut! (list 'AND (list 'IN zp-w 'ZZ) '(IN 1 ZZ)))
(fact 'zz-add-closed zp-w 1)             ; (IN (w+1) ZZ)
(fact 'zz-neg-closed (list '+ zp-w 1))   ; (IN (- (w+1)) ZZ)

;;; Normalize the natural's parity to +1 form (no succ, so crs can finish):
;;; PARN := (n = 2*w) or (n = 2*w + 1).  Proved from zp-wor + nn-succ-plus-one.
(define zp-parn (list 'OR (list '= zp-n (list '* 2 zp-w))
                          (list '= zp-n (list '+ (list '* 2 zp-w) 1))))
(zp-cut! zp-parn
  (lambda ()
    ;; from n = 2w or n = succ(2w): left disjunct is already the target's left;
    ;; right disjunct becomes 2w+1 via succ(2w) = 2w+1.
    (for-each
      (lambda (leaf)
        (dk-focus! leaf)
        (let ((asm (zp-any (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) zp-n)))
                           (zp-asms))))
          (cond
            ((equal? asm (list '= zp-n (list '* 2 zp-w))) (oi-l) (ass))
            (else                                   ; n = succ(2w)
             (oi-r)
             (fact 'nn-succ-plus-one (list '* 2 zp-w))     ; succ(2w) = 2w+1
             (subst asm)                                    ; goal n=2w+1 -> succ(2w)=2w+1
             (ass)))))
      (dk-opened (lambda () (ai zp-wor))))))

;;; Now the 4-way split: {a=n, a=-n} x {n=2w, n=2w+1}.  Negation preserves
;;; parity, so parity(a) = parity(n); the witness shifts.  Every leaf closes by
;;; two substs and a crs identity.
(define (zp-a-eq)                         ; the a-equation on the focused leaf
  (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) 'a))) (zp-asms))
      (error "zz-parity: no a-equation on this leaf")))
(define (zp-n-eq)                         ; the n-equation on the focused leaf
  (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) zp-n))) (zp-asms))
      (error "zz-parity: no n-equation on this leaf")))

(for-each
  (lambda (a-leaf)
    (dk-focus! a-leaf)
    (for-each
      (lambda (n-leaf)
        (dk-focus! n-leaf)
        (let* ((a-eq  (zp-a-eq))
               (n-eq  (zp-n-eq))
               (neg?  (pair? (caddr a-eq)))                 ; a = -n  vs  a = n
               (even? (equal? (caddr n-eq) (list '* 2 zp-w)))
               (wit   (cond ((not neg?) zp-w)               ; a = n : same witness
                            (even?      (list '- zp-w))     ; -(2w) = 2(-w)
                            (else (list '- (list '+ zp-w 1))))))  ; -(2w+1) = 2(-(w+1))+1
          (if even? (oi-l) (oi-r))
          (mac (if even? 'even-def 'odd-def))
          (ew wit)
          (for-each
            (lambda (k)
              (dk-focus! k)
              (let ((g (zp-goal)))
                (if (and (pair? g) (eq? (car g) 'IN))
                    (zp-from-context!)                      ; (IN wit ZZ)
                    (begin (subst a-eq) (subst n-eq) (crs)))))
            (dk-opened (lambda () (di))))))
      (dk-opened (lambda () (ai zp-parn)))))
  (dk-opened (lambda () (ai zp-nor))))
(zp-qed! 'zz-parity)
;;; =======================================================================
;;; Two facts about DOUBLED NATURALS, the arithmetic core of exclusivity:
;;;   nn-2p-neq-1    : p in NN => 2p /= 1     (2p is succ(2*0) is FALSE)
;;;   nn-2p-neq-neg1 : p in NN => 2p /= -1    (2p >= 0 > -1)
(sp (make-wff '(FORALL p (IMPLIES (IN p NN) (NOT (= (* 2 p) 1))))))
(di)(di)
(fact 'nn-parity-exclusive 'p 0)         ; NOT (2p = succ(2*0))
(di)                                     ; assume 2p = 1; goal FALSITY
(zp-cut! '(= (* 2 0) 0) (lambda () (arith)))
(zp-cut! '(= (* 2 p) (succ (* 2 0)))
         (lambda ()
           (subst '(= (* 2 p) 1))                ; 2p -> 1
           (subst '(= (* 2 0) 0))                ; succ(2*0) -> succ 0
           (mac 'nn-one-is-succ-zero)            ; goal 1 = succ 0
           (rfl)))
(ai '(NOT (= (* 2 p) (succ (* 2 0)))))
(zp-qed! 'nn-2p-neq-1)

(sp (make-wff '(FORALL p (IMPLIES (IN p NN) (NOT (= (* 2 p) (- 1)))))))
(di)(di)
(zp-cut! (list 'AND '(IN 2 NN) '(IN p NN)))
(fact 'nn-mul-closed 2 'p)               ; (IN (2p) NN)
(fact 'nn-zero-le '(* 2 p))              ; 0 <= 2p
(di)                                     ; assume 2p = -1; goal FALSITY
(zp-cut! '(<= 0 (- 1)) (lambda () (subst '(= (- 1) (* 2 p))) (ass)))
(zp-cut! '(NOT (<= 0 (- 1))) (lambda () (arith)))
(ai '(NOT (<= 0 (- 1))))
(zp-qed! 'nn-2p-neq-neg1)

;;; -----------------------------------------------------------------------
;;; zz-2m-neq-1 : forall m in ZZ. 2m /= 1.
;;; m = p or m = -p (p in NN).  m = p gives 2p = 1 (nn-2p-neq-1); m = -p gives
;;; 2p = -1 (via 2p = -(2m) = -1), which nn-2p-neq-neg1 forbids.
(sp (make-wff '(FORALL m (IMPLIES (IN m ZZ) (NOT (= (* 2 m) 1))))))
(di)(di)
(fact 'zz-generated-by-nn 'm)
(define zp2-gen (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (zp-asms))
                    (error "zz-2m-neq-1: no generator")))
(ai zp2-gen)
(define zp2-conj (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                                (pair? (caddr f)) (eq? (car (caddr f)) 'OR))) (zp-asms))
                     (error "zz-2m-neq-1: no body")))
(ai zp2-conj)
(define zp2-pn (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'NN))) (zp-asms))
                   (error "zz-2m-neq-1: no (IN p NN)")))
(define zp2-p (cadr zp2-pn))
(define zp2-or (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'OR))) (zp-asms))
                   (error "zz-2m-neq-1: no m=p / m=-p")))
(di)                                     ; assume 2m = 1; goal FALSITY
(for-each
  (lambda (leaf)
    (dk-focus! leaf)
    (let ((meq (zp-any (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) 'm))) (zp-asms))))
      (cond
        ((equal? meq (list '= 'm zp2-p))           ; m = p
         (fact 'nn-2p-neq-1 zp2-p)                 ; NOT (2p = 1)
         (zp-cut! (list '= (list '* 2 zp2-p) 1)
                  (lambda () (subst (list '= zp2-p 'm)) (ass)))   ; 2p -> 2m -> (=1)
         (ai (list 'NOT (list '= (list '* 2 zp2-p) 1))))
        (else                                      ; m = -p
         (fact 'nn-2p-neq-neg1 zp2-p)              ; NOT (2p = -1)
         (fact 'nn-subset-zz zp2-p)                ; p in ZZ, for crs
         ;; p = -m (neg-neg of m = -p), then 2p = -(2m) = -1.
         (zp-cut! (list '= zp2-p (list '- 'm))
                  (lambda () (subst (list '= 'm (list '- zp2-p))) (crs)))
         (zp-cut! (list '= (list '* 2 zp2-p) (list '- (list '* 2 'm)))
                  (lambda () (subst (list '= zp2-p (list '- 'm))) (crs)))  ; p->-m, identity
         (zp-cut! (list '= (list '* 2 zp2-p) '(- 1))
                  (lambda ()
                    (subst (list '= (list '* 2 zp2-p) (list '- (list '* 2 'm))))  ; 2p -> -(2m)
                    (subst '(= (* 2 m) 1))                                         ; 2m -> 1
                    (crs)))
         (ai (list 'NOT (list '= (list '* 2 zp2-p) '(- 1))))))))
  (dk-opened (lambda () (ai zp2-or))))
(zp-qed! 'zz-2m-neq-1)

;;; =======================================================================
;;; zz-not-even-and-odd : no integer is both EVEN and ODD.
;;; x = 2k and x = 2j+1  =>  2k = 2j+1  =>  2(k-j) = 1, forbidden by zz-2m-neq-1.
(sp (make-wff '(FORALL x (IMPLIES (IN x ZZ)
                 (NOT (AND (EVEN x) (ODD x)))))))
(di)(di)(di)                             ; x ; IN x ZZ ; assume (EVEN x and ODD x); goal FALSITY
(define zp-eo (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                            (pair? (cadr f)) (eq? (car (cadr f)) 'EVEN))) (zp-asms))
                  (error "not-even-and-odd: no conjunction")))
(ai zp-eo)                               ; EVEN x , ODD x
(mac-h 'even-def '(EVEN x))
(mac-h 'odd-def '(ODD x))
;; skolemize BOTH existentials (EVEN and ODD each land one), then split both
;; landed conjunctions, until no FORSOME/AND-with-x remains.
(let loop ((fuel 8))
  (let ((ex (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (zp-asms))))
    (when (and ex (> fuel 0)) (ai ex) (loop (- fuel 1)))))
(let loop ((fuel 8))
  (let ((cj (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                        (pair? (caddr f)) (eq? (car (caddr f)) '=)
                        (eq? (cadr (caddr f)) 'x))) (zp-asms))))
    (when (and cj (> fuel 0)) (ai cj) (loop (- fuel 1)))))
;; two `= x' assumptions now: x = 2*k  and  x = 2*j+1.  Read each off its shape.
(define zp-keq (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) 'x)
                             (pair? (caddr f)) (eq? (car (caddr f)) '*))) (zp-asms))
                   (error "not-even-and-odd: no x=2k")))
(define zp-jeq (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) 'x)
                             (pair? (caddr f)) (eq? (car (caddr f)) '+))) (zp-asms))
                   (error "not-even-and-odd: no x=2j+1")))
(define zp-k (caddr (caddr zp-keq)))      ; x = 2 * k
(define zp-j (caddr (cadr (caddr zp-jeq))))  ; x = (2 * j) + 1
;; k, j in ZZ; m := k - j; 2m = 1, contradiction.
(define zp-m (list '+ zp-k (list '- zp-j)))   ; k + (-j), matches closure directly
(zp-cut! (list 'AND (list 'IN zp-k 'ZZ) (list 'IN zp-j 'ZZ)))
(fact 'zz-neg-closed zp-j)               ; -j in ZZ
(zp-cut! (list 'AND (list 'IN zp-k 'ZZ) (list 'IN (list '- zp-j) 'ZZ)))
(fact 'zz-add-closed zp-k (list '- zp-j))    ; k + (-j) = k - j in ZZ
; (IN (k + -j) ZZ) is already in context, from zz-add-closed above -- no cut needed.
(fact 'zz-2m-neq-1 zp-m)                 ; NOT (2*(k-j) = 1)
;; 2*(k-j) = 2k - 2j = (2j+1) - 2j = 1.  crs, using x=2k and x=2j+1.
;; 2k = 2j+1 (both equal x); then 2*(k-j) = (2j+1) - 2j = 1.  `simp' distributes
;; the goal so 2k is a subterm; subst rewrites it; crs finishes.
(define zp-2k=2j1 (list '= (list '* 2 zp-k) (list '+ (list '* 2 zp-j) 1)))
(zp-cut! zp-2k=2j1
         (lambda () (subst (list '= (list '* 2 zp-k) 'x)) (ass)))   ; 2k->x = zp-jeq
(zp-cut! (list '= (list '* 2 zp-m)
                    (list '- (list '* 2 zp-k) (list '* 2 zp-j)))
         (lambda () (crs)))                             ; distribute: pure identity
(zp-cut! (list '= (list '* 2 zp-m) 1)
         (lambda ()
           (subst (list '= (list '* 2 zp-m)
                        (list '- (list '* 2 zp-k) (list '* 2 zp-j))))  ; 2(k-j) -> 2k-2j
           (subst zp-2k=2j1)                             ; 2k -> 2j+1
           (crs)))
(ai (list 'NOT (list '= (list '* 2 zp-m) 1)))
(zp-qed! 'zz-not-even-and-odd)

;;; =======================================================================
;;; zz-even-iff-not-odd : EVEN(x) <=> not ODD(x), the two halves together.
(sp (make-wff '(FORALL x (IMPLIES (IN x ZZ) (IFF (EVEN x) (NOT (ODD x)))))))
(di)(di)
(di)                                     ; IFF -> two implications; do -> first
;; forward: EVEN x => not ODD x.  Directly from exclusivity.
(di)                                     ; assume EVEN x ; goal NOT (ODD x)
(di)                                     ; assume ODD x ; goal FALSITY
(fact 'zz-not-even-and-odd 'x)           ; NOT (EVEN x and ODD x)
(zp-cut! '(AND (EVEN x) (ODD x)))
(ai '(NOT (AND (EVEN x) (ODD x))))
;; backward: not ODD x => EVEN x.  From dichotomy: x is EVEN or ODD; not ODD kills the right.
(fact 'zz-parity 'x)                     ; EVEN x or ODD x
(di)                                     ; assume NOT (ODD x) ; goal EVEN x
(define zp-eio (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'OR))) (zp-asms))
                   (error "even-iff: no dichotomy")))
(for-each
  (lambda (leaf)
    (dk-focus! leaf)
    (let ((has-even (zp-any (lambda (f) (equal? f '(EVEN x))) (zp-asms))))
      (if has-even
          (ass)                          ; EVEN x is the goal
          (ai '(NOT (ODD x))))))         ; ODD x present, contradicts NOT (ODD x)
  (dk-opened (lambda () (ai zp-eio))))
(zp-qed! 'zz-even-iff-not-odd)

;;; =======================================================================
;;; Multiplicative facts -- ring identities over typed generators, so crs.
;;; zz-even-mul : EVEN(x) => EVEN(x*y).   x = 2k => x*y = 2*(k*y).
(sp (make-wff '(FORALL x (IMPLIES (IN x ZZ)
                 (FORALL y (IMPLIES (IN y ZZ)
                   (IMPLIES (EVEN x) (EVEN (* x y)))))))))
(di)(di)(di)(di)(di)                     ; x ; INx ; y ; INy ; assume EVEN x
(mac-h 'even-def '(EVEN x))
(define zm-ex (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (zp-asms))
                  (error "even-mul: EVEN did not unfold")))
(ai zm-ex)
(define zm-c (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                          (pair? (caddr f)) (eq? (cadr (caddr f)) 'x))) (zp-asms))
                 (error "even-mul: no x=2k")))
(ai zm-c)
(define zm-k (caddr (caddr (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) '=)
                     (eq? (cadr f) 'x))) (zp-asms)) (error "even-mul: no k")))))
(mac 'even-def)                          ; goal EVEN(x*y) -> forsome...
(ew (list '* zm-k 'y))                   ; witness k*y
(for-each (lambda (leaf)
            (dk-focus! leaf)
            (let ((g (zp-goal)))
              (cond
                ((and (pair? g) (eq? (car g) 'IN))       ; (IN (k*y) ZZ)
                 (zp-cut! (list 'AND (list 'IN zm-k 'ZZ) '(IN y ZZ)))
                 (fact 'zz-mul-closed zm-k 'y) (ass))
                (else                                     ; x*y = 2*(k*y)
                 (subst (list '= 'x (list '* 2 zm-k)))    ; x -> 2k
                 (crs)))))
          (dk-opened (lambda () (di))))
(zp-qed! 'zz-even-mul)

;;; zz-odd-mul-odd : ODD(x) and ODD(y) => ODD(x*y).
;;; x = 2a+1, y = 2b+1 => x*y = 2*(2ab+a+b)+1.
(sp (make-wff '(FORALL x (IMPLIES (IN x ZZ)
                 (FORALL y (IMPLIES (IN y ZZ)
                   (IMPLIES (ODD x) (IMPLIES (ODD y) (ODD (* x y))))))))))
(di)(di)(di)(di)(di)(di)                 ; x INx y INy ODDx ODDy
(mac-h 'odd-def '(ODD x))
(mac-h 'odd-def '(ODD y))
(let loop ((fuel 6))
  (let ((ex (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (zp-asms))))
    (when (and ex (> fuel 0)) (ai ex) (loop (- fuel 1)))))
(let loop ((fuel 6))
  (let ((cj (zp-any (lambda (f) (and (pair? f) (eq? (car f) 'AND) (pair? (caddr f))
                        (eq? (car (caddr f)) '=) (memq (cadr (caddr f)) '(x y)))) (zp-asms))))
    (when (and cj (> fuel 0)) (ai cj) (loop (- fuel 1)))))
(define zo-xeq (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) 'x))) (zp-asms))
                   (error "odd-mul: no x eq")))
(define zo-yeq (or (zp-any (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) 'y))) (zp-asms))
                   (error "odd-mul: no y eq")))
(define zo-a (caddr (cadr (caddr zo-xeq))))   ; x = 2a+1
(define zo-b (caddr (cadr (caddr zo-yeq))))   ; y = 2b+1
(mac 'odd-def)                                ; goal ODD(x*y)
(define zo-ab   (list '* zo-a zo-b))
(define zo-2ab  (list '* 2 zo-ab))
(define zo-2aba (list '+ zo-2ab zo-a))
(define zo-wit  (list '+ zo-2aba zo-b))       ; 2ab+a+b, SAME subterms as typing below
(ew zo-wit)
(for-each (lambda (leaf)
            (dk-focus! leaf)
            (let ((g (zp-goal)))
              (cond
                ((and (pair? g) (eq? (car g) 'IN))       ; (IN (2ab+a+b) ZZ)
                 (zp-close2! zo-a zo-b 'zz-mul-closed)   ; ab in ZZ
                 (zp-close2! 2 zo-ab   'zz-mul-closed)   ; 2ab in ZZ
                 (zp-close2! zo-2ab zo-a 'zz-add-closed) ; 2ab+a in ZZ
                 (zp-close2! zo-2aba zo-b 'zz-add-closed); 2ab+a+b in ZZ
                 (ass))
                (else                                     ; x*y = 2*wit + 1
                 (subst zo-xeq) (subst zo-yeq) (crs)))))
          (dk-opened (lambda () (di))))
(zp-qed! 'zz-odd-mul-odd)

;;; zz-odd-sq-odd : ODD(x) => ODD(x*x).  Instance of odd-mul-odd at y := x.
(sp (make-wff '(FORALL x (IMPLIES (IN x ZZ) (IMPLIES (ODD x) (ODD (* x x)))))))
(di)(di)(di)
(fact 'zz-odd-mul-odd 'x 'x)
(ass)
(zp-qed! 'zz-odd-sq-odd)

;;; NOTE: even-square => even lives on NN (theorem-library/nn-parity-proof.scm,
;;; nn-even-square) -- the sqrt(2) descent is entirely in NN, per the plan, so
;;; the ZZ version is not needed and is omitted.
