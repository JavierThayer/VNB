;;; lastcoeff-ideal-proof.scm -- the two self-contained lemmas the
;;; spans-submodule-fg descent leans on (no induction here).
;;;
;;;   lastcoeff-zero-in-span   c_{1,succ p} = 0  =>  c.u in SPAN(md,p,BLOCK u p 1)
;;;   lastcoeff-set-is-ideal   LASTCOEFF-SET(md,p,u,sm) is an ideal of SCAL md
;;;
;;; lastcoeff-zero-in-span is matact-row-peel with the last term killed
;;; (module-zero-act) and dropped (abelian-group-right-id via MODULE-VECTOR-AG).
;;; lastcoeff-set-is-ideal reads each ideal axiom off a coefficient-row witness:
;;; ZEROMAT for 0, MATADD for +, MATSCALE for ring multiples and (via the -1
;;; multiple) for negation -- exactly bricks 1-3.
;;;
;;; Needs: mod-seq (MATACT, LASTCOEFF-SET, SPAN + memberships), the row bricks
;;; (matact-row-peel/-add/-scale/-zerorow), matrix (BLOCK/ZEROMAT/MATADD/MATSCALE
;;; read-offs), ring/abelian-group (ring-neg-mul-left, abelian-group-right-id),
;;; finite-dimensional (submodule-*-closed).

(define SR '(SCAL md))
(define SC '(CARR (SCAL md)))

;;; ---- driver helpers (lc- prefix)
(define (lc-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (lc-foc! n) (set-proof-state-focus! *ps* n))
(define (lc-di*)
  (let lp () (let* ((g (lc-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (lc-head? h) (lambda (g) (and (pair? g) (eq? (car g) h))))
(define (lc-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (lc-find pred) (let loop ((as (lc-asms)))
                         (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
;; snapshot-and-split a 2-way branching tactic; prove each new leaf
(define (lc-two! act pred-a proa prob)
  (let ((before (proof-leaves)))
    (act)
    (let* ((new (filter (lambda (l) (not (memq l before))) (proof-leaves)))
           (a   (car (filter (lambda (l) (pred-a (wff-formula (sequent-node-assertion l)))) new)))
           (b   (car (filter (lambda (l) (not (eq? l a))) new))))
      (lc-foc! a) (proa)
      (lc-foc! b) (prob))))


;;; ===================================================================
;;; lastcoeff-zero-in-span
;;; ===================================================================
(define lz-Bc '(BLOCK c 1 p))
(define lz-Bu '(BLOCK u p 1))
(define lz-x  '(ENTRY (MATACT md c u) 1 1))
(define lz-bcbu '(ENTRY (MATACT md (BLOCK c 1 p) (BLOCK u p 1)) 1 1))
(define lz-last '((ACT md) (ENTRY c 1 (succ p)) (ENTRY u (succ p) 1)))

(sp (make-wff
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL p (IMPLIES (IN p NN)
      (FORALL u (IMPLIES (IN u (MAT (succ p) 1 (VEC md)))
       (FORALL c (IMPLIES (IN c (MAT 1 (succ p) (CARR (SCAL md))))
         (IMPLIES (= (ENTRY c 1 (succ p)) (ZERO (SCAL md)))
           (IN (ENTRY (MATACT md c u) 1 1) (SPAN md p (BLOCK u p 1))))))))))))))
(lc-di*)

(fact 'module-scalar-ring 'md)
(fact 'module-vector-ag-is-abelian-group 'md)
(fact 'nn-one-in) (fact 'nn-le-refl 1) (fact 'nn-le-succ 'p) (fact 'nn-succ-closed 'p)
(fact 'one-in-interval-1)
(fact 'nn-le-refl '(succ p)) (fact 'nn-one-le-succ 'p)
(fact 'interval-mem-intro 1 '(succ p) '(succ p))          ; succ p in [1,succ p]
(fact 'block-type 1 '(succ p) SC 'c 1 'p)                 ; Bc in MAT 1 p CARR
(fact 'block-type '(succ p) 1 '(VEC md) 'u 'p 1)          ; Bu in MAT p 1 VEC
(fact 'entry-in-carrier '(succ p) 1 '(VEC md) 'u '(succ p) 1)  ; u_{succ p,1} in VEC

;; x = bcbu + last  (matact-row-peel at n := p) -- lands the peel eq in context
(fact 'matact-row-peel 'md 'p 'c 'u)
(fact 'module-zero-act 'md '(ENTRY u (succ p) 1))          ; (ACT)(ZERO)(u_{succ p,1}) = VZERO
(fact 'matact-type 'md 1 'p 1 lz-Bc lz-Bu)                 ; MATACT Bc Bu in MAT 1 1 VEC
(fact 'entry-in-carrier 1 1 '(VEC md) '(MATACT md (BLOCK c 1 p) (BLOCK u p 1)) 1 1)  ; bcbu in VEC
(fact 'abelian-group-right-id-module-vector-ag 'md lz-bcbu)  ; (VADD)(bcbu)(VZERO) = bcbu

;; assemble x = bcbu  via a cut
(define lz-eq (list '= lz-x lz-bcbu))
(let ((before (proof-leaves)))
  (cut lz-eq)
  (let* ((new (filter (lambda (l) (not (memq l before))) (proof-leaves)))
         (sub (car (filter (lambda (l) (equal? (wff-formula (sequent-node-assertion l)) lz-eq)) new)))
         (cont (car (filter (lambda (l) (not (eq? l sub))) new))))
    (lc-foc! sub)
    ;; goal x = bcbu.  Rewrite x by the peel eq, then collapse the last term.
    (subst (list '= lz-x (list '(VADD md) lz-bcbu lz-last)))     ; x -> (VADD)(bcbu)(last)
    (subst (list '= '(ENTRY c 1 (succ p)) '(ZERO (SCAL md))))    ; entry c 1 (succ p) -> 0
    (subst (list '= (list '(ACT md) '(ZERO (SCAL md)) '(ENTRY u (succ p) 1)) '(VZERO md)))  ; 0.u -> VZERO
    ;; goal (VADD)(bcbu)(VZERO) = bcbu -- exactly abelian-group-right-id
    (ass)
    (lc-foc! cont)
    ;; now x = bcbu in context; prove IN x (SPAN md p Bu)
    (mac 'span-membership)
    (lc-two! (lambda () (di)) (lc-head? 'IN)
      (lambda ()                                            ; IN x (VEC md)
        (subst lz-eq)                                       ; x -> bcbu
        (ass))
      (lambda ()                                            ; FORSOME c' ...
        (lc-two! (lambda () (ew lz-Bc) (di)) (lc-head? 'IN)
          (lambda () (ass))                                 ; IN Bc (MAT 1 p CARR)
          (lambda () (ass)))))))                            ; = x bcbu (lz-eq)

(qed 'lastcoeff-zero-in-span)
(category! 'lastcoeff-zero-in-span 'algebra)
(category! 'abelian-group-right-id 'algebra)
(category! 'ring-neg-mul-left 'algebra)


;;; ===================================================================
;;; lastcoeff-set-is-ideal -- each ideal axiom read off a coefficient-row witness.
;;; ===================================================================
(define LCS '(LASTCOEFF-SET md p u sm))
(define lc-n1 (list (list 'NEG '(SCAL md)) (list 'ONE '(SCAL md))))   ; -1 in SCAL md
(define (lc-mateq c) (list 'IN c (list 'MAT 1 '(succ p) SC)))
(define (lc-cu c) (list 'ENTRY (list 'MATACT 'md c 'u) 1 1))          ; c.u

;; safe nested list access: (g@ g 2 1 2) = list-ref chain, or #f on any bad step
(define (g@ l . idxs)
  (let loop ((x l) (is idxs))
    (cond ((null? is) x)
          ((and (pair? x) (list? x) (> (length x) (car is))) (loop (list-ref x (car is)) (cdr is)))
          (else #f))))
(define (lc-find pred) (let loop ((as (lc-asms)))
                         (cond ((null? as) (error "lc-find: none" pred))
                               ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (lc-foc-goal! pred)
  (let loop ((ls (proof-leaves)))
    (cond ((null? ls) (error "lc-foc-goal!: no leaf"))
          ((pred (wff-formula (sequent-node-assertion (car ls)))) (lc-foc! (car ls)) (car ls))
          (else (loop (cdr ls))))))
(define (lc-split-and!)
  (let lp ((k 0))
    (let ((leaf (find-first (lambda (s) (let ((g (wff-formula (sequent-node-assertion s))))
                                          (and (pair? g) (eq? (car g) 'AND)))) (proof-leaves))))
      (when (and leaf (< k 12)) (lc-foc! leaf) (di) (lp (+ k 1))))))
;; the (IN _ (MAT 1 (succ p) SC)) witnesses currently in context
(define (lc-wits) (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) (list 'MAT 1 '(succ p) SC))))
                          (lc-asms)))
;; unpack (IN rterm LCS): leaves (IN rterm CARR), (= (ENTRY cw 1 (succ p)) rterm),
;; (IN cw.u sm) in context; returns the fresh witness matrix cw.
(define (lc-open! rterm)
  (let ((before (map cadr (lc-wits))))
    (mac-h 'lastcoeff-set-membership (list 'IN rterm LCS))
    (ai (lc-find (lc-head? 'AND)))
    (ai (lc-find (lc-head? 'FORSOME)))
    (ai (lc-find (lambda (f) (and (pair? f) (eq? (car f) 'AND) (pair? (cadr f)) (eq? (car (cadr f)) 'IN)
                                  (pair? (caddr (cadr f))) (eq? (car (caddr (cadr f))) 'MAT)))))
    (ai (lc-find (lambda (f) (and (pair? f) (eq? (car f) 'AND) (pair? (cadr f)) (eq? (car (cadr f)) '=)))))
    (car (filter (lambda (w) (not (member w before))) (map cadr (lc-wits))))))
;; focus, among leaves NOT in `before', the unique new one whose goal matches pred
(define (lc-new-foc! before pred)
  (let ((cand (filter (lambda (l) (and (not (memq l before))
                                       (pred (wff-formula (sequent-node-assertion l)))))
                      (proof-leaves))))
    (lc-foc! (car cand)) (car cand)))
(define (lc-new-other before matched)
  (car (filter (lambda (l) (and (not (memq l before)) (not (eq? l matched)))) (proof-leaves))))
;; prove goal (IN newr LCS): CARR-membership + a witness cw with its two facts.
;; Navigate STRICTLY within this call's own new leaves -- a global (lc-head? '=)
;; search would grab a leftover = leaf from another conjunct (wrong context).
(define (lc-show! newr cw prove-carr prove-mat prove-entry prove-act)
  (mac 'lastcoeff-set-membership)
  (let ((b0 (proof-leaves)))
    (di)                                          ; (AND (IN newr CARR)(FORSOME..))
    (let ((carr (lc-new-foc! b0 (lc-head? 'IN))))
      (prove-carr)
      (lc-foc! (lc-new-other b0 carr))            ; the FORSOME leaf
      (let ((b1 (proof-leaves)))
        (ew cw)                                    ; -> the AND body (one leaf)
        (lc-foc! (lc-new-other b1 #f))
        (let ((b2 (proof-leaves)))
          (di)                                     ; (IN cw MAT) ; (AND (= ..)(IN ..sm))
          (let ((matl (lc-new-foc! b2 (lambda (g) (and (pair? g) (eq? (car g) 'IN)
                                                       (equal? (caddr g) (list 'MAT 1 '(succ p) SC)))))))
            (prove-mat)
            (lc-foc! (lc-new-other b2 matl))       ; the (AND (= ..)(IN ..sm)) leaf
            (let ((b3 (proof-leaves)))
              (di)                                 ; (= ..) ; (IN cw.u sm)
              (let ((eql (lc-new-foc! b3 (lc-head? '=))))
                (prove-entry)
                (lc-foc! (lc-new-other b3 eql))    ; the sm-membership leaf
                (prove-act)))))))))

(sp (make-wff
  '(FORALL md (IMPLIES (IS-MODULE md)
     (IMPLIES (IS-COMMUTATIVE-RING (SCAL md))
      (FORALL p (IMPLIES (IN p NN)
       (FORALL u (IMPLIES (IN u (MAT (succ p) 1 (VEC md)))
        (FORALL sm (IMPLIES (IS-SUBMODULE md sm)
          (IS-IDEAL (SCAL md) (LASTCOEFF-SET md p u sm)))))))))))))
(lc-di*)

(fact 'commutative-ring-is-ring '(SCAL md))               ; SCAL md is a ring
(fact 'ring-one-in '(SCAL md))
(fact 'ring-neg-in-carr '(SCAL md) '(ONE (SCAL md)))      ; -1 in CARR
(fact 'one-in-interval-1)
(fact 'nn-succ-closed 'p)                                 ; succ p in NN (FIRST -- the rest need it)
(fact 'nn-le-refl '(succ p)) (fact 'nn-one-le-succ 'p)
(fact 'interval-mem-intro 1 '(succ p) '(succ p))          ; succ p in [1,succ p]

(mac 'IS-IDEAL)
(lc-split-and!)

;; (1) IS-COMMUTATIVE-RING (SCAL md)
(lc-foc-goal! (lc-head? 'IS-COMMUTATIVE-RING)) (ass)

;; (2) SUBSET LCS (CARR (SCAL md))
(lc-foc-goal! (lc-head? 'SUBSET))
(mac 'subset-def) (di)
(let ((rr (cadr (lc-goal))))
  (mac-h 'lastcoeff-set-membership (list 'IN rr LCS))
  (ai (lc-find (lc-head? 'AND)))
  (ass))

;; (3) IN (ZERO (SCAL md)) LCS
(lc-foc-goal! (lambda (g) (and (eq? (g@ g 0) 'IN) (equal? (g@ g 2) LCS) (equal? (g@ g 1) '(ZERO (SCAL md))))))
(lc-show! '(ZERO (SCAL md)) '(ZEROMAT (SCAL md) 1 (succ p))
  (lambda () (fact 'ring-zero-in '(SCAL md)) (ass))
  (lambda () (fact 'zeromat-type '(SCAL md) 1 '(succ p)) (ass))
  (lambda () (fact 'entry-of-zeromat '(SCAL md) 1 '(succ p) 1 '(succ p)) (ass))
  (lambda () (fact 'matact-zerorow 'md '(succ p) 'u)
             (subst (list '= (lc-cu '(ZEROMAT (SCAL md) 1 (succ p))) '(VZERO md)))
             (fact 'submodule-vzero-in 'md 'sm) (ass)))

;; (4) closed under (ADD (SCAL md))
(lc-foc-goal! (lambda (g) (and (eq? (g@ g 0) 'FORALL) (equal? (g@ g 2 1 2) LCS)    ; ante (IN a LCS)
                               (eq? (g@ g 2 2 0) 'FORALL))))                          ; cons FORALL b
(lc-di*)
(let* ((g (lc-goal)) (aa (cadr (cadr g))) (bb (caddr (cadr g))))   ; goal (IN ((ADD SR) a b) LCS)
  (let ((ca (lc-open! aa)) (cb (lc-open! bb)))
    (lc-show! (list '(ADD (SCAL md)) aa bb) (list 'MATADD '(SCAL md) ca cb)
      (lambda () (fact 'ring-add-closed '(SCAL md) aa bb) (ass))
      (lambda () (fact 'matadd-type '(SCAL md) 1 '(succ p) ca cb) (ass))
      (lambda ()
        (fact 'matadd-entry '(SCAL md) 1 '(succ p) ca cb 1 '(succ p))
        (subst (list '= (list 'ENTRY (list 'MATADD '(SCAL md) ca cb) 1 '(succ p))
                     (list '(ADD (SCAL md)) (list 'ENTRY ca 1 '(succ p)) (list 'ENTRY cb 1 '(succ p)))))
        (subst (list '= (list 'ENTRY ca 1 '(succ p)) aa))
        (subst (list '= (list 'ENTRY cb 1 '(succ p)) bb))
        (fact 'ring-add-closed '(SCAL md) aa bb)            ; (ADD a b) defined, for rfl
        (rfl))
      (lambda ()
        (fact 'matact-row-add 'md '(succ p) ca cb 'u)
        (subst (list '= (lc-cu (list 'MATADD '(SCAL md) ca cb)) (list '(VADD md) (lc-cu ca) (lc-cu cb))))
        (fact 'submodule-vadd-closed 'md 'sm (lc-cu ca) (lc-cu cb)) (ass)))))

;; (5) closed under (NEG (SCAL md))
(lc-foc-goal! (lambda (g) (and (eq? (g@ g 0) 'FORALL) (equal? (g@ g 2 1 2) LCS)    ; ante (IN a LCS)
                               (eq? (g@ g 2 2 0) 'IN))))                              ; cons IN (NEG..)
(lc-di*)
(let* ((g (lc-goal)) (aa (cadr (cadr g))))                       ; goal (IN ((NEG SR) a) LCS)
  (let ((ca (lc-open! aa)))
    (lc-show! (list '(NEG (SCAL md)) aa) (list 'MATSCALE '(SCAL md) lc-n1 ca)
      (lambda () (fact 'ring-neg-in-carr '(SCAL md) aa) (ass))
      (lambda () (fact 'matscale-type '(SCAL md) 1 '(succ p) lc-n1 ca) (ass))
      (lambda ()
        (fact 'one-in-interval-1) (fact 'interval-mem-intro 1 '(succ p) '(succ p))
        (fact 'matscale-entry '(SCAL md) 1 '(succ p) lc-n1 ca 1 '(succ p))
        (subst (list '= (list 'ENTRY (list 'MATSCALE '(SCAL md) lc-n1 ca) 1 '(succ p))
                     (list '(MUL (SCAL md)) lc-n1 (list 'ENTRY ca 1 '(succ p)))))
        (subst (list '= (list 'ENTRY ca 1 '(succ p)) aa))
        ;; goal (MUL (NEG 1) a) = (NEG a).  (NEG 1)*a = -(1*a) = -a.
        (fact 'ring-neg-mul-left '(SCAL md) '(ONE (SCAL md)) aa)
        (subst (list '= (list '(MUL (SCAL md)) lc-n1 aa)
                     (list '(NEG (SCAL md)) (list '(MUL (SCAL md)) '(ONE (SCAL md)) aa))))
        (fact 'ring-mul-left-id '(SCAL md) aa)
        (subst (list '= (list '(MUL (SCAL md)) '(ONE (SCAL md)) aa) aa))
        (fact 'ring-neg-in-carr '(SCAL md) aa)              ; (NEG a) defined, for rfl
        (rfl))
      (lambda ()
        (fact 'matact-row-scale 'md '(succ p) lc-n1 ca 'u)
        (subst (list '= (lc-cu (list 'MATSCALE '(SCAL md) lc-n1 ca)) (list '(ACT md) lc-n1 (lc-cu ca))))
        (fact 'submodule-act-closed 'md 'sm lc-n1 (lc-cu ca)) (ass)))))

;; (6) closed under ring multiples
(lc-foc-goal! (lambda (g) (and (eq? (g@ g 0) 'FORALL) (equal? (g@ g 2 1 2) SC))))  ; ante (IN r (CARR SR))
(lc-di*)
(let* ((g (lc-goal)) (rr (cadr (cadr g))) (aa (caddr (cadr g))))  ; goal (IN ((MUL SR) r a) LCS)
  (let ((ca (lc-open! aa)))
    (lc-show! (list '(MUL (SCAL md)) rr aa) (list 'MATSCALE '(SCAL md) rr ca)
      (lambda () (fact 'ring-carrier-closed-mul '(SCAL md) rr aa) (ass))
      (lambda () (fact 'matscale-type '(SCAL md) 1 '(succ p) rr ca) (ass))
      (lambda ()
        (fact 'one-in-interval-1) (fact 'interval-mem-intro 1 '(succ p) '(succ p))
        (fact 'matscale-entry '(SCAL md) 1 '(succ p) rr ca 1 '(succ p))
        (subst (list '= (list 'ENTRY (list 'MATSCALE '(SCAL md) rr ca) 1 '(succ p))
                     (list '(MUL (SCAL md)) rr (list 'ENTRY ca 1 '(succ p)))))
        (subst (list '= (list 'ENTRY ca 1 '(succ p)) aa))
        (fact 'ring-carrier-closed-mul '(SCAL md) rr aa)    ; (MUL r a) defined, for rfl
        (rfl))
      (lambda ()
        (fact 'matact-row-scale 'md '(succ p) rr ca 'u)
        (subst (list '= (lc-cu (list 'MATSCALE '(SCAL md) rr ca)) (list '(ACT md) rr (lc-cu ca))))
        (fact 'submodule-act-closed 'md 'sm rr (lc-cu ca)) (ass)))))

(qed 'lastcoeff-set-is-ideal)
(category! 'lastcoeff-set-is-ideal 'algebra)
