;;; calculus/prop-3-15-proof.scm
;;; ===================================================================
;;; Proposition 3.15, (1) => (3) of docs/calculus.pdf:
;;;
;;;   IS-CONTINUOUS(s,t,f)  =>  for every open V in t,
;;;                             PREIMAGE(s,f,V) is open in s.
;;;
;;; This is the topological-continuity keystone (the closed-set version
;;; (1) => (2) is a complement-algebra corollary of it via
;;; preimage-complement, exactly as that warrant states).  Previously
;;; `continuous-implies-open-preimage' was an ASSERTED support carrying a
;;; paper-proof warrant; this file proves it inside VNB, flipping it
;;; asserted -> proven (cf. metric-laws.scm / subtype-laws.scm).
;;;
;;; Run standalone (deterministic eigenvars; skips the load-time proofs):
;;;   VNB_SKIP_PROOFS=1 mit-scheme --quiet --load load.scm \
;;;                                --load calculus/prop-3-15-proof.scm
;;;
;;; THE STRESS TEST -- three pieces of machinery the eps/delta argument
;;; needs, all added as warranted PSS supports (library-build phase):
;;;   * preimage-subset-carrier  PREIMAGE(s,f,V) subset X(s)        [set]
;;;   * ball-mem-from-le         d(x,y)<=d, d<r  =>  y in BALL(s,x,r)
;;;                              -- bridges V's STRICT eps-ball to
;;;                                 continuity's NON-strict bound      [metric/order]
;;;   * rr-pos-shrink            below every eps>0 sits a d>0 with d<eps
;;;                              -- order density at 0; lets continuity
;;;                                 be applied at a strictly smaller radius [order]
;;; Modulo those + the RR order axioms + fun-apply-type, the structural
;;; skeleton (preimage<->membership, continuity-at threading, witness
;;; delta) checks to QED.
;;;
;;; Proof shape: y in PREIMAGE means f(y) in V open, so some eps-ball
;;; B(t,f(y),eps) subset V.  Shrink to half<eps; continuity at y for half
;;; gives delta>0 with d(s)(y,z)<=delta  =>  d(t)(f(y),f(z))<=half<eps,
;;; so f(z) in B(t,f(y),eps) subset V, i.e. f(z) in V, i.e.
;;; B(s,y,delta) subset PREIMAGE(s,f,V).  Hence the preimage is open.
;;; ===================================================================

;;; ---- forward-reasoning helpers (mirrors prop-3-14-proof.scm) ----
(define (proof-leaves)
  (filter (lambda (sqn) (and (not (sequent-node-grounded? sqn))
                             (null? (sequent-node-in-arrows sqn))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (sub? substr s) (and (string-search-forward substr s 0) #t))
(define (any-pred pred lst)
  (let loop ((l lst)) (cond ((null? l) #f) ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (cur-sqn) (proof-state-focus *ps*))
(define (cur-goal-raw) (wff-formula (sequent-node-assertion (cur-sqn))))
(define (asm-find-pred pred)
  (let ((w (any-pred (lambda (w) (pred (wff-formula w)))
                     (sequent-node-assumptions (cur-sqn)))))
    (and w (wff-formula w))))
(define (asm-find-sub substr)
  (asm-find-pred (lambda (f) (sub? substr (expression->string f)))))
(define (asm-find= raw) (asm-find-pred (lambda (w) (equal? w raw))))  ; exact assumption
(define (estr raw) (expression->string (make-wff raw)))              ; printed form of a raw wff
(define (focus-leaf! substr)
  (let ((s (any-pred (lambda (s) (sub? substr (expression->string (sequent-node-assertion s))))
                     (proof-leaves))))
    (if s (begin (set-proof-state-focus! *ps* s) s)
        (error "focus-leaf!: no frontier leaf matching" substr))))
(define (focus-leaf-goal! raw)
  (let ((s (any-pred (lambda (s) (equal? (wff-formula (sequent-node-assertion s)) raw))
                     (proof-leaves))))
    (if s (begin (set-proof-state-focus! *ps* s) s)
        (error "focus-leaf-goal!: none equal to" (expression->string raw)))))
(define (focus-leaf-asm! substr)
  (let ((s (any-pred (lambda (s) (any-pred (lambda (w) (sub? substr (expression->string (wff-formula w))))
                                           (sequent-node-assumptions s)))
                     (proof-leaves))))
    (if s (begin (set-proof-state-focus! *ps* s) s)
        (error "focus-leaf-asm!: none with asm" substr))))
(define (split-ands!)
  (let loop ()
    (let scan ((as (sequent-node-assumptions (cur-sqn))))
      (cond ((null? as) 'done)
            ((let ((f (wff-formula (car as)))) (and (pair? f) (eq? (car f) 'AND)))
             (ai (wff-formula (car as))) (loop))
            (else (scan (cdr as)))))))
(define (asm-set) (map wff-formula (sequent-node-assumptions (cur-sqn))))
(define (ai-body forsome-raw)            ; eliminate FORSOME hyp, return body added
  (let ((before (asm-set)))
    (ai forsome-raw)
    (any-pred (lambda (f) (not (member f before))) (asm-set))))
(define (witness-of body) (cadr (cadr body)))   ; (AND (POS-RR w) _) -> w
(define (detach! impl)                   ; forward MP: A in ctx, (IMPLIES A B) -> B in ctx
  (let ((B (caddr impl)))
    (cut B) (focus-leaf-goal! B) (bc impl) (ass)
    (focus-leaf-asm! (expression->string B))))
(define (di-all-and!)                    ; split every AND-goal frontier leaf
  (let loop ()
    (let ((hit (any-pred (lambda (s) (let ((g (wff-formula (sequent-node-assertion s))))
                                       (and (pair? g) (eq? (car g) 'AND) s)))
                         (proof-leaves))))
      (when hit (set-proof-state-focus! *ps* hit) (di) (loop)))))
(define (close-trivial!)                 ; ass-close every leaf whose goal sits in its asms
  (let loop ()
    (let ((hit (any-pred
                (lambda (s)
                  (let ((g (wff-formula (sequent-node-assertion s))))
                    (and (any-pred (lambda (w) (equal? (wff-formula w) g))
                                   (sequent-node-assumptions s)) s)))
                (proof-leaves))))
      (when hit (set-proof-state-focus! *ps* hit) (ass) (loop)))))

;;; ===================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL f
   (IMPLIES (IS-CONTINUOUS s t f)
     (FORALL V (IMPLIES (IS-OPEN t V)
       (IS-OPEN s (PREIMAGE s f V))))))))))
(di) (di) (di) (di)        ; peel s,t,f,V ; asms: cont, is-open(t,V)
(mac 'IS-OPEN) (di)        ; goal AND -> leaf1 metric, leaf2 AND(subset, interior)

;;; G1: IS-METRIC-SPACE s  (from continuity's typing conjunct)
(focus-leaf! "is-metric-space")
(mac-h 'IS-CONTINUOUS (asm-find-sub "is-continuous")) (split-ands!) (ass)

;;; split G2 ; G2a: PREIMAGE(s,f,V) subset X(s)
(focus-leaf! "and forall(") (di)
(focus-leaf! "subset x(s") (bc* 'preimage-subset-carrier)

;;; G2b: peel the open point y, capture structural eigenvars
(focus-leaf! "forall([y in preimage") (di)
(define GOAL0 (cur-goal-raw))            ; (FORSOME r (AND (POS-RR r)(SUBSET (BALL S Y r)(PREIMAGE S F V))))
(define sub0  (caddr (caddr GOAL0)))
(define ball0 (cadr sub0))
(define S (cadr ball0)) (define Y (caddr ball0))
(define pre0 (caddr sub0))
(define F (caddr pre0)) (define V (cadddr pre0))
(define T (caddr (asm-find-sub "is-continuous(s")))
(define (main!) (focus-leaf-goal! GOAL0))
(define EPS #f) (define HALF #f) (define DELTA #f)

;;; unfold y-membership and V-openness
(mac-h 'preimage-membership (asm-find= `(IN ,Y (PREIMAGE ,S ,F ,V)))) (split-ands!)
(mac-h 'IS-OPEN (asm-find= `(IS-OPEN ,T ,V))) (split-ands!)

;;; eps-ball B(t,f(y),eps) subset V:  inst V-interior at f(y), detach, witness eps
(inst (asm-find-sub (string-append "in " (symbol->string V) "], forsome")) `(,F ,Y))
(let ((impl-v (asm-find-pred (lambda (w) (and (pair? w) (eq? (car w) 'IMPLIES)
                                              (equal? (cadr w) `(IN (,F ,Y) ,V)))))))
  (detach! impl-v)
  (set! EPS (witness-of (ai-body (caddr impl-v)))))
(split-ands!)                            ; H_eps_pos: POS-RR EPS ; H_Vsub: B(t,f y,EPS) subset V

;;; shrink eps:  half with POS-RR half and half < eps
(main!)
(cut `(FORSOME d (AND (POS-RR d) (< d ,EPS))))
(focus-leaf-goal! `(FORSOME d (AND (POS-RR d) (< d ,EPS))))
(bc* 'rr-pos-shrink () (ass))            ; antecedent POS-RR eps
(main!)
(set! HALF (witness-of (ai-body `(FORSOME d (AND (POS-RR d) (< d ,EPS))))))
(split-ands!)                            ; H_half_pos: POS-RR HALF ; H_half_lt: HALF < EPS

;;; continuity at y, instantiated at half
(main!)
(cut `(IS-CONTINUOUS-AT ,S ,T ,F ,Y))
(focus-leaf-goal! `(IS-CONTINUOUS-AT ,S ,T ,F ,Y))
(bc* 'continuous-is-continuous-at () (ass) (ass))   ; IS-CONTINUOUS s t f ; IN y X(s)
(main!)
(mac-h 'IS-CONTINUOUS-AT (asm-find-sub "is-continuous-at")) (split-ands!)
(inst (asm-find-sub "pos-rr(eps) implies") HALF)
(let ((impl-c (asm-find-sub "implies forsome([delta")))
  (detach! impl-c)
  (set! DELTA (witness-of (ai-body (caddr impl-c)))))
(split-ands!)                            ; H_delta_pos ; H_delta_prop (forall b)

;;; expose RR-typing of half and eps for ball-mem-from-le.  Match the EXACT
;;; standalone (POS-RR w): the substring "pos-rr(<half>" would also hit the
;;; leftover "pos-rr(<half>) implies forsome..." continuity implication.
(mac-h 'POS-RR (asm-find= `(POS-RR ,HALF))) (split-ands!)   ; IN HALF RR
(mac-h 'POS-RR (asm-find= `(POS-RR ,EPS)))  (split-ands!)   ; IN EPS RR

;;; supply witness r := delta ; POS-RR delta is immediate
(main!)
(ew DELTA) (di)
(focus-leaf-goal! `(POS-RR ,DELTA)) (ass)

;;; remaining: BALL(s,y,delta) subset PREIMAGE(s,f,V)
(focus-leaf! "subset preimage")
(mac 'subset-def) (di)                   ; bounded forall: peels z AND drops "z in BALL" as asm
(define Z (cadr (cur-goal-raw)))         ; goal (IN Z (PREIMAGE S F V))
(mac-h 'ball-membership (asm-find= `(IN ,Z (BALL ,S ,Y ,DELTA)))) (split-ands!)  ; H_zX, H_dyz_le
(mac 'preimage-membership) (di)          ; IN z X(s) ; IN (f z) V
(focus-leaf-goal! `(IN ,Z (X ,S))) (ass)

;;; the crux: f(z) in V
;;; (a) d(t)(f y, f z) <= half   from the delta-property at z.
;;;     H_delta_prop is the only assumption with "b) <= <delta> implies"
;;;     (the spent continuity implication has the bound "<= delta implies").
(focus-leaf-goal! `(IN (,F ,Z) ,V))
;; find an (IMPLIES <ante> _) assumption by its exact antecedent
(define (impl-with ante)
  (asm-find-pred (lambda (w) (and (pair? w) (eq? (car w) 'IMPLIES) (equal? (cadr w) ante)))))
(let ((dp (asm-find-sub (string-append "b) <= " (symbol->string DELTA) " implies"))))
  (inst dp Z)
  (detach! (impl-with `(IN ,Z (X ,S))))            ; antecedent IN z X(s)
  (detach! (impl-with `(<= ((D ,S) ,Y ,Z) ,DELTA))))  ; antecedent d(s)(y,z) <= delta
;; (b) f(z) in BALL(t, f y, eps)  by ball-mem-from-le  (d := half)
(cut `(IN (,F ,Z) (BALL ,T (,F ,Y) ,EPS)))
(focus-leaf-goal! `(IN (,F ,Z) (BALL ,T (,F ,Y) ,EPS)))
(bc* 'ball-mem-from-le ((d HALF)))       ; spawns: IS-METRIC-SPACE t ; the typing/order AND
(close-trivial!)                         ; IS-METRIC-SPACE t
(di-all-and!) (close-trivial!)           ; IN half RR, IN eps RR, d(.,.)<=half, half<eps
(focus-leaf-goal! `(IN (,F ,Z) (X ,T)))  ; IN (f z) (X t)
(bc* 'fun-apply-type ((A `(X ,S))))      ; spawns AND (IN f (FUN..) , IN z X(s))
(di-all-and!) (close-trivial!)
;; (c) f(z) in V  via H_Vsub (subset): unfold subset-def, inst at f(z), backchain
(focus-leaf-goal! `(IN (,F ,Z) ,V))
(let ((before (asm-set)))
  (mac-h 'subset-def (asm-find= `(SUBSET (BALL ,T (,F ,Y) ,EPS) ,V)))   ; -> FORALL x (IN x BALL => IN x V)
  (let ((univ (any-pred (lambda (f) (and (not (member f before)) (pair? f) (eq? (car f) 'FORALL)))
                        (asm-set))))
    (inst univ `(,F ,Z))
    (bc (impl-with `(IN (,F ,Z) (BALL ,T (,F ,Y) ,EPS))))   ; goal IN (f z) V -> IN (f z) BALL
    (ass)))                              ; IN (f z) BALL in ctx (from step b)

;;; ---- install:  asserted -> proven ----
(qed 'continuous-implies-open-preimage)
(newline)
(display ";;; ==> proof-done? = ") (write (proof-done? *ps*)) (newline)
