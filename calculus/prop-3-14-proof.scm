;;; prop-3-14-proof.scm
;;; ===================================================================
;;; Proposition 3.14 (=>):  the image of a convergent sequence under a
;;; continuous map converges to the image of the limit.
;;;
;;;   IS-CONTINUOUS-AT(s,t,f,a)  AND  CONVERGES-TO(s,g,a)
;;;        =>  CONVERGES-TO(t, COMPOSE(f,g), f(a))
;;;
;;; This is the first end-to-end metric-analysis proof in VNB to go all
;;; the way to QED through the eps-N core.  It was unreachable before
;;; `mac-h` (the hypothesis-side dual of `mac`): the typing conjuncts and
;;; the quantified eps-delta / eps-N payloads were locked inside the FOLDED
;;; predicates IS-CONTINUOUS-AT / CONVERGES-TO, and macetes only ever
;;; rewrote goals.  `mac-h` unfolds them in place, after which the rest is
;;; ordinary forward work.  See memory project_mac_h_tactic.
;;;
;;; Run standalone:
;;;   VNB_SKIP_PROOFS=1 mit-scheme --quiet --load load.scm \
;;;                                 --load calculus/prop-3-14-proof.scm
;;;
;;; The proof installs the theorem `converges-to-compose-continuous`.
;;; Proof debt:  modulo {compose, metric-sym}  (the only asserted leaves;
;;; fun-apply-type is primitive, the two folded-predicate unfolds are
;;; definitional).
;;; ===================================================================

;;; --------------------------------------------------------------------
;;; Forward-reasoning machinery
;;;
;;; The kernel has no forward modus ponens and no generic "use this
;;; quantified-implication hypothesis" step, and `proof-open-goals`
;;; returns ALL ungrounded nodes (ancestors included) so the auto-advanced
;;; focus after a leaf-closing rule is unreliable.  These helpers supply
;;; the missing discipline.  They are generic; candidates for promotion to
;;; a shared tactics file if more analysis proofs need them.
;;; --------------------------------------------------------------------

;; FRONTIER LEAVES = ungrounded nodes with no in-arrow (not yet expanded).
(define (proof-leaves)
  (filter (lambda (sqn) (and (not (sequent-node-grounded? sqn))
                             (null? (sequent-node-in-arrows sqn))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))

(define (sub? substr s) (and (string-search-forward substr s 0) #t))
(define (any-pred pred lst)
  (let loop ((l lst)) (cond ((null? l) #f) ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (cur-sqn) (proof-state-focus *ps*))
(define (cur-goal-raw) (wff-formula (sequent-node-assertion (cur-sqn))))

;; Find the raw formula of a current-context assumption (newest first, so a
;; loose predicate returns the most-recently-derived match).
(define (asm-find-pred pred)
  (let ((w (any-pred (lambda (w) (pred (wff-formula w)))
                     (sequent-node-assumptions (cur-sqn)))))
    (and w (wff-formula w))))
(define (asm-find-sub substr)
  (asm-find-pred (lambda (f) (sub? substr (expression->string f)))))

;; Explicitly focus the frontier leaf identified by goal (equal) / goal
;; (substring) / an assumption (substring).  Never trust auto-advance.
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

;; Split every AND hypothesis of the focus goal (used after mac-h to flatten
;; the unfolded payloads).
(define (split-ands!)
  (let loop ()
    (let scan ((as (sequent-node-assumptions (cur-sqn))))
      (cond ((null? as) 'done)
            ((let ((f (wff-formula (car as)))) (and (pair? f) (eq? (car f) 'AND)))
             (ai (wff-formula (car as))) (loop))
            (else (scan (cdr as)))))))

;; FORWARD MODUS PONENS on a local (IMPLIES A B) whose antecedent A is in
;; context: leaves B in context, focus on the continuation leaf.
;; (cut B; on the prove-B leaf backchain the implication and discharge A.)
(define (detach! impl)
  (let ((B (caddr impl)))
    (cut B)
    (focus-leaf-goal! B)
    (bc impl)
    (ass)
    (focus-leaf-asm! (expression->string B))))

;; Close every frontier leaf whose goal is already among its assumptions.
(define (ass-all-frontier!)
  (let loop ()
    (let ((hit (any-pred
                 (lambda (s)
                   (let ((g (wff-formula (sequent-node-assertion s))))
                     (and (any-pred (lambda (w) (alpha-equiv? (wff-formula w) g))
                                    (sequent-node-assumptions s))
                          s)))
                 (proof-leaves))))
      (when hit (set-proof-state-focus! *ps* hit) (ass) (loop)))))

;; Prove (IN (f x) B) by fun-apply-type (A supplied), leaving it in context.
(define (cut-mem! mem A)
  (cut mem)
  (focus-leaf-goal! mem)
  (bc* 'fun-apply-type ((A A)))
  (let ((andleaf (any-pred (lambda (s)
                             (let ((g (wff-formula (sequent-node-assertion s))))
                               (and (pair? g) (eq? (car g) 'AND) s)))
                           (proof-leaves))))
    (set-proof-state-focus! *ps* andleaf) (di))
  (ass-all-frontier!)
  (focus-leaf-asm! (expression->string mem)))

;; Add (= ((D S) P Q) ((D S) Q P)) to context via the metric-sym axiom.
;; Needs is-ms(S), (IN P (X S)), (IN Q (X S)) in context.  Relies on
;; newest-asm-first ordering so the generic forall predicates pick the
;; freshly-instantiated layer.  (The kernel handles the accessor-x /
;; bound-x name coincidence without capture.)
(define (forall-over S)
  (asm-find-pred (lambda (f)
    (and (pair? f) (eq? (car f) 'FORALL)
         (let ((b (caddr f)))
           (and (pair? b) (eq? (car b) 'IMPLIES)
                (equal? (cadr b) (list 'IN (cadr f) (list 'X S)))))))))
(define (metric-sym-eq! S P Q)
  (ta 'metric-sym)
  (inst (asm-find-pred (lambda (f)
          (and (pair? f) (eq? (car f) 'FORALL)
               (let ((b (caddr f)))
                 (and (pair? b) (eq? (car b) 'IMPLIES)
                      (equal? (cadr b) (list 'IS-METRIC-SPACE (cadr f))))))))
        S)
  (detach! (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                           (equal? (cadr f) (list 'IS-METRIC-SPACE S))))))
  (inst (forall-over S) P)
  (detach! (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                           (equal? (cadr f) (list 'IN P (list 'X S)))))))
  (inst (forall-over S) Q)
  (detach! (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                           (equal? (cadr f) (list 'IN Q (list 'X S))))))))

;;; ====================================================================
;;; The proof
;;; ====================================================================

(sp (make-wff '(IMPLIES (AND (IS-CONTINUOUS-AT s t f a) (CONVERGES-TO s g a))
                        (CONVERGES-TO t (COMPOSE f g) (f a)))))
(di)
(ai '(AND (IS-CONTINUOUS-AT s t f a) (CONVERGES-TO s g a)))

;;; --- clear "block 1": unfold the folded hypotheses with mac-h ---
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT s t f a))
(mac-h 'CONVERGES-TO     '(CONVERGES-TO s g a))
(split-ands!)                            ; flatten both payloads into context
(mac 'CONVERGES-TO)                      ; unfold the goal
(mac 'COMPOSE) (lam-b)                   ; COMPOSE(f,g)(n) -> f(g(n))

;;; The goal is now the 4-conjunct residue.  Split it fully.
(di)
(focus-leaf! "vnb-lambda") (di)
(focus-leaf! "f(a) in x(t) and") (di)

;;; --- C1: is-metric-space(t) ---
(focus-leaf! "is-metric-space(t)") (ass)

;;; --- C3: f(a) in x(t)  (fun-apply-type, A := X(s)) ---
(focus-leaf! "f(a) in x(t)")
(bc* 'fun-apply-type ((A '(X s))))
(focus-leaf! "and a in x(s)") (di)
(focus-leaf! "f in fun(x(s), x(t))") (ass)
(focus-leaf! "a in x(s)") (ass)

;;; --- C2: COMPOSE(f,g) in FUN(NN, X(t))  (lambda-type + fun-apply-type^2) ---
(focus-leaf! "vnb-lambda")
(lam-t) (di)
(focus-leaf! "in x(t)")
(bc* 'fun-apply-type ((A '(X s))))
(focus-leaf! "and g(") (di)
(focus-leaf! "f in fun(x(s), x(t))") (ass)
(focus-leaf! ") in x(s)")
(bc* 'fun-apply-type ((A 'NN)))
(focus-leaf! "fun(nn, x(s)) and") (di)
(focus-leaf! "g in fun(nn, x(s))") (ass)
(focus-leaf! "z_") (ass)

;;; --- C4: the eps-N core ---
(focus-leaf! "f(g(n_)), f(a)")
(di)                                     ; intro eps eigenvar E
(di)                                     ; asm pos-rr(E); goal forsome n . ...
(define E (cadr (asm-find-sub "pos-rr")))

;; delta from continuity at E
(define Craw (asm-find-sub "f(a), f(b)"))
(inst Craw E)
(detach! (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                         (equal? (cadr f) (list 'POS-RR E))))))
(ai (asm-find-sub "forall([b in x(s)]"))      ; existential-elim -> delta eigenvar
(ai (asm-find-sub "and forall([b in x(s)]"))  ; split (pos-rr(D) and CONT-INNER)
(define D (cadr (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'POS-RR)
                                               (not (equal? (cadr f) E)))))))

;; N from convergence at D
(define Kraw (asm-find-sub "(d(s))(g(n_), a)"))
(inst Kraw D)
(detach! (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                         (equal? (cadr f) (list 'POS-RR D))))))
(ai (asm-find-sub "forsome([n in nn]"))       ; existential-elim -> N eigenvar
(ai (asm-find-sub "nn and forall([n_ in nn]"))
(define Nw (cadr (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                (eq? (caddr f) 'NN))))))

;; witness n := N, intro n_, assume N <= n_
(ew Nw)
(di)
(focus-leaf! "n_4 in nn")                ; bounded-witness membership
(focus-leaf-goal! (list 'IN Nw 'NN)) (ass)
(focus-leaf! "(d(t))(f(g(n_))")
(di) (di)
(define M (cadr (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                               (eq? (caddr f) 'NN)
                                               (not (equal? (cadr f) Nw)))))))

;; convergence inner at M -> (d(s))(g(M),a) <= delta
(define conv-inner (asm-find-sub "n_ implies (d(s))(g(n_), a)"))
(inst conv-inner M)
(detach! (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                         (equal? (cadr f) (list 'IN M 'NN))))))
(detach! (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                         (equal? (cadr f) (list '<= Nw M))))))

;; term shorthands read off the actual (lowercase, folded) context
(define conv-res (asm-find-sub "(d(s))(g("))
(define Ds  (car (cadr conv-res)))       ; (d s)
(define gM  (list 'g M))
(define fa  (list 'f 'a))
(define fgM (list 'f gM))
(define Xs  (list 'X 's))
(define Xt  (list 'X 't))

;; memberships needed for the symmetry instances
(cut-mem! (list 'IN gM Xs) 'NN)          ; g(M) in x(s)
(cut-mem! (list 'IN fa Xt) Xs)           ; f(a) in x(t)
(cut-mem! (list 'IN fgM Xt) Xs)          ; f(g(M)) in x(t)

;; symmetry on s: turn (d(s))(g(M),a) into (d(s))(a,g(M)) <= delta
(metric-sym-eq! 's gM 'a)
(define symbound (list '<= (list Ds 'a gM) D))
(cut symbound)
(focus-leaf-goal! symbound)
(subst (list '= (list Ds 'a gM) (list Ds gM 'a)))   ; flip eq_s, rewrite goal -> conv-res
(ass)
(focus-leaf-asm! (expression->string symbound))

;; continuity at b := g(M) -> (d(t))(f(a), f(g(M))) <= eps
(define cont-inner (asm-find-sub "(d(s))(a, b) <= delta_3 implies"))
(inst cont-inner gM)
(detach! (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                         (equal? (cadr f) (list 'IN gM Xs))))))
(detach! (asm-find-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                         (equal? (cadr f) symbound)))))

;; symmetry on t: rewrite the goal (d(t))(f(g(M)),f(a)) -> (d(t))(f(a),f(g(M)))
(metric-sym-eq! 't fgM fa)
(let* ((gl  (cur-goal-raw))
       (lhs (cadr gl))
       (swp (list (car lhs) (caddr lhs) (cadr lhs))))
  (subst (list '= lhs swp)))
(ass)

;;; --- close ---
(if (proof-done? *ps*)
    (begin (qed 'converges-to-compose-continuous)
           (display ";; Prop 3.14 (=>) QED: converges-to-compose-continuous\n"))
    (error "prop-3-14-proof: NOT closed -- leaves remain"
           (map (lambda (s) (expression->string (sequent-node-assertion s))) (proof-leaves))))
