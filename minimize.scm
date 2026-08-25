;;; minimize.scm -- `minimize!', the least-measure tactic.
;;;
;;;   (minimize! '(v1 ... vk) GUARD MEASURE)
;;;
;;; "Choose v1..vk satisfying GUARD with MEASURE as small as possible."
;;;
;;; GUARD is a formula and MEASURE an NN-valued term, both free in the vk.
;;; On the main branch the tactic lands two assumptions, for fresh
;;; eigenconstants w1..wk:
;;;
;;;     GUARD[v:=w]
;;;     (FORALL v1' ... (FORALL vk' (IMPLIES GUARD[v:=v']
;;;                                  (<= MEASURE[v:=w] MEASURE[v:=v']))))
;;;
;;; and opens exactly two side goals, returned to the caller in this order:
;;;
;;;     TYPE      (FORALL v1 ... (FORALL vk (IMPLIES GUARD (IN MEASURE NN))))
;;;     NONEMPTY  (FORSOME v1 ... (FORSOME vk GUARD))
;;;
;;; "MEASURE is a natural number wherever GUARD holds", and "GUARD holds
;;; somewhere".  Those are the only two things a minimization argument owes.
;;; Everything else -- forming the value set, well-ordering it, unpacking the
;;; witness, and re-expressing minimality in terms of the vk rather than in
;;; terms of the set -- is mechanical, and is what this tactic does.
;;;
;;; Return value: (list (w1 ... wk) TYPE-node NONEMPTY-node).  Focus is left on
;;; the caller's own goal; refocus to the two nodes to discharge them.
;;;
;;; Either node is #f when that obligation was ALREADY in context up to alpha
;;; and so was never cut -- nothing to prove, nothing to focus.  NONEMPTY is #f
;;; whenever the caller's own nonempty hypothesis has the shape minimize! would
;;; have asked for, which is the common case.  Test before refocusing.
;;;
;;; RESTRICTION: every vi must occur in MEASURE.  minimize! reads the
;;; eigenvariables di introduced back off the goal, and a vi absent from
;;; MEASURE leaves no trace there.  This is not a real limitation: a variable
;;; the measure ignores is not one you are minimizing over.
;;;
;;; WHY A TACTIC AND NOT A LEMMA.  The first-order statement
;;;     U in SET, f in FUN(U,NN), U nonempty  =>  some u0 in U minimizes f
;;; is true and provable, but unusable: every call site must tuple its vk into
;;; a CARTESIAN, build a VNB-LAMBDA, and prove that lambda inhabits FUN(U,NN).
;;; That typing obligation is bigger than the minimization it buys (see
;;; matrix.scm:492 for what one such obligation looks like written out).
;;; minimize! takes a formula and a term -- what a proof driver actually has in
;;; hand -- and never forms U at all.  It quantifies over the vk at the META
;;; level, so no schema enters the logic.
;;;
;;; SOUNDNESS.  minimize! adds no kernel rule.  It drives cut / di / ai / ew /
;;; sep-mi / sep-me / fact / inst / detach! / subst / ass / rfl exactly as a
;;; hand-written driver would, and its one appeal to mathematics is
;;; `nn-least-element' (theorem-library/nn-least-element.scm), which is proven
;;; from ord-well-ordered.  A proof using minimize! rests on nn-least-element
;;; and nothing else; in particular NO form of choice is used.  The reason is
;;; worth recording, because it is the whole trick: well-ordering hands back a
;;; MEMBER of the value set
;;;     T = { d in NN | FORSOME v. GUARD(v) and MEASURE(v) = d },
;;; and T is a SEP set, so `sep-me' turns that membership straight into the
;;; witnessing v.  The "now pick a minimizer" step that looks like it needs
;;; choice is separation-elimination.
;;;
;;; Loads after `interactive' (needs the tactic surface).  `nn-least-element'
;;; is resolved by name at CALL time, so this file may load before it.

;;; -----------------------------------------------------------------------
;;; Proof-state plumbing.  Every helper is mz-- prefixed: a top-level define
;;; whose name case-folds onto a tactic silently rebinds that tactic (see
;;; CLAUDE.md, "Case folding").

(define (mz--sqn)  (proof-state-focus *ps*))
(define (mz--goal) (wff-formula (sequent-node-assertion (mz--sqn))))
(define (mz--asms) (map wff-formula (sequent-node-assumptions (mz--sqn))))
(define (mz--foc! n) (set-proof-state-focus! *ps* n))

;; Open leaves: ungrounded, and not yet reduced by any rule.
(define (mz--leaves)
  (filter (lambda (n) (and (not (sequent-node-grounded? n))
                           (null? (sequent-node-in-arrows n))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))

;; Every tactic below must FIRE.  vnb--run! reports a miss by displaying a
;; warning and leaving *ps* alone -- and `quietly' suppresses the display -- so
;; a no-op would sail through and derail every later step in a different
;; branch.  Every primitive inference applies its rule to the FOCUSED node, so
;; "that node acquired an in-arrow" is a uniform success test (it holds even
;; for ass / rfl, which post no subgoal).
(define (mz--fire! label thunk)
  (let ((n (mz--sqn)))
    (thunk)
    (if (null? (sequent-node-in-arrows n))
        (error (string-append "minimize!: `" label "' did not fire on goal")
               (wff-formula (sequent-node-assertion n))))))

(define (mz-di)        (mz--fire! "di"      di))
(define (mz-ass)       (mz--fire! "ass"     ass))
(define (mz-rfl)       (mz--fire! "rfl"     rfl))
(define (mz-sep-mi)    (mz--fire! "sep-mi"  sep-mi))
(define (mz-ew t)      (mz--fire! "ew"      (lambda () (ew t))))
(define (mz-ai f)      (mz--fire! "ai"      (lambda () (ai f))))
(define (mz-mac m)     (mz--fire! "mac"     (lambda () (mac m))))
(define (mz-sep-me f)  (mz--fire! "sep-me"  (lambda () (sep-me f))))
(define (mz-inst f t)  (mz--fire! "inst"    (lambda () (inst f t))))
(define (mz-detach! f) (mz--fire! "detach!" (lambda () (detach! f))))
(define (mz-subst e)   (mz--fire! "subst"   (lambda () (subst e))))
(define (mz-fact n t)  (mz--fire! "fact"    (lambda () (fact n t))))

;; Suppress `show', but NOT the guard: a tactic that raises must say so.  Plain
;; `quietly' silences vnb-guard too, which turns any internal error into a
;; silent no-op -- and then minimize! keeps issuing commands into the wrong
;; branch and fails somewhere unrelated.
(define (mz--quietly thunk)
  (let ((saved *vnb-quiet*))
    (dynamic-wind (lambda () (set! *vnb-quiet* #t))
                  thunk
                  (lambda () (set! *vnb-quiet* saved)))))

(define (mz--dump-leaves! label ns)
  (display ";;; minimize! ") (display label) (display ":") (newline)
  (for-each (lambda (n)
              (display ";;;   ")
              (write (wff-formula (sequent-node-assertion n)))
              (newline))
            ns))

;; Run THUNK (a branching tactic) and hand back the leaves it opened, one per
;; goal in GOALS, in the caller's order.  Identifying branches by content is not
;; optional: dg-post! hash-conses sequent nodes, so "the last node created" is
;; not a reliable handle, and sibling branches routinely share a goal head.
(define (mz--branch! thunk . goals)
  (let ((before (mz--leaves))
        (focus  (mz--sqn)))
    (thunk)
    (if (null? (sequent-node-in-arrows focus))
        (error "minimize!: branching tactic did not fire on goal"
               (wff-formula (sequent-node-assertion focus))))
    (let ((new (filter (lambda (n) (not (memq n before))) (mz--leaves))))
      (map (lambda (g)
             (or (find-first
                  (lambda (n) (equal? (wff-formula (sequent-node-assertion n)) g))
                  new)
                 (begin (mz--dump-leaves! "opened" new)
                        (error "minimize!: no branch opened with goal" g))))
           goals))))

(define (mz--in-context? f)
  (let loop ((as (mz--asms)))
    (cond ((null? as) #f)
          ((alpha-equiv? (car as) f) #t)
          (else (loop (cdr as))))))

;; cut L under the current goal G.  Returns (cons side-node main-node): the
;; L-goal to prove, and the branch where L is available.  Focus is left on the
;; side node when there is one.
;;
;; When L is ALREADY in context (up to alpha) there is no cut to make, and
;; side-node is #f.  This is not an optimization.  dg-post! hash-conses sequent
;; nodes up to alpha-equivalence of the assertion and equality of the context,
;; and context-add-assumption is likewise alpha-idempotent -- so cutting an
;; in-context lemma yields a main branch that IS the focus node, i.e. a cycle
;; in the deduction graph, and only one leaf opens.  minimize! walks into it
;; every time NONEMPTY happens to be an alpha-variant of the caller's own
;; nonempty hypothesis, which is the usual case.  Same trap for a lemma
;; alpha-equal to the goal; there we refuse, since a minimization whose answer
;; is already the goal is a no-op the caller did not mean to write.
(define (mz--cut! l)
  (cond
    ((mz--in-context? l) (cons #f (mz--sqn)))
    ((alpha-equiv? l (mz--goal))
     (error "minimize!: cut lemma is an alpha-variant of the goal (cut would self-loop)" l))
    (else
     (let* ((g     (mz--goal))
            (nodes (mz--branch! (lambda () (cut l)) l g)))
       (mz--foc! (car nodes))
       (cons (car nodes) (cadr nodes))))))

;;; -----------------------------------------------------------------------
;;; Syntax.

(define (mz--forsome* vs body)
  (if (null? vs) body (list 'FORSOME (car vs) (mz--forsome* (cdr vs) body))))
(define (mz--forall* vs body)
  (if (null? vs) body (list 'FORALL (car vs) (mz--forall* (cdr vs) body))))

;; Iterated substitution.  Safe as a simultaneous one here because every
;; replacement is a fresh eigenconstant, so no vi occurs in any tj.
(define (mz--subst* vs ts e)
  (if (null? vs) e (mz--subst* (cdr vs) (cdr ts) (subst-free (car vs) (car ts) e))))

;; Recover the term that replaced the free variable V when OLD became NEW.
;; Eigenvariable names are not predictable -- fresh-var advances a global
;; counter, and di reuses the bound name only when it does not clash with the
;; context -- so read them back off the result instead of guessing.
(define (mz--align v old new)
  (cond
    ((eq? old v) new)
    ((or (not (pair? old)) (not (pair? new))) #f)
    ;; a binder that rebinds v shadows it: nothing of v's survives inside
    ((and (memq (car old) '(FORALL FORSOME)) (eq? (cadr old) v)) #f)
    ((and (eq? (car old) 'SEP) (eq? (cadr old) v))
     (mz--align v (caddr old) (caddr new)))      ; the range sits outside the binder
    ((not (= (length old) (length new))) #f)
    (else
     (let loop ((o old) (n new))
       (cond ((null? o) #f)
             ((mz--align v (car o) (car n)))
             (else (loop (cdr o) (cdr n))))))))

;;; -----------------------------------------------------------------------
;;; Context moves.

(define (mz--new-asms before)
  (filter (lambda (f) (not (member f before))) (mz--asms)))

;; (ai f) on a FORSOME assumption; returns (values eigenconstant instantiated-body).
(define (mz--ai-forsome f)
  (let ((x (cadr f)) (body (caddr f)) (before (mz--asms)))
    (mz-ai f)
    (let ((new (mz--new-asms before)))
      (if (null? new) (error "minimize!: ai on a FORSOME landed nothing" f))
      (let* ((inst (car new))
             (y    (mz--align x body inst)))
        (if (not y) (error "minimize!: cannot recover the eigenconstant for" x))
        (values y inst)))))

;; Peel k nested FORSOMEs; returns (values (y1 ... yk) body[v:=y]).
(define (mz--ai-forsome* f k)
  (let loop ((f f) (i 0) (ys '()))
    (if (= i k)
        (values (reverse ys) f)
        (call-with-values (lambda () (mz--ai-forsome f))
          (lambda (y inst) (loop inst (+ i 1) (cons y ys)))))))

;; Split an in-context (AND p q); returns (values p q).
(define (mz--ai-and f) (mz-ai f) (values (cadr f) (caddr f)))

;; From an in-context (FORALL v1 ... (IMPLIES GUARD (IN MEASURE NN))) land
;; (IN MEASURE[v:=ts] NN).  `inst' peels one universal per call and keeps the
;; universal in context; the guard is then detached against the GUARD[v:=ts]
;; that the caller has already put there.
(define (mz--type-at! type ts)
  ;; nested-quantifier peel: one subst-free per binder, under the binders that
  ;; remain (see proof-commands.scm's cmd-fact).  A substitution LIST would need
  ;; subst-free* -- expressions.scm.
  (let loop ((f type) (ts ts))
    (if (null? ts)
        (begin (mz-detach! f) (caddr f))         ; f = (IMPLIES GUARD (IN M NN))
        (begin (mz-inst f (car ts))
               (loop (subst-free (cadr f) (car ts) (caddr f)) (cdr ts))))))

;;; -----------------------------------------------------------------------
;;; Close the goal (IN MEASURE[ts] T).
;;;
;;; sep-mi splits it into the NN-typing and the witnessing instance of the SEP
;;; body.  BOTH subgoals inherit the context as it stands NOW, which is why
;;; (IN MEASURE[ts] NN) must be landed by the caller before this runs and not
;;; inside the first subgoal: the second subgoal's `rfl' needs it too, since in
;;; VNB `t = t' asserts that t is defined.

(define (mz--in-sep! tee vars guard ts mts)
  (let* ((d    (cadr tee))
         (body (subst-free d mts (cadddr tee)))          ; FORSOME v.. (AND G (= M mts))
         (nodes (mz--branch! mz-sep-mi (list 'IN mts 'NN) body)))
    (mz--foc! (car nodes)) (mz-ass)
    (mz--foc! (cadr nodes))
    (for-each mz-ew ts)                                  ; goal (AND G[ts] (= mts mts))
    (let ((gs (mz--branch! mz-di (mz--subst* vars ts guard) (list '= mts mts))))
      (mz--foc! (car gs)) (mz-ass)
      (mz--foc! (cadr gs)) (mz-rfl))))

;;; -----------------------------------------------------------------------
;;; minimize!

(define (minimize! vars guard measure)
  (vnb--require-proof!)
  ;; RECORD ITSELF, not its expansion -- same reason as `prop' (prop.scm) and the
  ;; other half of the `dk-focus!' repair.  minimize! drives its own branches, so
  ;; a script of its internals replays them against engine-chosen leaves; and its
  ;; three arguments are DATA (a variable list, a guard formula, a measure term),
  ;; so the call re-emits exactly.  One line in a script instead of forty, and it
  ;; runs.
  (let* ((mark (vnb--take-mark (cons 'minimize! (list vars guard measure))))
         (r (fluid-let ((*replaying?* #t))
              (mz--quietly (lambda () (mz--run! vars guard measure))))))
    ;; Mark taken OUTSIDE the fluid-let, beside the record-cmd! and for the same
    ;; reason: minimize! records itself, so backup-one takes back the whole
    ;; minimisation rather than its last internal step.
    (vnb--undo-push! mark)
    (record-cmd! 'minimize! (list vars guard measure))
    r))

(define (mz--run! vars guard measure)
  (let* ((k        (length vars))
         (avoid    (list guard measure (mz--goal)))
         (d        (apply fresh-var 'd avoid))
         (pvars    (let loop ((vs vars) (acc '()) (av avoid))
                     (if (null? vs) (reverse acc)
                         (let ((p (apply fresh-var (car vs) av)))
                           (loop (cdr vs) (cons p acc) (cons p av))))))
         ;; T = { d in NN | FORSOME v1..vk. GUARD and MEASURE = d }
         (tee      (list 'SEP d 'NN
                         (mz--forsome* vars (list 'AND guard (list '= measure d)))))
         (type     (mz--forall* vars (list 'IMPLIES guard (list 'IN measure 'NN))))
         (nonempty (mz--forsome* vars guard))
         (pguard   (mz--subst* vars pvars guard))
         (pmeasure (mz--subst* vars pvars measure))
         ;; MIN = FORSOME v. GUARD and (FORALL v'. GUARD' => MEASURE <= MEASURE')
         (minimal  (mz--forsome*
                    vars (list 'AND guard
                               (mz--forall* pvars
                                            (list 'IMPLIES pguard
                                                  (list '<= measure pmeasure))))))
         (nn0      (fresh-var 'n tee))
         (subset-g (list 'SUBSET tee 'NN))
         (ne-g     (list 'FORSOME nn0 (list 'IN nn0 tee)))
         (ante     (list 'AND subset-g ne-g)))

    ;; ---- 0. cut in MIN; `main' is the caller's branch, with MIN in context
    (let* ((c-min  (mz--cut! minimal))
           (main   (cdr c-min)))
      (if (not (car c-min))
          (error "minimize!: the minimality statement is already in context" minimal))
      ;; ---- 1. the caller's two obligations.  Cut them in and leave them open.
      ;; Either may come back #f: the caller already had it in context.
      (let* ((c-type (mz--cut! type))
             (t-goal (car c-type)))
        (mz--foc! (cdr c-type))
        (let* ((c-ne   (mz--cut! nonempty))
               (n-goal (car c-ne)))
          (mz--foc! (cdr c-ne))

        ;; ---- 2. the antecedent of nn-least-element: T subset NN, T nonempty
        (let ((main-a (cdr (mz--cut! ante))))
          (let ((cs (mz--branch! mz-di subset-g ne-g)))

            ;; (SUBSET T NN): unfold, peel, and read the membership back off T
            (mz--foc! (car cs))
            (mz-mac 'subset-def)                 ; FORALL x. x in T => x in NN
            (mz-di)                              ; peels the forall, absorbs the bound
            (let ((xx (cadr (mz--goal))))        ; goal (IN xx NN)
              (mz-sep-me (list 'IN xx tee))      ; gains (IN xx NN)
              (mz-ass))

            ;; (FORSOME n. n in T): witness MEASURE at any GUARD witness
            (mz--foc! (cadr cs))
            (call-with-values (lambda () (mz--ai-forsome* nonempty k))
              (lambda (us guard-u)
                (mz--type-at! type us)           ; (IN MEASURE[us] NN)
                (let ((mu (mz--subst* vars us measure)))
                  (mz-ew mu)
                  (mz--in-sep! tee vars guard us mu)))))

          ;; ---- 3. well-order T, unpack its least element
          (mz--foc! main-a)
          (let ((before (mz--asms)))
            (mz-fact 'nn-least-element tee)
            (let ((le (let loop ((fs (mz--new-asms before)))
                        (cond ((null? fs)
                               (error "minimize!: nn-least-element landed nothing"))
                              ((eq? (car (car fs)) 'FORSOME) (car fs))
                              (else (loop (cdr fs)))))))
              (call-with-values (lambda () (mz--ai-forsome le))
                (lambda (m0 body)
                  ;; body = (AND (IN m0 T) (FORALL kk. kk in T => m0 <= kk))
                  (call-with-values (lambda () (mz--ai-and body))
                    (lambda (mem min0)
                      (mz-sep-me mem)            ; gains (IN m0 NN) and the SEP body at m0
                      (let ((exf (subst-free d m0 (cadddr tee))))
                        (call-with-values (lambda () (mz--ai-forsome* exf k))
                          (lambda (ws body-w)
                            (call-with-values (lambda () (mz--ai-and body-w))
                              (lambda (guard-w eqn)  ; eqn = (= MEASURE[ws] m0)

                                ;; ---- 4. discharge MIN with the witnesses ws
                                (for-each mz-ew ws)
                                (let* ((mw    (mz--subst* vars ws measure))
                                       (left  (mz--subst* vars ws guard))
                                       (right (mz--forall*
                                               pvars (list 'IMPLIES pguard
                                                           (list '<= mw pmeasure))))
                                       (bs    (mz--branch! mz-di left right)))
                                  (mz--foc! (car bs)) (mz-ass)
                                  (mz--foc! (cadr bs))
                                  (mz-di)        ; peel the pvars (maybe the IMPLIES too)
                                  (if (eq? (car (mz--goal)) 'IMPLIES) (mz-di))
                                  ;; goal (<= mw MEASURE[zs]); GUARD[zs] in context
                                  (let* ((mz (caddr (mz--goal)))
                                         (zs (map (lambda (p)
                                                    (or (mz--align p pmeasure mz)
                                                        (error "minimize!: variable absent from MEASURE" p)))
                                                  pvars)))
                                    (mz--type-at! type zs)   ; (IN MEASURE[zs] NN)
                                    (let ((main-i (cdr (mz--cut! (list 'IN mz tee)))))
                                      (mz--in-sep! tee vars guard zs mz)
                                      (mz--foc! main-i)
                                      (mz-subst eqn)         ; mw -> m0 in the goal
                                      (mz-inst min0 mz)
                                      (mz-detach! (list 'IMPLIES (list 'IN mz tee)
                                                        (list '<= m0 mz)))
                                      (mz-ass))))))))))))))))

        ;; ---- 5. back on the caller's branch: skolemize MIN into context
        (mz--foc! main)
        (call-with-values (lambda () (mz--ai-forsome* minimal k))
          (lambda (ws body)
            (mz-ai body)                         ; split GUARD[ws] from minimality
            (list ws t-goal n-goal))))))))
