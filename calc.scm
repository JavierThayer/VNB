;;; calc.scm -- the "directive chain checker" (notes-27): ground a goal by a
;;; chain of intermediaries, proving each link and composing them.
;;;
;;;   (calc L0 (rel1 L1 just1) (rel2 L2 just2) ... (reln Ln justn))
;;;
;;; grounds the CURRENT focus goal  (REL L0 Ln)  by the chain
;;;   L0  rel1  L1  rel2  L2  ...  reln  Ln
;;; proving each LINK  (reli L(i-1) Li)  by a dispatched lane, then COMPOSING
;;; the links into the endpoint.  A link no lane closes is LEFT OPEN as a leaf --
;;; the refinement point: insert more intermediaries until each link is
;;; discoverable, or cite a lemma.  Pure bookkeeping over the trusted tactics --
;;; no kernel rule, no axiom.  Three composer families, forced by the logic:
;;;   'cong  (=, ==)  fold by transitivity (eq-trans).
;;;   'iff           di the goal into its two implication directions, chain each
;;;                  with ai/detach! (VNB cannot quantify over propositions, so
;;;                  there is no first-order iff-trans lemma).
;;;   'order (<, <=)  fold a running relation through the co-*-trans lemmas;
;;;                  = steps ride along as rewrites.  Link lane = NN->RR bridge
;;;                  then ineq over the order-shaped premises.
;;;
;;; Justification (justi), optional, defaults to 'auto:
;;;   'auto        try the relation's lanes; else leave OPEN
;;;   'scout       a small scout search
;;;   'open / #f   leave the link OPEN (a deliberate refinement placeholder)
;;;   <symbol>     a macete/theorem name: (mac <symbol>) then close
;;;   (t . args)   an explicit tactic form, eval'd at the link's focus
;;;
;;; RETURNS (and prints) an alist: done, composer, composed-rel, goal, links,
;;; open, pss-candidates (each = formula + free-vars + context-typing).  The
;;; open links are the isolated obstacles / PSS candidates.
;;;
;;; LOAD ORDER: after interactive (tactics), driver-kit (dc-focus!/dc-open-leaves),
;;; proof-debt, and structure-library/{order-lemmas,ineq-oracle} (the co-*-trans /
;;; nn-pos-of-nonzero / nn-in-rr / eq-trans supports and the ineq oracle).  The
;;; composition lemmas live in order-lemmas.scm; this file only USES them.

;;; ---- relation registry: rel -> (composer default-lanes) ----------------
(define *calc-rel-registry*
  ;; composer: 'cong (=,==) | 'iff | 'order (<,<=)
  ;; lanes: thunks tried in order by 'auto
  (list
    (list '=   'cong  (list (lambda () (crs)) (lambda () (arith))))
    (list '==  'cong  (list (lambda () (crs)) (lambda () (arith))))
    (list 'IFF 'iff   (list (lambda () (grind))))
    (list '<   'order (list (lambda () (calc--order-close!))))
    (list '<=  'order (list (lambda () (calc--order-close!))))))

;; order fold: (Racc . Ri) -> (lemma . Rnew).  < / <= combinations plus = steps
;; interleaved (refinement rewrites one endpoint of the running relation).
(define *calc-order-trans*
  (list (cons '(<= . <=) (cons 'rr-le-trans-c    '<=))
        (cons '(<= . <)  (cons 'co-le-lt-trans '<))
        (cons '(<  . <=) (cons 'co-lt-le-trans '<))
        (cons '(<  . <)  (cons 'co-lt-trans    '<))
        (cons '(<= . =)  (cons 'co-le-eq-trans '<=))
        (cons '(<  . =)  (cons 'co-lt-eq-trans '<))
        (cons '(=  . <=) (cons 'co-eq-le-trans '<=))
        (cons '(=  . <)  (cons 'co-eq-lt-trans '<))
        (cons '(=  . =)  (cons 'eq-trans       '=))))

(define (calc--reg rel)
  (or (assq rel *calc-rel-registry*)
      (error "calc: no registry entry for relation" rel)))

;;; ---- small helpers over the live proof state ---------------------------
(define (calc--goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (calc--alpha=? a b) (alpha-equiv? a b))
(define (calc--in-ctx? raw)
  (any-pred (lambda (a) (alpha-equiv? a raw))
            (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))

;;; ---- the order link lane: NN->RR bridge, then ineq over order premises -----
;;; Bare (ineq) passes ZERO premises to pi-ineq!, and its atoms must be RR-
;;; certified.  So gather the order-shaped assumptions and bridge every
;;; (IN v NN) to (IN v RR) first.  Each proc returns a value.
(define (calc--ctx-asms)                 ; the focus context, as raw formulas
  (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (calc--nn-typed-vars)            ; -> list of v with (IN v NN) in context
  (let loop ((as (calc--ctx-asms)) (acc '()))
    (cond ((null? as) (reverse acc))
          ((and (pair? (car as)) (eq? (caar as) 'IN) (eq? (caddr (car as)) 'NN))
           (loop (cdr as) (cons (cadr (car as)) acc)))
          (else (loop (cdr as) acc)))))
(define (calc--nn-rr-bridge!)            ; land (IN v RR) for each NN var; -> the v's
  (let ((vs (calc--nn-typed-vars)))
    (for-each (lambda (v) (vnb-guard (lambda () (fact 'nn-in-rr v)))) vs)
    vs))
(define (calc--order-premises)           ; -> 1-based indices of order/eq assumptions
  (let loop ((as (calc--ctx-asms)) (i 1) (acc '()))
    (cond ((null? as) (reverse acc))
          ((and (pair? (car as)) (memq (caar as) '(< <= = ==)))
           (loop (cdr as) (+ i 1) (cons i acc)))
          (else (loop (cdr as) (+ i 1) acc)))))
(define (calc--order-close!)             ; bridge + ineq w/ premises; -> idxs used
  (calc--nn-rr-bridge!)
  (let ((idxs (calc--order-premises)))
    (vnb-guard (lambda () (apply ineq idxs)))
    idxs))

;;; Try to close the CURRENT focus goal with the lanes / justification.
;; NODE is the link's leaf, captured before dispatch.  A tactic that closes the
;; focus AUTO-ADVANCES *ps* to another leaf, so we must test NODE itself, never
;; the current focus, to know whether the link closed.  Tactics already run in
;; vnb--run!'s guard (return #f, never raise); vnb-guard here catches the ones
;; that don't (scout, an eval'd form), so a bad link never aborts the chain.
(define (calc--try th node)
  (vnb-guard th)                          ; swallow any hard error
  (sequent-node-grounded? node))
(define (calc--discharge just rel node)   ; -> 'closed | 'open | 'error
  (cond
    ((or (eq? just 'open) (eq? just #f)) 'open)
    ((eq? just 'auto)
     (let loop ((lanes (caddr (calc--reg rel))))
       (cond ((null? lanes) 'open)
             ((calc--try (car lanes) node) 'closed)
             (else (loop (cdr lanes))))))
    ((eq? just 'scout)                     ; explicit small-scout lane
     (if (calc--auto-scout? node) 'closed 'open))
    ((symbol? just)                        ; a macete/theorem name
     (if (calc--try (lambda () (mac just) (ass)) node) 'closed 'open))
    ((pair? just)                          ; an explicit tactic form
     (if (calc--try (lambda () (eval just user-initial-environment)) node)
         'closed 'open))
    (else 'error)))

(define *calc-scout-depth* 3)
(define *calc-scout-branch* 4)
(define (calc--auto-scout? node)
  ;; a small scout; adopt branch 1 if it closes.  Probe then commit.  #t iff NODE closed.
  (let ((res (vnb-guard (lambda () (scout *calc-scout-depth* *calc-scout-branch*)))))
    (and (not (vnb-error? res)) (pair? res) (>= (length res) 5) (pair? (list-ref res 4))
         (begin (vnb-guard (lambda () (scout-run 1)))
                (sequent-node-grounded? node)))))

;;; ---- the composers -----------------------------------------------------
;;; After all links (reli L(i-1) Li) are proved into context, close (REL L0 Ln).

;; 'cong: fold by transitivity.  For = / == the curried untyped eq-trans lets a
;; forward `fact' land (= L0 Li) from (= L0 L(i-1)) and (= L(i-1) Li) in context.
(define (calc--compose-cong rel lines)
  ;; lines = (L0 L1 ... Ln).  Accumulator (= L0 prev) starts as link 1 = (= L0 L1);
  ;; fold L2..Ln through eq-trans.  Returns rel.
  (let ((L0 (car lines)))
    (let loop ((prev (cadr lines)) (rest (cddr lines)))
      (if (null? rest)
          rel
          (let ((Li (car rest)))
            (fact 'eq-trans L0 prev Li)   ; from (= L0 prev),(= prev Li) land (= L0 Li)
            (loop Li (cdr rest)))))))

;; 'iff: di-ing the (IFF L0 Ln) goal yields TWO leaves -- one ASSERTING Ln with
;; L0 assumed (forward), one asserting L0 with Ln assumed (backward).  Each iff
;; link (IFF l(i-1) li) is in context; `ai' on it lands BOTH implication
;; directions, so we detach the one the walk needs.  No inner di: di on the iff
;; already discharged the implication and moved the antecedent into context.
(define (calc--compose-iff lines)
  (let* ((L0 (car lines)) (Ln (car (reverse lines)))
         (pairs (map cons lines (cdr lines))))   ; ((l0.l1)(l1.l2)...)
    (di)                                          ; iff-intro
    ;; forward: assert Ln, L0 assumed; walk l0 -> l1 -> ... -> ln
    (dc-focus! Ln)
    (for-each (lambda (p)
                (ai `(IFF ,(car p) ,(cdr p)))
                (detach! `(IMPLIES ,(car p) ,(cdr p))))   ; lands (cdr p)
              pairs)
    (ass)
    ;; backward: assert L0, Ln assumed; walk ln -> ... -> l0 (reverse direction)
    (dc-focus! L0)
    (for-each (lambda (p)
                (ai `(IFF ,(car p) ,(cdr p)))
                (detach! `(IMPLIES ,(cdr p) ,(car p))))   ; lands (car p)
              (reverse pairs))
    (ass)
    'IFF))

;; 'order: fold in context.  Accumulator (Racc L0 Lcur) starts as link 1; each
;; next link (Ri Lcur Li) combines via the (Racc,Ri) trans lemma, landing
;; (Rnew L0 Li).  Final (REL L0 Ln) is in context -> ass.  Returns the final rel.
(define (calc--compose-order rels lines)
  (let ((L0 (car lines)))
    (let loop ((racc (car rels)) (prev (cadr lines))
               (rs (cdr rels)) (ls (cddr lines)))
      (if (null? rs)
          (begin (ass) racc)
          (let* ((ri    (car rs)) (Li (car ls))
                 (entry (assoc (cons racc ri) *calc-order-trans*))
                 (lemma (cadr entry)) (rnew (cddr entry)))
            (fact lemma L0 prev Li)               ; lands (rnew L0 Li)
            (loop rnew Li (cdr rs) (cdr ls)))))))

;;; ---- main --------------------------------------------------------------
(define (calc--composer-of rel) (cadr (calc--reg rel)))
;; Pick ONE composer from the whole relation SET.  = / == belong to cong on their
;; own, but ride an order chain as interleaved rewrite steps -- so a chain with
;; any < or <= is an order chain even when it also contains = steps.
(define (calc--pick-composer rels)
  (cond
    ((calc--every rels (lambda (r) (eq? r 'IFF))) 'iff)
    ((calc--every rels (lambda (r) (memq r '(= ==)))) 'cong)
    ((calc--every rels (lambda (r) (memq r '(< <= =)))) 'order)
    (else (error "calc: chain mixes incompatible relations" rels))))
(define (calc--composed-rel composer rels)   ; the endpoint relation a chain proves
  (case composer
    ((order) (if (memq '< rels) '< '<=))     ; strict iff any strict step
    ((cong)  (if (memq '== rels) '== '=))
    ((iff)   'IFF)
    (else (car rels))))

(define (calc L0 . steps)
  ;; steps: each (rel Li [just])
  (let* ((goal  (calc--goal))
         (rels  (map car steps))
         (lines (cons L0 (map cadr steps)))
         (justs (map (lambda (s) (if (>= (length s) 3) (caddr s) 'auto)) steps))
         (composer (calc--pick-composer rels))
         (comp-rel (calc--composed-rel composer rels))
         (mainraw goal)
         (records '()))
    ;; sanity: endpoints + composed relation match the goal
    (unless (and (pair? goal) (eq? (car goal) comp-rel))
      (error "calc: goal head /= composed relation" (and (pair? goal) (car goal)) comp-rel))
    (unless (calc--alpha=? (cadr goal) L0)
      (error "calc: goal LHS /= L0" (cadr goal) L0))
    (unless (calc--alpha=? (caddr goal) (car (reverse lines)))
      (error "calc: goal RHS /= Ln" (caddr goal) (car (reverse lines))))
    ;; prove each link, then compose -- all under `quietly' so the per-tactic
    ;; `show' noise is suppressed; closure is read off the captured node, not
    ;; output, so silencing is safe.  The report below prints normally.
    (quietly
     (lambda ()
      (let loop ((prev L0) (rs (cdr lines)) (rlist rels) (js justs))
        (when (pair? rs)
          (let* ((Li   (car rs))
                 (ri   (car rlist))
                 (just (car js))
                 (link `(,ri ,prev ,Li)))
            ;; A link already in the main context is a GIVEN -- cutting it would
            ;; be an alpha self-loop (no new leaf), so skip the cut and record it
            ;; closed.  Check BEFORE cutting, while focus is on the main goal.
            (if (calc--in-ctx? link)
                (set! records (cons (list ri prev Li just 'closed) records))
                (begin
                  (cut link)
                  (let* ((node   (dc-focus! link))
                         (status (calc--discharge just ri node)))
                    (set! records (cons (list ri prev Li just status) records)))
                  (dc-focus! mainraw)))
            (loop Li (cdr rs) (cdr rlist) (cdr js)))))
      (set! records (reverse records))))
    ;; compose iff every link closed
    (let ((all-closed (calc--every records (lambda (r) (eq? (list-ref r 4) 'closed)))))
      (when all-closed
        (quietly
         (lambda ()
           (dc-focus! mainraw)
           (vnb-guard
            (lambda ()
              (case composer
                ((cong)  (calc--compose-cong '= lines) (ass) (rfl))
                ((iff)   (calc--compose-iff lines))
                ((order) (calc--compose-order rels lines))))))))
      ;; Build and RETURN the structured result (also printed by calc--report).
      (calc--report (calc--result records composer comp-rel mainraw)))))

(define (calc--every lst p) (or (null? lst) (and (p (car lst)) (calc--every (cdr lst) p))))

;;; ---- the result value: usable obstacle + PSS-candidate data -------------
;; A link record (rel from to just status) -> an alist with its formula.
(define (calc--record->alist r)
  (list (cons 'rel (car r)) (cons 'from (cadr r)) (cons 'to (caddr r))
        (cons 'just (cadddr r)) (cons 'status (list-ref r 4))
        (cons 'formula (list (car r) (cadr r) (caddr r)))))
;; Free variables = symbols in ARGUMENT position (the head/car of every compound
;; is an operator, so skip it).  Returns the variable list, no duplicates.
(define (calc--free-vars form)
  (reverse
   (let walk ((f form) (acc '()))
     (cond ((symbol? f) (if (memq f acc) acc (cons f acc)))
           ((pair? f) (fold-left (lambda (a x) (walk x a)) acc (cdr f)))
           (else acc)))))
;; The OPEN links are the obstacles; each yields a PSS candidate (its formula,
;; the free variables to close over, and the context typing of those vars).
(define (calc--result records composer comp-rel goal)
  (let* ((open  (filter (lambda (r) (not (eq? (list-ref r 4) 'closed))) records))
         (typing (filter (lambda (a) (and (pair? a) (eq? (car a) 'IN))) (calc--ctx-asms)))
         (cands (map (lambda (r)
                       (let ((form (list (car r) (cadr r) (caddr r))))
                         (list (cons 'formula form)
                               (cons 'free-vars (calc--free-vars form))
                               (cons 'context-typing typing))))
                     open)))
    (list (cons 'done (proof-done? *ps*))
          (cons 'composer composer)
          (cons 'composed-rel comp-rel)
          (cons 'goal goal)
          (cons 'links (map calc--record->alist records))
          (cons 'open (map calc--record->alist open))
          (cons 'pss-candidates cands))))

;; Print a human report AND return the result value unchanged.
(define (calc--report result)
  (let* ((links (cdr (assq 'links result)))
         (open  (cdr (assq 'open result)))
         (cands (cdr (assq 'pss-candidates result)))
         (records (map (lambda (a) (list (cdr (assq 'rel a)) (cdr (assq 'from a))
                                         (cdr (assq 'to a)) (cdr (assq 'just a))
                                         (cdr (assq 'status a)))) links)))
  (newline)
  (display ";; calc: ") (display (length records)) (display " link(s)")
  (display (if (null? open) ", all closed" ""))
  (display "; done? ") (display (cdr (assq 'done result)))
  (display "; open leaves: ") (display (length (dc-open-leaves))) (newline)
  (for-each
   (lambda (r)
     (display ";;   [") (display (list-ref r 4)) (display "] ")
     (display (expression->string (cadr r))) (display "  ")
     (display (car r)) (display "  ")
     (display (expression->string (caddr r)))
     (unless (eq? (cadddr r) 'auto)
       (display "   (") (display (cadddr r)) (display ")"))
     (newline))
   records)
  ;; PSS candidates: the open links, as formulas a support could discharge.
  (when (pair? cands)
    (display ";; PSS candidate(s) -- open links to close, refine, or promote:\n")
    (for-each
     (lambda (c)
       (let ((form (cdr (assq 'formula c))) (fv (cdr (assq 'free-vars c))))
         (display ";;   ") (display (expression->string form))
         (when (pair? fv)
           (display "   [free: ") (display fv) (display "]"))
         (newline)))
     cands))
  result))
