;;; calculus/quantifier-swap-stress.scm
;;; ====================================================================
;;; STRESS TEST -- the QUANTIFIER-ALTERNATION (a la nonstandard analysis) case
;;; that the A1-A4 toy examples in scout-eps-cauchy-record.scm hide.
;;;
;;; Easy swap:  exists f in FUBA. forall eps>0. GUBA(f,eps)
;;;        |--  forall eps>0. exists g in FUBA. GUBA(g,eps)        (g := f0)
;;;
;;; RESULT (2026-06-24): the UNGUARDED swap (drop the pos-rr guard) now CLOSES
;;; automatically -- scout branch:
;;;   (grind) (ew f0) (inst+ forall-eps.Q(f0,eps) AT eps) (grind) (ass) (ass).
;;; It took THREE search-guidance pieces, each found by stress-testing here:
;;;   1. grind SKOLEMIZES existential hypotheses (cmd-mac-h*) + intros eps -- the
;;;      structural prefix collapses into one ply (commit a063dc8);
;;;   2. the inst lane offers the EIGENVAR eps: an unguarded forall-var carries no
;;;      (IN _) type, so the typed-only pool never tried it -- added the
;;;      atomic-subterm-of-goal fallback the inst design always specified;
;;;   3. the effective-open metric DISCOUNTS trivially-closable leaves (ass/rfl),
;;;      so the post-ew AND-split (one conjunct is the typing hyp already in
;;;      context) isn't read as regress 1->2 and fled.
;;; Originally scout found 0 closing in 600 nodes: best-first had no downhill
;;; gradient through skolemize -> intro -> witness -> instantiate.
;;;
;;; STILL OPEN:
;;;   * the GUARDED swap below (inner `pos-rr(eps) implies ...') is NOT closed:
;;;     grind UNFOLDS pos-rr(eps) in the hyps into its conjuncts, destroying the
;;;     whole (pos-rr eps) that inst+'s detach needs -- a grind-unfold vs detach
;;;     tension (the hand-drive dodges it by using di, which keeps pos-rr folded).
;;;   * APPLIED WITNESSES -- ew cannot construct g := f(eps) (witness depends on
;;;     the goal's bound var), the genuine alphabet gap for e.g. the Cauchy
;;;     threshold N := null-threshold(eps/2).
;;;
;;; Run: VNB_SKIP_PROOFS=1 mit-scheme --quiet --load load.scm \
;;;        --load calculus/quantifier-swap-stress.scm --eval '(exit)' 2>&1 | grep ';;S'
;;; ====================================================================

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (ga) (and *ps* (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))
(define (find-head h) (let loop ((as (ga)))
  (cond ((null? as) #f) ((and (pair? (car as)) (eq? (caar as) h)) (car as)) (else (loop (cdr as))))))
(define (sho t)(display ";;S [")(display t)(display "] goal=")(write (gf))(newline)
  (display ";;S      asms=")(write (ga))(newline))
;; EASY SWAP: (exists f in FUBA. forall eps>0. GUBA(f,eps))  =>
;;            (forall eps>0. exists g in FUBA. GUBA(g,eps))
;; witness g := f0 (the skolem) -- a BARE context term.
(define SWAP '(IMPLIES
  (FORSOME f (AND (IN f FUBA) (FORALL eps (IMPLIES (POS-RR eps) (GUBA f eps)))))
  (FORALL eps (IMPLIES (POS-RR eps) (FORSOME g (AND (IN g FUBA) (GUBA g eps)))))))
(display ";;S ===== hand-drive =====\n")
(sp (make-wff SWAP))
(di)                                    ; antecedent -> hyp
(ai (find-head 'FORSOME))               ; skolemize exists f
(ai (find-head 'AND))                   ; split (IN f0 FUBA) & the universal
(sho "after skolemize+split")
(di)(di)                                ; intro eps, move POS-RR eps to hyp
(sho "goal now the existential, eps introduced")
(ew (cadr (find-head 'IN)))             ; witness g := f0 (the typed elt)
(sho "after ew g:=f0")
(di)                                    ; split the AND goal
(ass)                                   ; (IN f0 FUBA)
(inst+ (find-head 'FORALL) (let ((p (find-head 'POS-RR))) (cadr p)))  ; inst univ at eps + detach
(ass)
(display ";;S hand-drive done? ")(write (proof-done? *ps*))(newline)
(display ";;S ===== scout (depth 10) =====\n")
(sp (make-wff SWAP))
(let ((r (scout 10 3 600)))
  (display ";;S scout nodes=")(write (list-ref r 0))
  (display " closing=")(write (length (list-ref r 4)))
  (display " best-partials=")(write (length (list-ref r 3)))(newline)
  (when (pair? (list-ref r 4)) (display ";;S branch1=")(write (car (list-ref r 4)))(newline)))
