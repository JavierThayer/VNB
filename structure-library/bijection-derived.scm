;;; bijection-derived.scm -- the three BIJECTION projection lemmas, PROVEN.
;;;
;;; bijection-in-fun / bijection-injective / bijection-surjective were long
;;; ASSERTED in bijection.scm "for direct use", even though each is just one
;;; RHS conjunct of the definitional `bijection-membership-iff'.  They were
;;; pure phantom debt -- the same pattern subtype-laws.scm / metric-laws.scm
;;; retired: unfold the membership hypothesis with `mac-h', split the AND,
;;; and project (the FUN conjunct closes by assumption; the injective /
;;; surjective conjuncts are universals applied to the eigenvars by a small
;;; inst+detach driver).  Each is now PROVEN modulo 0.
;;;
;;; NOT retired here (genuinely more than a projection -- they need
;;; lambda-beta + VNB-LAMBDA typing / exists-intro / subclass-of-set
;;; separation, not just the iff): bijection-identity, bijection-compose,
;;; bijection-set-iff.  Those remain asserted (with warrants) in bijection.scm.
;;;
;;; Loaded after interactive + proof-debt (needs sp/di/mac-h/inst/bc/qed), in
;;; place of the axioms removed from bijection.scm.  Trivial + cheap, so NOT
;;; guarded by VNB_SKIP_PROOFS -- the names are always installed (as proven).

;;; --- local proof helpers (bd-- prefix; do not clobber globals) ----------
(define (bd--leaves)
  (filter (lambda (s) (and (not (sequent-node-grounded? s))
                           (null? (sequent-node-in-arrows s))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (bd--any p l) (let loop ((l l)) (cond ((null? l) #f) ((p (car l)) (car l)) (else (loop (cdr l))))))
(define (bd--goalof s) (wff-formula (sequent-node-assertion s)))
(define (bd--asms s) (sequent-node-assumptions s))
(define (bd--cur) (proof-state-focus *ps*))
(define (bd--hyp-sub substr)
  (let ((w (bd--any (lambda (w) (string-search-forward substr (expression->string (wff-formula w)) 0))
                    (bd--asms (bd--cur)))))
    (and w (wff-formula w))))
(define (bd--split-ands!)
  (let loop ()
    (let scan ((as (bd--asms (bd--cur))))
      (cond ((null? as) 'done)
            ((let ((f (wff-formula (car as)))) (and (pair? f) (eq? (car f) 'AND)))
             (ai (wff-formula (car as))) (loop))
            (else (scan (cdr as)))))))

;; refocus onto a leaf by goal / by assumption
(define (bd--focus-goal! G)
  (let ((s (bd--any (lambda (s) (equal? (bd--goalof s) G)) (bd--leaves))))
    (and s (set-proof-state-focus! *ps* s))))
(define (bd--focus-asm! G)
  (let ((s (bd--any (lambda (s) (bd--any (lambda (w) (equal? (wff-formula w) G)) (bd--asms s))) (bd--leaves))))
    (and s (set-proof-state-focus! *ps* s))))

;; structural substitution (ground value; respect shadowing binders)
(define (bd--subst f v val)
  (cond ((eq? f v) val)
        ((not (pair? f)) f)
        ((and (memq (car f) '(FORALL FORSOME)) (eq? (cadr f) v)) f)
        (else (cons (bd--subst (car f) v val) (bd--subst (cdr f) v val)))))

;; first-order match of pattern (holes = vars) against G; alist or #f
(define (bd--match pat G vars)
  (let ((subst '()))
    (define (go p g)
      (cond
        ((memq p vars)
         (let ((a (assq p subst)))
           (if a (equal? (cdr a) g) (begin (set! subst (cons (cons p g) subst)) #t))))
        ((and (pair? p) (pair? g) (= (length p) (length g)))
         (let lp ((p p) (g g)) (or (null? p) (and (go (car p) (car g)) (lp (cdr p) (cdr g))))))
        (else (equal? p g))))
    (and (go pat G) subst)))

;; peel leading FORALL/IMPLIES -> buried conclusion; the leading FORALL vars
(define (bd--concl f)
  (cond ((and (pair? f) (eq? (car f) 'FORALL)) (bd--concl (caddr f)))
        ((and (pair? f) (eq? (car f) 'IMPLIES)) (bd--concl (caddr f)))
        (else f)))
(define (bd--forall-vars f)
  (let loop ((f f) (vs '()))
    (cond ((and (pair? f) (eq? (car f) 'FORALL)) (loop (caddr f) (cons (cadr f) vs)))
          ((and (pair? f) (eq? (car f) 'IMPLIES)) (loop (caddr f) vs))
          (else (reverse vs)))))

;; detach: H=(IMPLIES A B) with A in ctx -> leave B in ctx, focus B-branch
(define (bd--detach! impl)
  (let ((B (caddr impl)))
    (cut B) (bd--focus-goal! B) (bc impl) (ass) (bd--focus-asm! B)))

;; drive a ctx FORALL*/IMPLIES* hyp H (whose conclusion matched the goal under
;; SUBST) to close the current atomic goal: instantiate each leading FORALL at
;; its matched value, detach each antecedent (in ctx), assume at the end.  The
;; final implication's consequent IS the goal, so backchain it directly --
;; cut-detaching there would auto-ground the assumption branch (goal in its own
;; context) and strand the focus.
(define (bd--use-hyp! H subst)
  (cond
    ((and (pair? H) (eq? (car H) 'FORALL))
     (let* ((v (cadr H)) (val (cdr (assq v subst))))
       (inst H val)
       (bd--use-hyp! (bd--subst (caddr H) v val) subst)))
    ((and (pair? H) (eq? (car H) 'IMPLIES))
     (if (equal? (caddr H) (bd--goalof (bd--cur)))
         (begin (bc H) (ass))
         (begin (bd--detach! H) (bd--use-hyp! (caddr H) subst))))
    (else (ass))))

;; close every open leaf: ass a direct hypothesis match; else find a
;; FORALL/IMPLIES hyp whose buried conclusion matches the goal and drive it.
(define (bd--close!)
  (let loop ((fuel 50))
    (when (> fuel 0)
      (let ((asl (bd--any (lambda (s) (bd--any (lambda (w) (alpha-equiv? (wff-formula w) (bd--goalof s)))
                                               (bd--asms s)))
                          (bd--leaves))))
        (cond
          (asl (set-proof-state-focus! *ps* asl) (ass) (loop (- fuel 1)))
          (else
           (let scan ((ls (bd--leaves)))
             (when (pair? ls)
               (let* ((s (car ls)) (g (bd--goalof s)))
                 (let ((hit (bd--any (lambda (w)
                                       (let ((f (wff-formula w)))
                                         (and (pair? f) (memq (car f) '(FORALL IMPLIES))
                                              (bd--match (bd--concl f) g (bd--forall-vars f)))))
                                     (bd--asms s))))
                   (if hit
                       (let ((H (wff-formula hit)))
                         (set-proof-state-focus! *ps* s)
                         (bd--use-hyp! H (bd--match (bd--concl H) g (bd--forall-vars H)))
                         (loop (- fuel 1)))
                       (scan (cdr ls)))))))))))))

;; di-count: how many di's to expose the membership hyp + peel the goal down
;; to the projected conclusion.
(define (bd--prove-projection! name di-count goal-sexpr)
  (sp (make-wff goal-sexpr))
  (let lp ((k di-count)) (when (> k 0) (di) (lp (- k 1))))
  (mac-h 'bijection-membership-iff (bd--hyp-sub "bijection"))
  (bd--split-ands!)
  (bd--close!)
  (if (proof-done? *ps*) (qed name)
      (error "bijection-derived: failed to prove" name)))

;;; --- the three projections ----------------------------------------------

;; phi in BIJECTION(X,Y) => phi in FUN(X,Y).  (FUN conjunct closes by ass.)
(bd--prove-projection! 'bijection-in-fun 1
  '(FORALL X (FORALL Y (FORALL phi
      (IMPLIES (IN phi (BIJECTION X Y)) (IN phi (FUN X Y)))))))

;; phi in BIJECTION(X,Y) => injective on X.
(bd--prove-projection! 'bijection-injective 2
  '(FORALL X (FORALL Y (FORALL phi
      (IMPLIES (IN phi (BIJECTION X Y))
               (FORALL a (IMPLIES (IN a X)
                 (FORALL b (IMPLIES (IN b X)
                   (IMPLIES (= (phi a) (phi b)) (= a b)))))))))))

;; phi in BIJECTION(X,Y) => surjective onto Y.  (Element vars w/z, not y/x:
;; the reader case-folds and y/x would capture against the class params Y/X.)
(bd--prove-projection! 'bijection-surjective 1
  '(FORALL X (FORALL Y (FORALL phi
      (IMPLIES (IN phi (BIJECTION X Y))
               (FORALL w (IMPLIES (IN w Y)
                 (FORSOME z (AND (IN z X) (= (phi z) w))))))))))
