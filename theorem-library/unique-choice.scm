;;; unique-choice.scm -- wave of 2026-11-09/10 (agent CCR-1109-D4), wired 2026-11-10 from scratchpad/ccr1109d4/unique-choice.scm.
;;; Library: core.

;;; unique-choice.scm -- UNIQUE CHOICE INTO A FUNCTION (the function defined by a relation that is
;;; functional on its domain).  Agent CCR-1109-D4, 2026-11-09.  Destination: theorem-library/unique-choice.scm.
;;; Library: core (it mentions only FUN, CARTESIAN, IOTA, VNB-LAMBDA and SET).  Helper prefix ucf-.
;;;
;;;   uniq-choice-fun     If A is a set and for every x in A there is exactly one c in C with c in Q(x),
;;;                       there is f in FUN(A, C) with f(x) in Q(x) for every x in A.
;;;   uniq-choice-fun-2   If A, B are sets and for every x in A, y in B there is exactly one c in C with
;;;                       c in Q(x, y), there is f in FUN(CARTESIAN(A, B), C) with f(x, y) in Q(x, y).
;;;
;;; The relation is given, as in dc-on-nn-pred, by a set-valued application Q(x) (resp. Q(x, y)): a caller
;;; instantiates Q at VNB-LAMBDA x_ A (SEP c_ C phi(x_, c_)) (resp. a two-binder lambda) and reduces it with
;;; dk-lam-b! / dk-lam-b-h!.  The witness is the lambda of the description,
;;;   f = VNB-LAMBDA x_ A (IOTA c_ (c_ in C and c_ in Q(x_))),
;;; typed by lam-t and iota-d (the existence-and-uniqueness obligation is the hypothesis), its values read by
;;; lam-b and iota-d again.  No AC, no CHOICE.  The tree had neither form (THEOREMS.md, 2026-11-09: the
;;; IOTA-built functions -- MATOF, DERIV, the D-functoids -- are each built for one relation).
;;;
;;; Load window: lo = the latest of its citations, which are none: it uses only kernel rules (lam-t, lam-b,
;;; iota-d) and the kit (dk-set-close! cites cartesian-set-iff, structure-library).  So any slot after
;;; driver-kit and interactive; hi = its first citer (theorem-library/ccr6-f.scm).  Proposed slot: beside
;;; theorem-library/rake-dc-on-nn (the other choice-into-a-function theorem).

(define (ucf-close!)
  (let ((g (dk-goal)))
    (cond ((dk-asm? g) (dk-ass!))
          ((dk-head-is? g 'AND) (dk-conj-close! ucf-close!))
          (#t (error "ucf-close!: unexpected goal" (expression->string g))))))

;; the existence-and-uniqueness leaf of iota-d, from HINST = (FORSOME c (AND (IN c C) (AND (IN c Q)
;; (FORALL d (IMPLIES (IN d C) (IMPLIES (IN d Q) (= d c))))))) in context
(define (ucf-exuniq! hinst)
  (let* ((c0 (dk-skolem! hinst))
         (uq (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f c0))) "uniqueness")))
    (ew c0)
    (dk-conj-close!
      (lambda ()
        (let ((g (dk-goal)))
          (cond ((dk-asm? g) (dk-ass!))
                ((dk-head-is? g 'FORALL)
                 (let* ((landed (dk-peel!)) (gl (dk-goal)) (yy (caddr gl)))
                   (dk-split-all! landed)
                   (dk-apply! uq yy)
                   (subst `(= ,c0 ,yy))
                   (rfl)))
                (#t (error "ucf-exuniq!: unexpected goal" (expression->string g)))))))))

;; drive (iota-d IO) on the focus leaf: the obligation from HINST, the main leaf from the defining property
(define (ucf-iota! io hinst)
  (for-each (lambda (leaf)
              (if (not (sequent-node-grounded? leaf))
                  (begin
                    (dk-focus! leaf)
                    (if (dk-head-is? (dk-goal) 'FORSOME)
                        (ucf-exuniq! hinst)
                        (begin (dk-split-all!) (ucf-close!))))))
            (dk-opened (lambda () (iota-d io)))))

;; the hypothesis of the statement, from context
(define (ucf-hyp)
  (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'FORSOME))) "the unique-existence hypothesis"))

;;; -----------------------------------------------------------------------
;;; one variable

(sp (make-wff '(FORALL uca (IMPLIES (IN uca SET) (FORALL ucc (FORALL ucq
  (IMPLIES (FORALL ucx (IMPLIES (IN ucx uca)
             (FORSOME ucy (AND (IN ucy ucc) (AND (IN ucy (ucq ucx))
               (FORALL ucz (IMPLIES (IN ucz ucc) (IMPLIES (IN ucz (ucq ucx)) (= ucz ucy)))))))))
    (FORSOME ucf_ (AND (IN ucf_ (FUN uca ucc)) (FORALL ucx (IMPLIES (IN ucx uca) (IN (ucf_ ucx) (ucq ucx)))))))))))))
(dk-peel!)
(let ((h (ucf-hyp)))
  (ew '(VNB-LAMBDA ucs_ uca (IOTA uci_ (AND (IN uci_ ucc) (IN uci_ (ucq ucs_))))))
  (dk-conj-close!
    (lambda ()
      (let ((g (dk-goal)))
        (if (dk-head-is? g 'IN)
            (dk-lam-type!
              (lambda ()
                (dk-peel!)
                (let* ((io (cadr (dk-goal))) (s (cadr (caddr (caddr (caddr io))))))
                  (ucf-iota! io (dk-apply! h s))))
              (lambda () (dk-set-close! 'uca)))
            (let* ((landed (dk-peel!)) (x (cadr (car landed))))
              (dk-lam-b!)
              (ucf-iota! (cadr (dk-goal)) (dk-apply! h x))))))))
(qed 'uniq-choice-fun)

;;; -----------------------------------------------------------------------
;;; two variables

(sp (make-wff '(FORALL uca (IMPLIES (IN uca SET) (FORALL ucb (IMPLIES (IN ucb SET) (FORALL ucc (FORALL ucq
  (IMPLIES (FORALL ucx (IMPLIES (IN ucx uca) (FORALL ucw (IMPLIES (IN ucw ucb)
             (FORSOME ucy (AND (IN ucy ucc) (AND (IN ucy (ucq ucx ucw))
               (FORALL ucz (IMPLIES (IN ucz ucc) (IMPLIES (IN ucz (ucq ucx ucw)) (= ucz ucy)))))))))))
    (FORSOME ucf_ (AND (IN ucf_ (FUN (CARTESIAN uca ucb) ucc))
      (FORALL ucx (IMPLIES (IN ucx uca) (FORALL ucw (IMPLIES (IN ucw ucb) (IN (ucf_ ucx ucw) (ucq ucx ucw)))))))))))))))))
(dk-peel!)
(let ((h (ucf-hyp)))
  (ew '(VNB-LAMBDA (LIST ucs_ uct_) (CARTESIAN uca ucb) (IOTA uci_ (AND (IN uci_ ucc) (IN uci_ (ucq ucs_ uct_))))))
  (dk-conj-close!
    (lambda ()
      (let ((g (dk-goal)))
        (if (dk-head-is? g 'IN)
            (dk-lam-type!
              (lambda ()
                (dk-peel!)
                (let* ((io (cadr (dk-goal))) (qst (caddr (caddr (caddr io)))))
                  (ucf-iota! io (dk-apply! h (cadr qst) (caddr qst)))))
              (lambda () (dk-set-close! '(CARTESIAN uca ucb))))
            (let* ((g (dk-goal)) (landed (dk-peel!)) (gl (dk-goal)) (qxy (caddr gl)))
              (dk-lam-b!)
              (ucf-iota! (cadr (dk-goal)) (dk-apply! h (cadr qxy) (caddr qxy)))))))))
(qed 'uniq-choice-fun-2)
