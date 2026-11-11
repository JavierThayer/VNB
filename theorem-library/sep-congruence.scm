;;; sep-congruence.scm -- wave of 2026-11-09/10 (agent CNVS2), wired 2026-11-10 from scratchpad/cnvs2-1109/cnvs2-sep.scm.
;;; Library: core.

;;; cnvs2-sep.scm -- SEP CONGRUENCE (agent CNVS2, 2026-11-10).  All PROVEN modulo 0.
;;; Destination: theorem-library/sep-congruence.scm.  Library: core.
;;;
;;; THE THEOREM.  Two separations of one class by two conditions that agree on the class are
;;; the same class:
;;;     sep-congruence-ptwise:     (forall x in A. x in P iff x in Q)
;;;                                  implies {x in A : x in P} == {x in A : x in Q}
;;;     sep-congruence-ptwise-eq:  the same with `=' (no sethood guard is needed: a SEP is a
;;;                                class term, and class-extensionality concludes `=').
;;; In NBG a condition on x is a class, so the conditions are stated as membership in the
;;; class variables P, Q (the convention of finite-set-induction).  The proof is
;;; class-extensionality plus SEP membership both ways.
;;;
;;; THE DEVICE.  An instance at two literal FORMULAS (the case the tree meets: two operator
;;; norms whose SEP conditions differ under the binder, CNVS-REPORT F1) is not obtained by
;;; instantiating P, Q -- a formula is not a class term, and COMP(x, phi) would give
;;; {x in A : x in COMP(x, phi)}, a different term.  It is proved by the same three steps,
;;; packaged as the procedure `cn2-sep-eq!' below (formulas, not classes; a proposed
;;; driver-kit entry `dk-sep-congr!').  The theorem and the procedure are the same
;;; argument; the theorem is the citable statement, the procedure the technique.
;;;
;;; Helper prefix: cn2-.  Binders: cn2e_ (eigenvariable of the extensionality), scx_.
;;; LOAD WINDOW: anywhere after interactive / proof-debt / driver-kit (class-extensionality
;;; is kernel-level, quasi-eq-* are in the base).  No late tactic.  Library: core.

(define (cn2-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'constructions))
      (begin
        (display "\n*** cnvs2-sep: ") (display name) (display " did NOT close.  Open leaves:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "cnvs2-sep: unfinished" name))))

;;; (cn2-sep-eq! S1 S2 IFF!) -- S1 = (SEP x1 A p1), S2 = (SEP x2 A p2), one domain A.  IFF! is
;;; a procedure of the eigenvariable e, run with (IN e A) and the condition of one side in
;;; context, which LANDS (IFF p1[e] p2[e]) in context and returns it.  Lands (= S1 S2) and
;;; returns it.  The two SEPs need not share their binder.
(define (cn2-sep-eq! s1 s2 iff!)
  (if (not (and (dk-head-is? s1 'SEP) (dk-head-is? s2 'SEP) (equal? (caddr s1) (caddr s2))))
      (error "cn2-sep-eq!: not two SEPs over one domain" (expression->string s1) (expression->string s2)))
  (let ((ext (list 'FORALL 'cn2e_ (list 'IFF (list 'IN 'cn2e_ s1) (list 'IN 'cn2e_ s2)))))
    (dk-have! ext
      (lambda ()
        (let ((e (dk-di-var! (lambda (g) (cadr (cadr g))))))
          (define (dir! from to fwd?)
            (sep-me (list 'IN e from))
            (let* ((iff (iff! e))
                   (a   (if fwd? (cadr iff) (caddr iff)))
                   (b   (if fwd? (caddr iff) (cadr iff))))
              (in-sep! (lambda () (ass))
                       (lambda ()
                         (ai iff)
                         (detach! (list 'IMPLIES a b))
                         (ass)))))
          (dk-iff! (lambda (g) (and (dk-head-is? g 'IN) (equal? (caddr g) s2)))
                   (lambda () (dir! s1 s2 #t))
                   (lambda () (dir! s2 s1 #f))))))
    (fact 'class-extensionality s1 s2)
    (list '= s1 s2)))

;;; ==========================================================================================
;;; THE THEOREM
;;; ==========================================================================================
(define cn2-hyp '(FORALL scx_ (IMPLIES (IN scx_ a) (IFF (IN scx_ p) (IN scx_ q)))))
(define cn2-s1 '(SEP scx_ a (IN scx_ p)))
(define cn2-s2 '(SEP scx_ a (IN scx_ q)))

(sp (make-wff (list 'FORALL 'a (list 'FORALL 'p (list 'FORALL 'q
  (list 'IMPLIES cn2-hyp (list '= cn2-s1 cn2-s2)))))))
(dk-peel!)
(let ((h (dk-pick (lambda (f) (dk-head-is? f 'FORALL)) "the pointwise hypothesis")))
  (cn2-sep-eq! cn2-s1 cn2-s2 (lambda (e) (dk-apply! h e))))
(ass)
(cn2-qed! 'sep-congruence-ptwise-eq)

(sp (make-wff (list 'FORALL 'a (list 'FORALL 'p (list 'FORALL 'q
  (list 'IMPLIES cn2-hyp (list '== cn2-s1 cn2-s2)))))))
(dk-peel!)
(dk-cite! 'sep-congruence-ptwise-eq 'a 'p 'q)
(subst (list '= cn2-s1 cn2-s2))
(qrfl)
(cn2-qed! 'sep-congruence-ptwise)
