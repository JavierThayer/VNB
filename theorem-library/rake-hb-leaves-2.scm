;;; theorem-library/rake-hb-leaves-2.scm -- three Hahn-Banach leaves, PROVEN
;;; modulo 0: good-sub-submodule, good-sub-in-power, line-has-v.
;;;
;;; They are stated in the vocabulary NPE / GOOD-SUB / LINE.  Until 2026-09-19
;;; that vocabulary was defined inside the proof files that first cite the
;;; leaves (noetherian-maximal-proof.scm, norm-as-sup-proof.scm), so this file
;;; had no load window.  The three definitions now live in
;;; structure-library/linear-functional.scm (beside DUAL-NORM-ON and
;;; EXTENDS-ON, which NPE mentions), the three supports are retired, and this
;;; file is wired in load.scm right after theorem-library/rake-hb-leaves.
;;;
;;; Load window: lo = theorem-library/discrete-space (power-mem-intro), the
;;; latest citation made here; the other floors are rake-analysis2
;;; (fun-domain-in-set), subset-lemmas, normed-vector-space;
;;; hi = theorem-library/noetherian-maximal-proof, the first citer.
;;;
;;; All three probe `proven modulo 0' on the band (worker-02, 2026-09-19).

;;; --------------------------------------------------------------------
;;; File-local helpers (`rhb-' prefix).

(define (rhb-cite! rhb-thm rhb-terms rhb-thunk)
  (let ((r (apply dk-fact! rhb-thm rhb-terms)))
    (if (and (pair? r) (eq? (car r) 'IMPLIES))
        (begin (have! (cadr r) rhb-thunk)
               (dk-landed-1 (lambda () (detach! r))))
        r)))

;;; GOOD-SUB(m,s,f,t) is FORSOME g. NPE(m,s,f,t,g): skolemize, unfold NPE, and
;;; every one of its five conjuncts is then a context assumption.  Both
;;; good-sub projections below open exactly this way.
(define (rhb-open-good-sub!)
  (let* ((rhb-h  (dk-pick (dk-head? 'GOOD-SUB) "the GOOD-SUB hypothesis"))
         (rhb-ex (dk-landed-1 (lambda () (mac-h 'good-sub rhb-h)))))
    (dk-skolem! rhb-ex)
    (mac-h 'npe (dk-pick (dk-head? 'NPE) "the NPE instance"))
    (dk-split-all!)))

;;; ====================================================================
;;; good-sub-submodule -- noetherian-maximal-proof.scm:231
;;; ====================================================================
(sp (make-wff
     '(FORALL m (FORALL s (FORALL f (FORALL t
        (IMPLIES (GOOD-SUB m s f t) (IS-SUBMODULE m t))))))))
(dk-peel!)
(rhb-open-good-sub!)
(ass)
(qed 'good-sub-submodule)
(topic! 'good-sub-submodule 'analysis)

;;; ====================================================================
;;; good-sub-in-power -- noetherian-maximal-proof.scm:253
;;;
;;; t is a SET because it is the DOMAIN of the extension g (fun-domain-in-set),
;;; and t subset VEC(m) is the first NPE conjunct; power-mem-intro closes it.
;;;
;;; THE LUTINS STEP.  This statement carries no structure hypothesis on m, so
;;; (VEC m) is not certified DEFINED and every forall-elim at it owes
;;; `vec(m) = vec(m)' -- an owed leaf with the parent's context, unclosable
;;; here, which silently leaves the proof ungrounded.  The cure is ONE
;;; instantiation whose result is a true IN mentioning (VEC m): the subset
;;; hypothesis, unfolded to its pointwise form and applied at (VZERO m) (whose
;;; own typing is the second NPE conjunct), lands (IN (VZERO m) (VEC m)) and
;;; certifies (VEC m) for everything after it.
;;; ====================================================================
(sp (make-wff
     '(FORALL m (FORALL s (FORALL f (FORALL t
        (IMPLIES (GOOD-SUB m s f t) (IN t (POWER (VEC m))))))))))
(dk-peel!)
(let* ((rhb-g    (dk-goal))
       (rhb-tt   (cadr rhb-g))
       (rhb-vecm (cadr (caddr rhb-g))))
  (rhb-open-good-sub!)
  (mac-h 'is-linear-functional-on
         (dk-pick (dk-head? 'IS-LINEAR-FUNCTIONAL-ON) "the extension's LF-ON"))
  (dk-split-all!)
  (let ((rhb-fun (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'IN)
                                            (pair? (caddr fm))
                                            (eq? (car (caddr fm)) 'FUN)
                                            (equal? (cadr (caddr fm)) rhb-tt)))
                          "the FUN(t,RR) typing")))
    (dk-fact! 'fun-domain-in-set rhb-tt (caddr (caddr rhb-fun)) (cadr rhb-fun)))
  (let ((rhb-mm (cadr (dk-pick (dk-head? 'IS-SUBMODULE) "IS-SUBMODULE m t"))))
    (dk-fact! 'submodule-subset  rhb-mm rhb-tt)
    (dk-fact! 'submodule-vzero-in rhb-mm rhb-tt)
    (let* ((rhb-sub (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'SUBSET)
                                               (equal? (cadr fm) rhb-tt)))
                             "t subset vec(m)"))
           (rhb-ptw (dk-landed-1 (lambda () (mac-h 'subset-def rhb-sub)))))
      (dk-apply! rhb-ptw (list 'VZERO rhb-mm))
      (rhb-cite! 'power-mem-intro (list rhb-vecm rhb-tt)
                 (lambda ()
                   (dk-apply! rhb-ptw (dk-di-var!))
                   (ass)))
      (ass))))
(qed 'good-sub-in-power)
(topic! 'good-sub-in-power 'analysis)

;;; ====================================================================
;;; line-has-v -- norm-as-sup-proof.scm:41
;;; v = 1.v.  The witness supplied to `ew' is ONE(SCAL m), not the literal 1:
;;; the unital law nvs-act-unital is stated at one(scal(m)), and `subst'
;;; rewrites LEFT TO RIGHT only, so nvs-scal-one (one(scal(m)) == 1) can carry
;;; the TYPING goal down to (IN 1 RR) but cannot carry a literal 1 back up.
;;; ====================================================================
(sp (make-wff
     '(FORALL m (FORALL v
        (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IMPLIES (IN v (VEC m))
           (IN v (LINE m v))))))))
(dk-peel!)
(let* ((rhb-g   (dk-goal))
       (rhb-v   (cadr rhb-g))
       (rhb-m   (cadr (caddr rhb-g)))
       (rhb-one (list 'ONE (list 'SCAL rhb-m))))
  (dk-fact! 'nvs-scal-one rhb-m)
  (dk-fact! 'nvs-act-unital rhb-m rhb-v)
  (mac 'LINE)
  (for-each
   (lambda (rhb-leaf)
     (dk-focus! rhb-leaf)
     (if (eq? (car (dk-goal)) 'FORSOME)
         (begin
           (ew rhb-one)
           (dk-conj-close!
            (lambda ()
              (let ((h (dk-goal)))
                (if (eq? (car h) 'IN)
                    (begin (subst (dk-pick (dk-head? '==) "one(scal(m)) == 1")) (arith))
                    (begin (dk-fact! 'eq-sym (caddr h) (cadr h)) (ass)))))))
         (ass)))
   (dk-opened (lambda () (sep-mi)))))
(qed 'line-has-v)
(topic! 'line-has-v 'analysis)
