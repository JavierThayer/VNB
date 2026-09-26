;;; theorem-library/rake-hb-leaves-2.scm -- THREE Hahn-Banach leaves whose LOAD
;;; WINDOW IS EMPTY.  *** DO NOT WIRE THIS FILE INTO load.scm AS IT STANDS. ***
;;;
;;; Each of the three is stated in vocabulary that is DEFINED inside the very
;;; file that first cites it, so no free-standing file can sit between the
;;; definition and the citation:
;;;
;;;   good-sub-submodule   GOOD-SUB / NPE are def-predicate'd at
;;;   good-sub-in-power    theorem-library/noetherian-maximal-proof.scm:218 and
;;;                        :228, asserted at :231 / :245 / :253, and cited at
;;;                        :320 of the same file.
;;;   line-has-v           LINE is def-functoid'd at
;;;                        theorem-library/norm-as-sup-proof.scm:22, asserted at
;;;                        :41, cited at :172 and below of the same file.
;;;
;;; TWO WAYS TO INTEGRATE, integrator's choice:
;;;
;;; (A) SPLICE.  Move the good-sub blocks into noetherian-maximal-proof.scm
;;;     between the GOOD-SUB definition (:229) and the first citation (:320),
;;;     deleting the add-to-pss/warrant!/topic! triples at :231-:236 and
;;;     :253-:257; move the line-has-v block into norm-as-sup-proof.scm between
;;;     the LINE definition (:24) and the first citation, deleting :41-:47.
;;;     The helpers at the head of this file go with the first block spliced
;;;     into each file (they are file-local, `rhb-' prefixed, and collide with
;;;     nothing in either file).
;;;
;;; (B) MOVE THE VOCABULARY, which is what the layout rule wants anyway:
;;;     NPE / GOOD-SUB are definitions, not proofs, and belong in
;;;     structure-library/finite-dimensional.scm beside IS-SUBMODULE and
;;;     SPAN-ADD-ONE; LINE belongs in structure-library/linear-functional.scm
;;;     beside DUAL-NORM-ON.  With that done this file loads free-standing in
;;;     the window [204, 503) -- lo = 204, theorem-library/discrete-space
;;;     (power-mem-intro), the latest citation here; the other floors are
;;;     rake-analysis2 (199, fun-domain-in-set), subset-lemmas (192),
;;;     normed-vector-space (64); hi = 503,
;;;     theorem-library/noetherian-maximal-proof.  RECOMMENDED SLOT: right
;;;     before "theorem-library/hahn-banach-proof".
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
