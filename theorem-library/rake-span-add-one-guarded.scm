;;; rake-span-add-one-guarded.scm -- the GUARDED forms of span-add-one-superset
;;; and span-add-one-has-v, PROVEN.
;;;
;;; The supports as stated are FALSE.
;;;   span-add-one-superset  theorem-library/hahn-banach-full-proof.scm:63-69
;;;   span-add-one-has-v     theorem-library/hahn-banach-full-proof.scm:71-77
;;; Both are guarded only by IS-SUBMODULE(m,t) and IN v (VEC m).  IS-SUBMODULE
;;; constrains a SUBSET of VEC(m) and its closure; it says NOTHING about the
;;; module laws of m.  The proofs need y = y (+) 0.v and v = 0 (+) 1.v, neither
;;; of which follows.  One model refutes both (scratchpad/rhb/HB-TRIAGE.md):
;;;
;;;     VEC(m) = {0,1}   VZERO(m) = 0   VNEG(m) = the identity on VEC(m)
;;;     VADD(m) = the constant 0 on CARTESIAN(VEC(m),VEC(m))
;;;     ACT(m)  = the constant 0 on CARTESIAN(CARR(SCAL m),VEC(m))
;;;     t = {0,1}        v = 1
;;;
;;; IS-SUBMODULE(m,t) holds and v in VEC(m), but SPAN-ADD-ONE(m,t,v) = {0}, so
;;; t is not a subset of it and v is not in it.
;;;
;;; The repair is one antecedent each: (IS-NORMED-VECTOR-SPACE m) FIRST and
;;; CURRIED, exactly as span-add-one-submodule (:79) already carries it.  Both
;;; citers -- hahn-banach-full-proof.scm:176, :261, :264 -- have
;;; IS-NORMED-VECTOR-SPACE(m) in context at the citation, so the guard costs
;;; them nothing.  CHANGING A STATEMENT IS THE USER'S CALL, so the guarded
;;; facts are proved here under NEW names and NOTHING that cites the old ones
;;; is touched:
;;;
;;;   span-add-one-superset-nvs   is-nvs(m) => is-submodule(m,t) => v in vec(m)
;;;                               => t subset SPAN-ADD-ONE(m,t,v)
;;;   span-add-one-has-v-nvs      ... => v in SPAN-ADD-ONE(m,t,v)
;;;
;;; The proofs are the obvious ones: y = y (+) 0.v is `nvs-act-zero' and
;;; v = VZERO(m) (+) 1.v is `nvs-act-one' followed by the left identity.
;;;
;;; LOAD WINDOW [<rake-hb-submodules> + 1, 508).
;;;   lo: the latest citation is `nvs-vzero-left', proven in
;;;       theorem-library/rake-hb-submodules (this batch) -- so this file loads
;;;       immediately AFTER it.  The other citations are far earlier:
;;;       nvs-act-laws (506: nvs-act-zero, nvs-act-one), subset-lemmas (191:
;;;       subset-mem-fwd), finite-dimensional (55: submodule-subset,
;;;       submodule-vzero-in, SPAN-ADD-ONE), views (60).
;;;   hi = 508: theorem-library/hahn-banach-full-proof would be the citer, if
;;;       and when the user decides that the guarded forms REPLACE the false
;;;       ones.  As the tree stands nothing cites these two names, so the
;;;       window's upper end is not forced.
;;;   No late tactic is used.
;;;
;;; Helper prefix `r8bg-'.

;;; --------------------------------------------------------------------
;;; File-local helpers.

;; Close (IN w (SPAN-ADD-ONE m t v)): unfold the functoid in the GOAL, then
;; sep-mi's two leaves -- the VEC(m) typing and the decomposition existential,
;; whose witnesses are the t-component and the scalar, in that order.  Every
;; atom that finally appears is handed to CLOSE!.
(define (r8bg-exists! r8bg-witnesses r8bg-close!)
  (if (null? r8bg-witnesses)
      (dk-conj-close! r8bg-close!)
      (begin
        (ew (car r8bg-witnesses))
        (dk-conj-close!
         (lambda ()
           (if (eq? (car (dk-goal)) 'FORSOME)
               (r8bg-exists! (cdr r8bg-witnesses) r8bg-close!)
               (r8bg-close!)))))))

(define (r8bg-mem-in! r8bg-witnesses r8bg-type! r8bg-close!)
  (mac 'SPAN-ADD-ONE)
  (for-each
   (lambda (r8bg-leaf)
     (dk-focus! r8bg-leaf)
     (if (eq? (car (dk-goal)) 'FORSOME)
         (r8bg-exists! r8bg-witnesses r8bg-close!)
         (r8bg-type!)))
   (dk-opened (lambda () (sep-mi)))))

;; the decomposition equation gets EQ!; every typing is already in the context
(define (r8bg-closer r8bg-eq!)
  (lambda () (if (eq? (car (dk-goal)) '=) (r8bg-eq!) (ass))))

(define (r8bg-check! r8bg-name)
  (if (not (proof-done? *ps*))
      (error "rake-span-add-one-guarded: proof did not close" r8bg-name
             (expression->string (dk-goal))))
  (qed r8bg-name)
  (topic! r8bg-name 'analysis))

;;; ====================================================================
;;; span-add-one-superset-nvs -- y in t is y (+) 0.v.
;;; ====================================================================
(sp (make-wff
     '(FORALL m (FORALL t (FORALL v
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
         (IMPLIES (IS-SUBMODULE m t)
          (IMPLIES (IN v (VEC m))
            (SUBSET t (SPAN-ADD-ONE m t v))))))))))
(dk-peel!)
(let* ((r8bg-g   (dk-goal))                       ; (SUBSET t (SPAN-ADD-ONE m t v))
       (r8bg-tt  (cadr r8bg-g))
       (r8bg-set (caddr r8bg-g))
       (r8bg-m   (cadr r8bg-set))
       (r8bg-v   (cadddr r8bg-set))
       (r8bg-vec (list 'VEC r8bg-m)))
  (mac 'subset-def)
  (let ((r8bg-y (cadr (car (dk-peel!)))))         ; the eigenvariable of (IN y t)
    (dk-fact! 'submodule-subset r8bg-m r8bg-tt)
    (dk-fact! 'subset-mem-fwd r8bg-tt r8bg-vec r8bg-y)
    (fact 'rr-zero-in)
    (r8bg-mem-in! (list r8bg-y 0) (lambda () (ass))
      (r8bg-closer
       (lambda ()
         (subst (dk-fact! 'nvs-act-zero r8bg-m r8bg-v r8bg-y))
         (rfl))))))
(r8bg-check! 'span-add-one-superset-nvs)

;;; ====================================================================
;;; span-add-one-has-v-nvs -- v is VZERO(m) (+) 1.v.
;;; ====================================================================
(sp (make-wff
     '(FORALL m (FORALL t (FORALL v
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
         (IMPLIES (IS-SUBMODULE m t)
          (IMPLIES (IN v (VEC m))
            (IN v (SPAN-ADD-ONE m t v))))))))))
(dk-peel!)
(let* ((r8bg-g    (dk-goal))                      ; (IN v (SPAN-ADD-ONE m t v))
       (r8bg-v    (cadr r8bg-g))
       (r8bg-set  (caddr r8bg-g))
       (r8bg-m    (cadr r8bg-set))
       (r8bg-tt   (caddr r8bg-set))
       (r8bg-zero (list 'VZERO r8bg-m)))
  (fact 'module-vzero-in-normed-vector-space-as-module r8bg-m)
  (fact 'submodule-vzero-in r8bg-m r8bg-tt)
  (fact 'rr-one-in)
  (r8bg-mem-in! (list r8bg-zero 1) (lambda () (ass))
    (r8bg-closer
     (lambda ()
       (subst (dk-fact! 'nvs-act-one r8bg-m r8bg-v r8bg-zero))
       (subst (dk-fact! 'nvs-vzero-left r8bg-m r8bg-v))
       (rfl)))))
(r8bg-check! 'span-add-one-has-v-nvs)
