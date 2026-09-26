;;; calculus/euclidean-ring-pid.scm
;;; ===================================================================
;;; STRESS TEST:  every Euclidean ring is a principal-ideal domain.
;;;
;;;   IS-EUCLIDEAN-RING(s)  =>  IS-PID(s)
;;;
;;; The point of the exercise was to find what machinery the classical
;;; proof needs.  The verdict, baked into structure-library/ideal.scm:
;;; once three lemmas are in hand the theorem is PURE SET-EXTENSIONALITY
;;; GLUE, and ALL the mathematics concentrates into ONE of them.
;;;
;;;   euclidean-ideal-has-generator  -- the whole proof: well-ordering of
;;;       the degree set (nn-least-element) + Euclidean division.  Every
;;;       ideal I has a b in I with I subset (b).
;;;   principal-ideal-in-ideal       -- trivial: b in I  =>  (b) subset I
;;;       (absorption).  The reverse inclusion.
;;;   ideal-elt-in-carrier           -- trivial: x in I  =>  x in A(s).
;;;
;;; This file proves the ASSEMBLY: from the generator b, witness a := b for
;;; "I is principal", and close I = (b) by class-extensionality, the two
;;; inclusions supplied by the generator (forward) and principal-ideal-in-
;;; ideal (backward).
;;;
;;; Run standalone (skips the heavy at-load proofs):
;;;   ./prover calculus/euclidean-ring-pid.scm
;;; ===================================================================

;;; ---- forward-reasoning helpers (mirrors prop-3-15-proof.scm) ----
(define (proof-leaves)
  (filter (lambda (sqn) (and (not (sequent-node-grounded? sqn))
                             (null? (sequent-node-in-arrows sqn))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (sub? substr s) (and (string-search-forward substr s 0) #t))
(define (any-pred pred lst)
  (let loop ((l lst)) (cond ((null? l) #f) ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (cur-sqn) (proof-state-focus *ps*))
(define (cur-goal-raw) (wff-formula (sequent-node-assertion (cur-sqn))))
(define (asm-set) (map wff-formula (sequent-node-assumptions (cur-sqn))))
(define (asm-find-pred pred)
  (let ((w (any-pred (lambda (w) (pred (wff-formula w)))
                     (sequent-node-assumptions (cur-sqn)))))
    (and w (wff-formula w))))
(define (asm-find-sub substr)
  (asm-find-pred (lambda (f) (sub? substr (expression->string (make-wff f))))))
(define (focus-leaf! substr)
  (let ((s (any-pred (lambda (s) (sub? substr (expression->string (sequent-node-assertion s))))
                     (proof-leaves))))
    (if s (begin (dk-focus! s) s)
        (error "focus-leaf!: no frontier leaf matching" substr))))
(define (focus-leaf-goal! raw)
  (let ((s (any-pred (lambda (s) (equal? (wff-formula (sequent-node-assertion s)) raw))
                     (proof-leaves))))
    (if s (begin (dk-focus! s) s)
        (error "focus-leaf-goal!: none equal to" (expression->string (make-wff raw))))))
(define (split-ands!)
  (let loop ()
    (let scan ((as (sequent-node-assumptions (cur-sqn))))
      (cond ((null? as) 'done)
            ((let ((f (wff-formula (car as)))) (and (pair? f) (eq? (car f) 'AND)))
             (ai (wff-formula (car as))) (loop))
            (else (scan (cdr as)))))))
(define (ai-body forsome-raw)            ; eliminate FORSOME hyp, return body added
  (let ((before (asm-set)))
    (ai forsome-raw)
    (any-pred (lambda (f) (not (member f before))) (asm-set))))
(define (find-forall-asm pred)           ; the FORALL assumption whose body satisfies pred
  (asm-find-pred (lambda (w) (and (pair? w) (eq? (car w) 'FORALL) (pred w)))))

;;; ===================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-EUCLIDEAN-RING s) (IS-PID s)))))
(di)                                     ; peel FORALL s ; goal (IMPLIES (IS-EUCLIDEAN-RING S) (IS-PID S))
(di)                                     ; peel IMPLIES ; asm IS-EUCLIDEAN-RING S ; goal (IS-PID S)
(define S (cadr (cur-goal-raw)))         ; (IS-PID S) -> S
(mac 'is-pid-def)                            ; goal AND(IS-INTEGRAL-DOMAIN S, FORALL I ...)
(di)                                     ; leaf1 / leaf2

;;; ---- leaf1: IS-INTEGRAL-DOMAIN S  (subtype law, forward) ----
(focus-leaf! "is-integral-domain")
(fact 'euclidean-ring-is-integral-domain S)
(ass)

;;; ---- leaf2: every ideal is principal ----
(focus-leaf! "forall(")                  ; FORALL I (IMPLIES (IS-IDEAL S I) (FORSOME a ...))
(di)                                     ; intro eigenvar I
(define II (caddr (cadr (cur-goal-raw)))); goal (IMPLIES (IS-IDEAL S II) _)
(di)                                     ; asm IS-IDEAL S II ; goal FORSOME a (AND (IN a (A S)) (= II (PRINCIPAL-IDEAL S a)))

;;; pull the generator b: I subset (b), with b in I
(fact 'euclidean-ideal-has-generator S II)
(define GENEX (asm-find-pred (lambda (w) (and (pair? w) (eq? (car w) 'FORSOME)))))
(define BODY  (ai-body GENEX))           ; (AND (IN B II) (FORALL a (IMPLIES (IN a II) (IN a (PRINCIPAL-IDEAL S B)))))
(define B     (cadr (cadr BODY)))        ; the generator eigenvar
(define HGEN  (caddr BODY))              ; (FORALL a (IMPLIES (IN a II) (IN a (PRINCIPAL-IDEAL S B))))
(split-ands!)                            ; H_bI: (IN B II) ; H_gen: HGEN

;;; witness a := b ; split the conjunction
(ew B)                                   ; goal AND( IN B (A S), = II (PRINCIPAL-IDEAL S B) )
(di)

;;; leaf2a: B in A(S)
(focus-leaf-goal! `(IN ,B (A ,S)))
(fact 'ideal-elt-in-carrier S II B)
(ass)

;;; leaf2b: II = (B)  by class-extensionality
(focus-leaf-goal! `(= ,II (PRINCIPAL-IDEAL ,S ,B)))
(bc* 'class-extensionality)              ; goal FORALL x (IFF (IN x II) (IN x (PRINCIPAL-IDEAL S B)))
(di)                                     ; intro eigenvar x
(define X (cadr (cadr (cur-goal-raw))))  ; (IFF (IN X II) _)
(di)                                     ; iff-intro: fwd (asm IN X II) ; bwd (asm IN X (PI S B))

;;; forward  x in I => x in (b):  the generator's universal at x
(focus-leaf-goal! `(IN ,X (PRINCIPAL-IDEAL ,S ,B)))
(inst HGEN X)
(detach! `(IMPLIES (IN ,X ,II) (IN ,X (PRINCIPAL-IDEAL ,S ,B))))
(ass)

;;; backward  x in (b) => x in I:  principal-ideal-in-ideal
(focus-leaf-goal! `(IN ,X ,II))
(fact 'principal-ideal-in-ideal S II B)
(define PII (find-forall-asm
             (lambda (w) (sub? "principal-ideal"
                               (expression->string (make-wff (cadr (caddr w))))))))
(inst PII X)
(detach! `(IMPLIES (IN ,X (PRINCIPAL-IDEAL ,S ,B)) (IN ,X ,II)))
(ass)

;;; ===================================================================
(if (proof-done? *ps*)
    (qed 'euclidean-ring-is-pid)
    (begin (display ";; NOT DONE -- open leaves:\n")
           (for-each (lambda (s) (display "  ") (display (expression->string (sequent-node-assertion s))) (newline))
                     (proof-leaves))))
