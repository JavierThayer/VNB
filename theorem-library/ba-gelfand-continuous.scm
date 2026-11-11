;;; ba-gelfand-continuous.scm -- wave of 2026-11-09/10 (agent BA-1D), wired 2026-11-10 from scratchpad/ba1d-1109/ba-gelfand-continuous.scm.
;;; Library: operator-algebras.

;;; ba-gelfand-continuous.scm -- THE GELFAND TRANSFORM OF x IS CONTINUOUS ON THE GELFAND SPACE (the continuity half
;;; of BanachAlgebras.pdf Proposition 1.15): the characters lie in the product of copies of CC, and G(x) is the
;;; evaluation at x restricted to them (cc-product-eval-continuous).
;;; Agent BA-1D, wave 2026-11-09.  Destination: theorem-library/ba-gelfand-continuous.scm.
;;; Library: operator-algebras.  All proofs modulo 0.  Helper prefix: bgk-.
;;; LOAD WINDOW: after cc-product.scm (this wave) and BA-1's ba-spectrum.scm (bas-characters-unfold).

(define (bgk-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** ba-gelfand-continuous: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (h) (display "      asm: ") (display (expression->string h)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "ba-gelfand-continuous: unfinished" name))))
(define (bgk-st body) (make-wff (list 'FORALL 'a (list 'IMPLIES '(IS-UNITAL-BANACH-ALGEBRA a) body))))
(define bgk-CF '(VNB-LAMBDA bgx_ (VEC a) (METRIC-TOP CC-MS)))
(define bgk-PRP (list 'TPROD-PTS '(VEC a) bgk-CF))
(define bgk-CH '(CHARACTERS a))

;;; a character is a function A -> CC
(define bgk-CHSEP '(SEP bac_ (FUN (VEC a) CC) (AND (IS-CC-LINEAR-ON a bac_) (AND (FORALL bax_ (IMPLIES (IN bax_ (VEC a))
  (FORALL bay_ (IMPLIES (IN bay_ (VEC a)) (= (bac_ ((VMUL a) bax_ bay_)) (* (bac_ bax_) (bac_ bay_))))))) (= (bac_ (VONE a)) 1)))))
(sp (bgk-st '(FORALL c (IMPLIES (IN c (CHARACTERS a)) (IN c (FUN (VEC a) CC))))))
(dk-peel!)
(fact 'bas-characters-unfold 'a)
(let ((m (dk-rewrite-h! '(IN c (CHARACTERS a)) '(CHARACTERS a) bgk-CHSEP)))
  (dk-project! '(IN c (FUN (VEC a) CC)) (lambda () (sep-me m)))
  (dk-ass!))
(bgk-qed! 'character-in-fun)

;;; Proposition 1.15, continuity half: G(x) is a continuous function on the Gelfand space
(sp (bgk-st '(FORALL x (IMPLIES (IN x (VEC a))
  (IS-HOM-TOP-SPACE (GELFAND-SPACE a) (METRIC-TOP CC-MS) ((GELFAND-TRANSFORM a) x))))))
(dk-peel!)
(dk-cite! 'bal-uba-vec-set 'a)
(dk-have! (list 'SUBSET bgk-CH bgk-PRP)
  (lambda ()
    (let ((c (subset-by-element!)))
      (dk-cite! 'character-in-fun 'a c)
      (dk-cite! 'fun-in-cc-product '(VEC a) c)
      (dk-ass!))))
(dk-cite! 'cc-product-eval-continuous '(VEC a) bgk-CH 'x)
(mac 'GELFAND-SPACE)
(mac 'GELFAND-TRANSFORM)
(if (not (dk-lam-b!)) (dk-ass!))
(bgk-qed! 'gelfand-transform-continuous)
