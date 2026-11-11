;;; kal-cstar-122.scm -- wave of 2026-11-09/10 (agent KIT-ALG), wired 2026-11-10 from scratchpad/kitalg-1109/kal-cstar-122.scm.
;;; Library: operator-algebras.

;;; kal-cstar-122.scm -- BANACH ALGEBRAS, Proposition 1.22: a character of a C*-algebra preserves the
;;; involution, chi(x*) = conj(chi(x)).  F. J. Thayer, "Banach Algebras and Applications", ch. 1.
;;; Agent KIT-ALG, 2026-11-10.  Destination: theorem-library/kal-cstar-122.scm.
;;; Library: operator-algebras.  All proofs modulo 0.  Helper prefix kcs-.
;;;
;;; THE ROUTE (a deviation in the PROOF only).  The notes bound |chi(h + i lambda 1)|^2 by
;;; ||h||^2 + lambda^2; here chi(h) lies in sigma(h) (character-value-in-spectrum, BA-1B), and
;;; sigma(h) is real for h self-adjoint (bcp-sa-spectrum-real, BA-2, whose proof IS the notes' bound
;;; for an element of the spectrum).  So chi is real on self-adjoint elements (kcs-character-sa-real).
;;; Then h1 = x + x* and h2 = i(x + (-1)x*) are self-adjoint (dk-alg-norm!), chi(h1) = u + v and
;;; chi(h2) = i(u + (-1)v) with u = chi(x), v = chi(x*), and u = (p - iq)/2, v = (p + iq)/2 for the
;;; reals p, q: v = conj(u) by dk-cc-norm!.  The notes state 1.22 for a COMMUTATIVE C*-algebra;
;;; commutativity is not used, so the general form (unital C*-algebra) is proved first and the
;;; notes' form is one citation (bcs-ccsa-ucsa).
;;;
;;; LOAD WINDOW: after BA-1B's ba-gelfand (character-value-in-spectrum), BA-1H's ba-cstar-laws
;;; (bcs-uiba-is-uba, bcs-characters-view, bcs-uu-vec, bcs-ccsa-ucsa), BA-2's ba2-cstar
;;; (bcp-ucsa-uiba, bcp-sa-noninvertible-real, bcp-shift-view, bcp-invertible-view,
;;; bcp-u-bas-shift-type) and kal-laws (the kal-uiba law set of the normaliser).

(define (kcs-qed! name)
  (if (not (proof-done? *ps*))
      (for-each (lambda (l)
                  (if (and (not (sequent-node-grounded? l))
                           (let ((g (dk-goal-of l))) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g)))))
                      (begin (dk-focus! l) (rfl))))
                (dk-open-leaves)))
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** kal-cstar-122: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "kal-cstar-122: unfinished" name))))
(define (kcs-ucsa body) (make-wff (list 'FORALL 'a (list 'IMPLIES '(IS-UNITAL-C-STAR-ALGEBRA a) body))))
(define kcs-V '(UIBA-AS-UBA a))
(define (kcs-ad x y) (list '(VADD a) x y))
(define (kcs-ac c x) (list '(ACT a) c x))
(define (kcs-st x) (list '(VSTAR a) x))

;;; open (IN c (CHARACTERS a)): (IN c (FUN (VEC a) CC)), additivity, homogeneity (the model is
;;; bgt-char-open! of ba-gelfand); returns (additivity homogeneity)
(define (kcs-char-open! c)
  (let* ((m0 (list 'IN c '(CHARACTERS a)))
         (body (caddr (dk-cite! 'bas-characters-unfold 'a)))
         (m1 (dk-rewrite-h! m0 '(CHARACTERS a) body)))
    (dk-project! (list 'IN c '(FUN (VEC a) CC)) (lambda () (sep-me m1)))
    (dk-project! (list 'IS-CC-LINEAR-ON 'a c) (lambda () (sep-me m1)))
    (let* ((ld (caddr (dk-cite! 'IS-CC-LINEAR-ON 'a c)))
           (la (dk-project! (cadr (caddr ld)) 'IS-CC-LINEAR-ON (list 'IS-CC-LINEAR-ON 'a c)))
           (lm (dk-project! (caddr (caddr ld)) 'IS-CC-LINEAR-ON (list 'IS-CC-LINEAR-ON 'a c))))
      (list la lm))))
(define (kcs-cval! c t)                     ; (IN (c t) CC), t typed in (VEC a)
  (dk-cite! 'fun-apply-type-c c '(VEC a) 'CC t))

;;; ---- (1) a character is real on a self-adjoint element ------------------------------------------
(sp (kcs-ucsa '(FORALL c (IMPLIES (IN c (CHARACTERS a)) (FORALL h (IMPLIES (IS-SELF-ADJOINT-EL a h)
  (IN (c h) RR)))))))
(dk-peel!)
(dk-cite! 'bcp-ucsa-uiba 'a)
(dk-project! '(IN h (VEC a)) 'is-self-adjoint-el '(IS-SELF-ADJOINT-EL a h))
(dk-cite! 'bcs-uiba-is-uba 'a)
(dk-cite! 'bcs-characters-view 'a)
(dk-cite! 'bcs-uu-vec 'a)
(let* ((cv (dk-rewrite-h! '(IN c (CHARACTERS a)) '(CHARACTERS a) (list 'CHARACTERS kcs-V)))
       (hv (dk-rewrite-h! '(IN h (VEC a)) '(VEC a) (list 'VEC kcs-V)))
       (sv (dk-cite! 'character-value-in-spectrum kcs-V 'h 'c))
       (un (dk-cite! 'bas-spectrum-unfold kcs-V 'h))
       (m1 (dk-rewrite-h! sv (cadr un) (caddr un)))
       (ch '(c h))
       (shV (list 'SHIFT-EL kcs-V ch 'h))
       (sha (list 'SHIFT-EL 'a ch 'h)))
  (dk-project! (list 'IN ch 'CC) (lambda () (sep-me m1)))
  (let* ((niV (dk-project! (list 'NOT (list 'IS-INVERTIBLE-EL kcs-V shV)) (lambda () (sep-me m1))))
         (ignore (dk-cite! 'bcp-shift-view 'a ch 'h))
         (ni1 (dk-rewrite-h! niV shV sha))
         (ignore2 (dk-cite! 'bcp-u-bas-shift-type 'a ch 'h))
         (iff (dk-cite! 'bcp-invertible-view 'a sha))
         (ni (list 'NOT (list 'IS-INVERTIBLE-EL 'a sha))))
    (dk-have! ni (lambda () (dk-only! iff ni1) (prop)))
    (dk-cite! 'bcp-sa-noninvertible-real 'a 'h ch)
    (dk-ass!)))
(kcs-qed! 'kcs-character-sa-real)

;;; ---- (2) Proposition 1.22, for a unital C*-algebra ---------------------------------------------
(sp (kcs-ucsa '(FORALL c (IMPLIES (IN c (CHARACTERS a)) (FORALL x (IMPLIES (IN x (VEC a))
  (= (c ((VSTAR a) x)) (CONJUGATE (c x)))))))))
(dk-peel!)
(dk-cite! 'bcp-ucsa-uiba 'a)
(let* ((laws (kcs-char-open! 'c)) (la (car laws)) (lm (cadr laws))
       (sx (kcs-st 'x))
       (nsx (kcs-ac -1 sx))
       (d (kcs-ad 'x nsx))
       (h1 (kcs-ad 'x sx))
       (h2 (kcs-ac +i d))
       (u '(c x)) (v (list 'c sx)))
  (for-each (lambda (t) (dk-alg-type! 'kal-uiba 'a t)) (list sx nsx d h1 h2))
  (for-each (lambda (t) (kcs-cval! 'c t)) (list 'x sx nsx d h1 h2))
  ;; h1 and h2 are self-adjoint: the normaliser
  (for-each (lambda (h)
              (dk-have! (list 'IS-SELF-ADJOINT-EL 'a h)
                (lambda ()
                  (mac 'is-self-adjoint-el)
                  (dk-each-leaf! di
                    (lambda ()
                      (if (eq? (car (dk-goal)) 'IN) (dk-ass!) (dk-alg-norm! 'kal-uiba 'a)))))))
            (list h1 h2))
  (let* ((r1 (dk-cite! 'kcs-character-sa-real 'a 'c h1))
         (r2 (dk-cite! 'kcs-character-sa-real 'a 'c h2))
         ;; linearity: c(h1) = u + v, c(h2) = i (u + (-1) v)
         (e1 (dk-apply! la 'x sx))
         (ignore (dk-cc-type! -1))
         (e2 (dk-apply! lm +i d))
         (e3 (dk-apply! la 'x nsx))
         (e4 (dk-apply! lm -1 sx))
         (p (list '+ u v))
         (q (list '* +i (list '+ u (list '* -1 v))))
         (r1b (dk-rewrite-h! r1 (cadr e1) (caddr e1)))
         (r2b (dk-rewrite-h! (dk-rewrite-h! (dk-rewrite-h! r2 (cadr e2) (caddr e2)) (cadr e3) (caddr e3))
                             (cadr e4) (caddr e4))))
    (if (not (and (equal? r1b (list 'IN p 'RR)) (equal? r2b (list 'IN q 'RR))))
        (error "kal-cstar-122: the linearity rewrites did not give the expected reals"
               (expression->string r1b) (expression->string r2b)))
    (let* ((pn (dk-name! p)) (qn (dk-name! q))
           (us (list '* 1/2 (list '+ pn (list '* -1 (list '* +i qn)))))
           (vs (list '* 1/2 (list '+ pn (list '* +i qn)))))
      (dk-cc-type! u) (dk-cc-type! v)
      (for-each (lambda (cl)
                  (dk-have! cl
                    (lambda ()
                      (subst (list '= pn p)) (subst (list '= qn q))
                      (dk-cc-norm!))))
                (list (list '= u us) (list '= v vs)))
      (subst (list '= u us))
      (subst (list '= v vs))
      (dk-cc-norm!))))
(kcs-qed! 'character-preserves-involution)

;;; ---- (3) Proposition 1.22 as the notes state it: A a commutative C*-algebra ------------------------
(sp (make-wff '(FORALL a (IMPLIES (IS-COMMUTATIVE-C-STAR-ALGEBRA a) (FORALL c (IMPLIES (IN c (CHARACTERS a))
  (FORALL x (IMPLIES (IN x (VEC a)) (= (c ((VSTAR a) x)) (CONJUGATE (c x)))))))))))
(dk-peel!)
(dk-cite! 'bcs-ccsa-ucsa 'a)
(dk-cite! 'character-preserves-involution 'a 'c 'x)
(dk-ass!)
(kcs-qed! 'ccsa-character-preserves-involution)
(display "\n;; KCS qed failures: ")  
