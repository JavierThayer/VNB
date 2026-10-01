;;; cc-int-laws.scm -- the read-offs of CC-INT, TRACE and LINE-INT
;;; (structure-library/path-integral.scm), sections 3.3 and 3.4 of
;;; docs/paths-and-line-integrals-2026-09-21.md.
;;;
;;; WHAT IS HERE AND WHAT IT COSTS.  CC-INT, TRACE and LINE-INT are FUNCTOIDS,
;;; so each installs only a rewrite MACETE; `mac' unfolds one in a GOAL but
;;; `mac-h' CANNOT unfold one in an ASSUMPTION by the functoid's own name (it
;;; warns `unknown theorem/macete' and the driver continues with the hypothesis
;;; untouched -- CLAUDE.md, "Where a definition lives").  The cure is to PROVE
;;; the unfold equation, which is what the first three theorems are.  Each is
;;; one `mac' and one `qrfl'; they are cheap and they are not optional.
;;;
;;; THE EQUATIONS ARE `==', NOT `='.  CC-INT's right-hand side contains two
;;; IOTA terms and an IOTA is never certified defined (CLAUDE.md, the LUTINS
;;; rule), so a strict `=' would assert the definedness of the integral -- the
;;; very thing that has to be earned from a piecewise antiderivative.  `==' is
;;; unconditional and says exactly what the definition says: the two sides
;;; denote the same thing when either denotes.
;;;
;;; Helper prefix: ci2-.
;;;
;;; Dependencies: structure-library/path-integral.scm;
;;; theorem-library/pw-antiderivative-laws.scm; ccint-basics.scm;
;;; structure-library/injection.scm (image-membership-iff, image-set);
;;; metric-subspace-laws.scm; number-systems (cc-mul-closed);
;;; fun-apply-type-proof (fun-apply-type-c); subset-lemmas (subset-mem-fwd).

;;; ---- file-local driver helpers ---------------------------------------

(define (ci2-head g) (and (pair? g) (car g)))

(define ci2-cc '(CCINT a b))

;;; =====================================================================
;;; (1) EQUATION (44).  The integral of a CC-valued function of a real
;;; variable is the integral of its real part plus i times the integral of its
;;; imaginary part -- the user's notes, complex-analysis.pdf 3.1, (44).
;;; =====================================================================
(sp (make-wff '(FORALL pphi_ (FORALL a (FORALL b
   (== (CC-INT pphi_ a b)
       (+ (PW-INT (VNB-LAMBDA pat_ (CCINT a b) (real-part (pphi_ pat_))) a b)
          (* (PW-INT (VNB-LAMBDA pat_ (CCINT a b) (imag-part (pphi_ pat_))) a b)
             +i))))))))
(di)
(mac 'CC-INT)
(qrfl)
(qed 'cc-int-unfold)
(topic! 'cc-int-unfold 'analysis)
(alias! 'cc-int-unfold
        "equation (44)"
        "the integral of a complex-valued function is taken componentwise")

;;; =====================================================================
;;; (2) THE INTEGRAL ALONG A ROAD.  Dieudonne 9.6: the integral of f along
;;; (gamma, dgamma) is the integral over [a,b] of f(gamma(t)) gamma'(t).
;;; =====================================================================
(sp (make-wff '(FORALL pf (FORALL pgam (FORALL dgam (FORALL a (FORALL b
   (== (LINE-INT pf pgam dgam a b)
       (CC-INT (VNB-LAMBDA pat_ (CCINT a b) (* (pf (pgam pat_)) (dgam pat_)))
               a b)))))))))
(di)
(mac 'LINE-INT)
(qrfl)
(qed 'line-int-unfold)
(topic! 'line-int-unfold 'analysis)
(alias! 'line-int-unfold
        "the integral of f along a road is the integral of f(gamma(t)) gamma'(t)")

;;; =====================================================================
;;; (3) THE TRACE.
;;; =====================================================================
(sp (make-wff '(FORALL pgam (FORALL a (FORALL b
   (== (TRACE pgam a b) (IMAGE pgam (CCINT a b))))))))
(di)
(mac 'TRACE)
(qrfl)
(qed 'trace-unfold)
(topic! 'trace-unfold 'analysis)
(alias! 'trace-unfold "the trace of a path is the image of the parameter interval")

;;; a point of the parameter interval has its value in the trace.
;;; The FUN typing is a hypothesis and is not decoration: the witness equation
;;; `pgam(t) = pgam(t)' is closed by `rfl', which since 2026-09-18 refuses a
;;; term that is not certified DEFINED, and an application is certified only
;;; through `f in FUN(D,_)' with the argument in D (CLAUDE.md, the LUTINS rule).
(sp (make-wff "forall([pgam, a, b],
   pgam in fun(ccint(a,b), cc) implies
   forall([pat_ in ccint(a,b)], pgam(pat_) in trace(pgam, a, b)))"))
(dk-peel!)
(let ((tv (cadr (cadr (dk-goal)))))
  (fact 'fun-apply-type-c 'pgam ci2-cc 'CC tv)
  (fact 'trace-unfold 'pgam 'a 'b)
  (subst (list '== (list 'TRACE 'pgam 'a 'b) (list 'IMAGE 'pgam ci2-cc)))
  (dk-image-goal!)
  (ew tv)
  (dk-conj-close! (lambda () (if (eq? (ci2-head (dk-goal)) '=) (rfl) (ass)))))
(qed 'trace-value-in)
(topic! 'trace-value-in 'analysis)
(alias! 'trace-value-in "a path takes its values in its trace")

;;; the trace lies in CC.
(sp (make-wff "forall([pgam, a, b],
   pgam in fun(ccint(a,b), cc) implies subset(trace(pgam, a, b), cc))"))
(dk-peel!)
(fact 'trace-unfold 'pgam 'a 'b)
(let ((w (subset-by-element!)))
  (dk-have! (list 'IN w (list 'IMAGE 'pgam ci2-cc))
    (lambda () (subst (list '== (list 'IMAGE 'pgam ci2-cc) '(TRACE pgam a b))) (ass)))
  ;; NOT `image-subset-codomain': that axiom is ASSERTED (injection.scm) and
  ;; citing it puts a leaf on the bill.  The membership IFF is `definitional'
  ;; and contributes {} -- skolemize it and type the value instead.
  (dk-image-hyp! (list 'IN w (list 'IMAGE 'pgam ci2-cc)))
  (let ((tv (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image existential"))))
    (dk-split-all!)
    (fact 'fun-apply-type-c 'pgam ci2-cc 'CC tv)
    (subst (list '= w (list 'pgam tv)))
    (ass)))
(qed 'trace-subset-cc)
(topic! 'trace-subset-cc 'analysis)
(alias! 'trace-subset-cc "the trace of a path is a set of complex numbers")

;;; the trace is a SET -- replacement, through `image-set'.
(sp (make-wff "forall([pgam, a, b],
   a in rr implies b in rr implies trace(pgam, a, b) in set)"))
(dk-peel!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set ci2-cc 'RR)
(fact 'image-set 'pgam ci2-cc)
(fact 'trace-unfold 'pgam 'a 'b)
(subst '(== (TRACE pgam a b) (IMAGE pgam (CCINT a b))))
(ass)
(qed 'trace-is-set)
(topic! 'trace-is-set 'analysis)

;;; =====================================================================
;;; (4) THE INTEGRAND OF A LINE INTEGRAL IS A FUNCTION ON THE INTERVAL.
;;;
;;; This is statement check (8) of the definition file, discharged: the term
;;; LINE-INT(f, gamma, dgamma, a, b) is formed unconditionally, and the
;;; condition that makes its integrand a function -- the trace inside the
;;; domain of f -- is a HYPOTHESIS here and in every law about LINE-INT.
;;; =====================================================================
(define ci2-integrand
  (list 'VNB-LAMBDA 'pat_ ci2-cc '(* (pf (pgam pat_)) (dgam pat_))))

(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'pgam (list 'FORALL 'dgam (list 'FORALL 'pf (list 'FORALL 'pad_
         (list 'IMPLIES (list 'IN 'pgam (list 'FUN ci2-cc 'CC))
         (list 'IMPLIES (list 'IN 'dgam (list 'FUN ci2-cc 'CC))
         (list 'IMPLIES '(IN pf (FUN pad_ CC))
         (list 'IMPLIES '(SUBSET (TRACE pgam a b) pad_)
           (list 'IN ci2-integrand (list 'FUN ci2-cc 'CC)))))))))))))
(dk-peel!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set ci2-cc 'RR)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (not (eq? (ci2-head (dk-goal)) 'FORALL))
       (ass)
       (let ((z (dk-di-var!)))
         (fact 'trace-value-in 'pgam 'a 'b z)
         (fact 'subset-mem-fwd '(TRACE pgam a b) 'pad_ (list 'pgam z))
         (fact 'fun-apply-type-c 'pf 'pad_ 'CC (list 'pgam z))
         (fact 'fun-apply-type-c 'dgam ci2-cc 'CC z)
         (have! (list 'AND (list 'IN (list 'pf (list 'pgam z)) 'CC)
                      (list 'IN (list 'dgam z) 'CC)))
         (fact 'cc-mul-closed (list 'pf (list 'pgam z)) (list 'dgam z))
         (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'line-int-integrand-in-fun)
(topic! 'line-int-integrand-in-fun 'analysis)
(alias! 'line-int-integrand-in-fun
        "the integrand of a line integral is a function on the parameter interval")

