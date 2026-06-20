;;; sos-oracle.scm -- the (sos) sum-of-squares oracle: close a nonstrict
;;; polynomial inequality goal over RR from a supplied list of square
;;; certificates.  The nonlinear companion of (ineq).
;;;
;;; (ineq) decides LINEAR arithmetic over RR: it treats every maximal
;;; non-arithmetic subterm as an opaque atom, so x*y, x^2, y^2 are three
;;; unrelated atoms and  x*y <= x^2 + y^2  is invisible to it.  (sos) supplies
;;; the missing nonlinear lane.  Given a goal
;;;
;;;     a <= b           (or b >= a)
;;;
;;; over RR and a handful of certificate terms  c_1 .. c_n,  it forms the
;;; difference polynomial  D = b - a  in crs's free commutative ring
;;; ZZ[generators] and asks whether D is a NONNEGATIVE rational combination of
;;; the squares:  D = Sum_i lambda_i c_i^2  with every  lambda_i >= 0.  The
;;; coefficient-matching is decided exactly by the Phase-I simplex in
;;; sos-arith.scm (the "modulo the ring identity crs already decides" step --
;;; equality is checked monomial-by-monomial in the crs normal form).  On
;;; success each  c_i^2 >= 0  over RR (rr-sq-nonneg) and  lambda_i >= 0,  so
;;; D >= 0  and  a <= b.
;;;
;;; PREDICTABLE, NO SEARCH: like (ineq i j ...) naming its premises, (sos)
;;; takes the certificate terms explicitly -- it is a VERIFIER, not a
;;; certificate finder.  The user (who knows the SOS decomposition) supplies
;;; the squares; the oracle checks the nonneg combination exists.
;;;
;;; SOUNDNESS: every generator of a, b and the c_i must be certified in RR (an
;;; (IN g RR) assumption, an abs(.) term, or an RR-typed goal binder); then
;;; each c_i (a ring expression in RR generators) lies in RR, c_i^2 >= 0, and
;;; the exact identity D = Sum lambda_i c_i^2 (enforced on every monomial) plus
;;; lambda_i >= 0 give 0 <= D = b - a.  Strict (<) goals are refused: a square
;;; may vanish, so squares alone never witness a strict inequality.  Trusted
;;; oracle; warrant 'sos below; each success prints its certificate.
;;;
;;; Dependencies: comm-ring-simplify.scm (cvnb->poly, cvnb-expand-pow,
;;; cpoly-mul, cvnb-source-generators, dedup-equal), ring-simplify.scm
;;; (poly-add, poly-neg), ineq-oracle.scm (ineq-peel-rr-foralls,
;;; ineq-atom-rr-ok?), sos-arith.scm (sos-nonneg-combo), kernel (sqn/dg).

;;; The square of a certificate term as a commutative poly, or #f if the term
;;; is not polynomializable.  Literal powers are pre-expanded (cvnb->poly has
;;; no `^'), exactly as crs does.
(define (sos-square-poly term)
  (let ((p (cvnb->poly (cvnb-expand-pow term))))
    (and p (cpoly-mul p p))))

;;; Print the verified certificate:  b - a = l1*(c1)^2 + l2*(c2)^2 + ...
;;; (zero-weight squares are dropped).
(define (sos-report certs lams)
  (display ";; sos: certificate  b - a = ")
  (let loop ((cs certs) (ls lams) (first #t))
    (cond
      ((null? cs) (if first (display "0")) (newline))
      ((= (car ls) 0) (loop (cdr cs) (cdr ls) first))
      (else
       (if (not first) (display " + "))
       (if (not (= (car ls) 1)) (begin (display (car ls)) (display "*")))
       (display "(") (display (expression->string (car cs))) (display ")^2")
       (loop (cdr cs) (cdr ls) #f)))))

;;; Short usage, printed when (sos) is called with no certificate -- a friendly
;;; nudge instead of an attempted (and failing) proof.
(define (sos-print-usage)
  (display ";; sos -- sum-of-squares closer for a nonstrict polynomial  a <= b  over RR.\n")
  (display ";; Supply the terms to be SQUARED (not the squares); sos finds nonnegative\n")
  (display ";; lambda_i with  b - a = lambda_1 c_1^2 + ... + lambda_n c_n^2  and closes.\n")
  (display ";;   e.g.  x*y <= x^2 + y^2  is closed by   (sos \"x - y\" \"x\" \"y\")\n")
  (display ";; Full explanation and more examples:  (tactics 'sos)\n"))

;;; Primitive inference: close  a <= b  (or  b >= a) over RR by a supplied
;;; sum-of-squares certificate.  cert-terms are raw s-expr terms.
(define (pi-sos! sqn cert-terms)
  (let* ((goal0 (wff-formula (sequent-node-assertion sqn)))
         (peel  (ineq-peel-rr-foralls goal0))
         (goal  (car peel))
         (rrqv  (cdr peel))
         (asms  (sequent-node-assumptions sqn))
         (dg    (sqn-dg sqn)))
    (and (pair? goal) (= (length goal) 3)
         (memq (car goal) '(<= >=))
         (let* ((flip (eq? (car goal) '>=))
                (a  (if flip (caddr goal) (cadr goal)))
                (b  (if flip (cadr goal) (caddr goal)))
                (ea (cvnb-expand-pow a))
                (eb (cvnb-expand-pow b))
                (pa (cvnb->poly ea))
                (pb (cvnb->poly eb)))
           (and pa pb
                (let ((Dpoly   (poly-add pb (poly-neg pa)))
                      (squares (map sos-square-poly cert-terms)))
                  (and (not (memq #f squares))
                       (let ((gens (dedup-equal
                                     (append
                                       (cvnb-source-generators ea)
                                       (cvnb-source-generators eb)
                                       (apply append
                                         (map (lambda (c)
                                                (cvnb-source-generators
                                                  (cvnb-expand-pow c)))
                                              cert-terms))))))
                         (and (let allok ((vs gens))
                                (or (null? vs)
                                    (and (ineq-atom-rr-ok? (car vs) asms rrqv)
                                         (allok (cdr vs)))))
                              (let ((lam (sos-nonneg-combo squares Dpoly)))
                                (and lam
                                     (begin (sos-report cert-terms lam)
                                            (dg-apply-rule! dg 'sos '() sqn)))))))))))))

(warrant! 'sos 'well-known
  "Sum-of-squares certificate for a nonstrict polynomial inequality over the
   ordered field RR.  For a goal a <= b and supplied terms c_1..c_n (all over
   RR-certified generators), the difference b - a is normalised to its
   commutative-ring sum-of-monomials form (crs's free ZZ[generators]) and a
   Phase-I simplex over the exact rationals decides whether it is a nonnegative
   rational combination Sum lambda_i c_i^2 of the certificate squares.  Each
   c_i^2 >= 0 (rr-sq-nonneg) and lambda_i >= 0, so the verified identity gives
   0 <= b - a, i.e. a <= b.  The monomial-by-monomial match is the standard
   commutative-ring normal-form decision (sound and complete); the nonnegative
   solve is exact LP.  Strict goals are refused (a square may be zero).
   Computed in Scheme as a trusted oracle; each closure prints its certificate.")
