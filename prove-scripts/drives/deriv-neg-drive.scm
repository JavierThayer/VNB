;;; deriv-neg-drive.scm -- THE LEAF LEFT FOR THE USER (2026-08-23), from the
;;; rung-0 session that proved deriv-sum, deriv-product and the power rule.
;;;
;;; `deriv-neg' (theorem-library/differentiation.scm) is now the LAST asserted
;;; differentiation rule in the tree:
;;;
;;;   IS-DIFF-AT(f, a, L)  =>  IS-DIFF-AT(lambda z in RR. -f(z), a, -L)
;;;
;;; It is a `support' + `warrant! 'reference' whose warrant text IS the proof --
;;; "f(x)-f(a)=phi(x)(x-a) gives (-f)(x)-(-f)(a) = (-phi)(x)(x-a), with -phi
;;; continuous at a and value -L" -- the same species as deriv-sum and
;;; deriv-product were until this morning, and the same species as
;;; `compose-apply'.  It is cited by `interior-min-deriv-zero' and, through the
;;; MVT arc, by `deriv-zero-const-up' / `deriv-zero-implies-constant' /
;;; `deriv-pos-strictly-increasing' -- so it is a real leaf of four bills, not a
;;; tidiness item.
;;;
;;; Run:   ./prover -b -i prove-scripts/drives/deriv-neg-drive.scm
;;;
;;; EVERYTHING IT NEEDS IS ALREADY PROVEN.  This is deriv-sum's driver with one
;;; function instead of two:
;;;
;;;   neg-fun-in-fun     (theorem-library/neg-continuous.scm:119)
;;;                      f in FUN(RR,RR)  =>  (VNB-LAMBDA z_ RR (- (f z_))) in FUN(RR,RR)
;;;   neg-continuous-at  (theorem-library/neg-continuous.scm:195)
;;;                      f continuous at x  =>  -f continuous at x
;;;   rr-neg-closed      (number-systems.scm)   L in RR  =>  -L in RR
;;;
;;; and the shape of the driver is, line for line, the one in
;;; theorem-library/deriv-sum-product.scm:
;;;
;;;   dk-peel-to! 'IS-DIFF-AT ; mac-h the IS-DIFF-AT hypothesis ; split off the
;;;   skolem phi ; land the three citations ABOVE the goal split (so every
;;;   branch has them, and so `rfl' has its definedness witness) ; (mac
;;;   'IS-DIFF-AT) ; three (di)(ass) ; (ew <the witness>) ; three more ;
;;;   then the factorization leaf: (di), beta, inst+ the Caratheodory
;;;   universal at the eigenvariable, and (crs).
;;;
;;; THE WITNESS is (VNB-LAMBDA z_ RR (- (phi z_))) with phi the skolem read off
;;; the context -- NOT written by hand: its name is generated (phi_1635 and the
;;; like), so capture it, as the helper below does.
;;;
;;; THE ONE WRINKLE, and it is why this is worth driving rather than typing.
;;; `neg-fun-in-fun' and `neg-continuous-at' are stated with the binder `z_'
;;; (nc-neg, neg-continuous.scm:98) while `deriv-neg' is stated with `z'.  The
;;; two terms are alpha-variants, and the citations land the `z_' spelling.
;;; Whether the goal's `z' copy closes by `ass' against it is exactly the
;;; question `alpha-equiv?' answers -- check it rather than assume it.  If it
;;; does not, the honest fix is to restate deriv-neg with `z_' (the statement is
;;; being retired from a `support' anyway, so nothing cites the old spelling),
;;; NOT to add a renaming lemma.
;;;
;;; The last leaf, after the beta, is
;;;
;;;     -f(x) - (-f(a))  =  (-phi(x)) * (x - a)
;;;
;;; with  f(x) - f(a) = phi(x)(x-a)  in context.  It is deriv-sum's endgame with
;;; one term: `have!' the distribution as a `crs' side goal, `subst' it, `eq-sym'
;;; + `subst' the Caratheodory identity in, and `crs'.  Type f(x), f(a), phi(x)
;;; and (x-a) first (fun-apply-type-c, rr-sub-in-rr) -- `crs' wants the
;;; certificates, and `rfl' wants the definedness witness.
;;;
;;; When it closes: retire the support in differentiation.scm with a pointer
;;; comment (as the sum/product pair now are), put the proof in
;;; theorem-library/deriv-neg.scm, add the load.scm entry right after
;;; deriv-sum-product, and re-measure -- the four citing bills are the point.

;;; ---- helpers, the same three deriv-sum-product.scm uses -----------------
(define (dn-split!)
  (let loop ((n 0))
    (let ((tgt (any-pred (lambda (a) (and (pair? a) (memq (car a) '(AND FORSOME))))
                         (dk-asms))))
      (if (and tgt (< n 30)) (begin (ai tgt) (loop (+ n 1)))))))

(define (dn-phi-for pt val)
  (let ((h (any-pred (lambda (a) (and (pair? a) (eq? (car a) '=)
                                      (equal? (caddr a) val)
                                      (pair? (cadr a)) (= (length (cadr a)) 2)
                                      (equal? (cadr (cadr a)) pt)))
                     (dk-asms))))
    (if h (car (cadr h)) (error "dn-phi-for: no factor assumption for" val))))

(define (dn-beta!)
  (let loop ((k 0) (prev #f))
    (let ((g (dk-goal)))
      (if (and (< k 8) (not (equal? g prev)))
          (begin (quietly (lambda () (vnb-guard (lambda () (lam-b))))) (loop (+ k 1) g))))))

;;; ---- the goal, VERBATIM from differentiation.scm ------------------------
(sp (make-wff
 '(FORALL f (FORALL a (FORALL L
    (IMPLIES (IS-DIFF-AT f a L)
      (IS-DIFF-AT (VNB-LAMBDA z RR (- (f z))) a (- L))))))))
(dk-peel-to! 'IS-DIFF-AT)
(mac-h 'IS-DIFF-AT '(IS-DIFF-AT f a l))
(dn-split!)
(define dn-phi (dn-phi-for 'a 'l))
(define dn-w (list 'VNB-LAMBDA 'z_ 'RR (list '- (list dn-phi 'z_))))
(display ";; the skolem factor is ") (write dn-phi) (newline)
(display ";; the witness is        ") (write dn-w) (newline)
(display ";; goal: ") (write (dk-goal)) (newline)
(display ";; over to you: (fact 'rr-neg-closed 'l), (fact 'neg-fun-in-fun 'f),")
(newline)
(display ";;              (fact 'neg-fun-in-fun ") (write dn-phi) (display "),")
(newline)
(display ";;              (fact 'neg-continuous-at ") (write dn-phi)
(display " 'a), then (mac 'IS-DIFF-AT).")
(newline)
