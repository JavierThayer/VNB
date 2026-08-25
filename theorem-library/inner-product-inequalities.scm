;;; inner-product-inequalities.scm -- CAUCHY-SCHWARZ and MINKOWSKI at the
;;; INNER-PRODUCT level, over a COMPLEX-INNER-PRODUCT-SPACE.  Both PROVEN
;;; modulo 0.
;;;
;;;   cips-schwarz     |<x,y>|^2  <=  <x,x> <y,y>
;;;                    written <x,y> conj<x,y> <= <x,x><y,y>, so that no SQRT
;;;                    and no `magnitude' appear in the statement at all.
;;;   cips-minkowski   ||x+y||  <=  ||x|| + ||y||   for  ||u|| = SQRT(<u,u>)
;;;                    (IP-NORM, structure-library/complex-inner-product.scm) --
;;;                    i.e. the triangle inequality for the induced norm, and so
;;;                    the one law of `ip-normed-ag-is-normed-ag' with content.
;;;
;;; NOT A DUPLICATE OF analysis-inequalities.scm, and the difference is the
;;; point.  That file asserts `cauchy-schwarz-finite', `cauchy-schwarz-sqrt' and
;;; `minkowski-l2' as `well-known' supports about FINITE SUMS OF REALS, with the
;;; Lagrange identity named in the warrant as the argument nobody has run.  These
;;; two cite neither of them and need no sums whatever: an inner product space is
;;; where these inequalities LIVE, and the finite-sum forms are the instance at
;;; RR^n with <a,b> = SUM a_i b_i.  Discharging those three supports means
;;; building that instance -- exhibiting RR^n as a COMPLEX-INNER-PRODUCT-SPACE
;;; and proving the sum form is its IP -- which is a separate piece of work and
;;; is NOT done here.
;;;
;;; SCHWARZ: NO DIVISION, ONE CASE SPLIT.  The textbook proof puts
;;; t = <x,y>/<y,y> and expands 0 <= <x - t y, x - t y>.  Division is avoidable
;;; and worth avoiding -- `crs' decides polynomial identities over CC but knows
;;; nothing about `recip' -- so the test vector is CLEARED of its denominator:
;;;
;;;     z  =  <y,y> . x  +  (-<x,y>) . y
;;;
;;; `cips-expand-two' (theorem-library/complex-inner-product-laws.scm) at
;;; (a,b) = (<y,y>, -<x,y>), with conj<y,y> = <y,y> (the diagonal is real) and
;;; conj(-p) = -conj(p) (`cc-conjugate-neg'), collapses to
;;;
;;;     <z,z>  =  <y,y> * ( <y,y><x,x>  -  <x,y> conj<x,y> )
;;;
;;; in one `crs'.  Positive-definiteness gives 0 <= <z,z>, and the factor <y,y>
;;; comes off by `rr-nonneg-cancel-pos' (theorem-library/rr-order-basics.scm,
;;; added with this file) -- which needs <y,y> > 0, hence the split.  In the
;;; other branch <y,y> = 0 forces y = 0 (cips-ip-zero-vector) and then
;;; <x,y> = <x,0> = 0 (cips-ip-zero-right), so both sides are 0.
;;;
;;; MINKOWSKI: SQUARE, THEN TAKE ROOTS.  `cips-expand-sum' gives
;;; ||x+y||^2 = <x,x> + (<x,y> + conj<x,y>) + <y,y>, and the cross term is
;;; 2 Re<x,y> (`cc-plus-conj-is-2re').  Re(p)^2 <= p conj p
;;; (`cc-re-sq-le-mod-sq') composed with Schwarz gives Re<x,y>^2 <= (||x|| ||y||)^2,
;;; and `sqrt-of-sq' / `sqrt-mono' / `rr-abs-of-nonneg' turn that into
;;; Re<x,y> <= ||x|| ||y||.  Hence ||x+y||^2 <= (||x|| + ||y||)^2, and one more
;;; sqrt-mono finishes.  Nothing here reasons about square roots directly: every
;;; step is a ring identity, a linear consequence, or one of the five sqrt facts
;;; PROVEN in theorem-library/sqrt-defined.scm -- which is why both bills are
;;; `modulo 0' rather than leaning on the SQRT supports of real-powers.scm.
;;;
;;; WHY THE CROSS TERM IS ROUTED THROUGH `real-part'.  `ineq' certifies an atom
;;; only from an (IN t RR) assumption (ineq-atom-rr-ok?, ineq-oracle.scm:112),
;;; and `vnb->linear' decomposes a sum, so the cross term written
;;; `<x,y> + conj<x,y>' arrives at the oracle as two COMPLEX atoms and the whole
;;; call is refused.  Rewritten as 2 Re<x,y> it is one atom, and
;;; `real-part-in-rr' certifies it.  The two bridging facts,
;;; `cc-plus-conj-is-2re' and `cc-re-sq-le-mod-sq', are proved in
;;; theorem-library/cc-real-imag.scm, where `real-part' is defined.
;;;
;;; A TRAP THAT COST A RUN, and it is the working brief's case-fold rule in its
;;; purest form: the term abbreviations below were first written `ii-p' for
;;; <x,y> and `ii-P' for <x,y>conj<x,y>.  MIT Scheme folds symbols, so those are
;;; ONE variable; the second definition silently replaced the first, the test
;;; vector went in as -|<x,y>|^2 rather than -<x,y>, and the only symptom was a
;;; `crs' declining an identity that was, correctly, not one.  Never distinguish
;;; two names by case.
;;;
;;; LOAD POSITION.  After complex-inner-product-laws (the expansions), after
;;; sqrt-defined (sqrt-nonneg/-sq/-of-sq/-mono), after cc-real-imag (the two
;;; bridges above and real-part-in-rr), after rr-order-basics
;;; (rr-nonneg-cancel-pos, rr-le-from-diff-nonneg, rr-le-cases, rr-le-scale-nonneg,
;;; rr-sq-nonneg, rr-abs-*) and after binary-minus-laws (rr-sub-in-rr).

;;; --------------------------------------------------------------------
;;; File-local driver helpers (the `ii-' / `mk-' prefixes -- never named like a
;;; tactic; see the case-fold section of the working brief).

;;; Peel the whole FORALL/IMPLIES prefix, guarded on a fuel count as well as on
;;; the head: `di' only WARNS when it cannot decompose, so a head test alone
;;; spins forever on a no-op.
(define (ii-peel!)
  (let loop ((n 0)) (let ((g (dk-goal)))
    (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14)) (begin (di) (loop (+ n 1))) #t))))

;;; The 1-based index of a context formula.  A bare `(ineq)' names NO premises
;;; (cmd-ineq passes idxs through unchanged, proof-commands.scm:717), so every
;;; `ineq' below names the assumptions it uses -- and names only those, since an
;;; `=' between COMPLEX terms is arithmetic in SHAPE and would contribute atoms
;;; that can never be certified in RR.
(define (ii-idx f)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ii-idx: not in context" f))
          ((equal? (car l) f) i) (else (loop (cdr l) (+ i 1))))))

;;; ====================================================================
;;; CAUCHY-SCHWARZ
;;; ====================================================================
(define ii-aa '((IP v) x_ x_))
(define ii-bb '((IP v) y_ y_))
(define ii-xy '((IP v) x_ y_))
(define ii-conj (list 'conjugate ii-xy))
(define ii-mod2 (list '* ii-xy ii-conj))
(define ii-vw (list '(ACT v) ii-bb 'x_))
(define ii-vu (list '(ACT v) (list '- ii-xy) 'y_))
(define ii-vz (list '(VADD v) ii-vw ii-vu))
(define ii-zz (list '(IP v) ii-vz ii-vz))
(define ii-ba (list '* ii-bb ii-aa))
(define ii-ab (list '* ii-aa ii-bb))
(define ii-diff (list '- ii-ba ii-mod2))

(sp (make-wff (forall-guarded '(v x_ y_)
   (list '(IS-COMPLEX-INNER-PRODUCT-SPACE v) '(IN x_ (VEC v)) '(IN y_ (VEC v)))
   (list '<= ii-mod2 ii-ab))))
(ii-peel!)
(have! '(IN 0 RR) (lambda () (arith)))
(fact 'cips-ip-self-real 'v 'x_)
(fact 'cips-ip-self-real 'v 'y_)
(fact 'cips-ip-self-nonneg 'v 'x_)
(fact 'cips-ip-self-nonneg 'v 'y_)
(fact 'cips-ip-type 'v 'x_ 'y_)
(fact 'cc-conjugate-closed ii-xy)
(fact 'rr-subset-cc ii-aa)
(fact 'cc-self-conj-nonneg ii-xy)
(ai (list 'AND (list 'IN ii-mod2 'RR) (list '<= 0 ii-mod2)))
(have! (list 'AND (list 'IN ii-aa 'RR) (list 'IN ii-bb 'RR)))
(fact 'rr-mul-closed ii-aa ii-bb)
(have! (list 'AND (list 'IN ii-bb 'RR) (list 'IN ii-aa 'RR)))
(fact 'rr-mul-closed ii-bb ii-aa)
(fact 'rr-sub-in-rr ii-ba ii-mod2)
(fact 'rr-le-cases 0 ii-bb)
(use-cases (list (list '< 0 ii-bb) (list '= 0 ii-bb))
  ;; --- 0 < <y,y> : the real case ---
  (lambda ()
    (fact 'rr-subset-cc ii-bb)
    (fact 'cc-neg-closed ii-xy)
    (fact 'cips-act-type 'v ii-bb 'x_)
    (fact 'cips-act-type 'v (list '- ii-xy) 'y_)
    (fact 'cips-vadd-type 'v ii-vw ii-vu)
    (fact 'cips-ip-self-nonneg 'v ii-vz)
    (fact 'cips-expand-two 'v ii-bb (list '- ii-xy) 'x_ 'y_)
    (fact 'cc-conjugate-fixes-rr ii-bb)
    (fact 'cc-conjugate-neg ii-xy)
    (have! (list '= ii-zz (list '* ii-bb ii-diff))
      (lambda ()
        (subst (list '= ii-zz
           (list '+ (list '+ (list '* (list '* ii-bb (list 'conjugate ii-bb)) ii-aa)
                             (list '* (list '* ii-bb (list 'conjugate (list '- ii-xy))) ii-xy))
                    (list '+ (list '* (list '* (list '- ii-xy) (list 'conjugate ii-bb)) (list 'conjugate ii-xy))
                             (list '* (list '* (list '- ii-xy) (list 'conjugate (list '- ii-xy))) ii-bb)))))
        (subst (list '= (list 'conjugate ii-bb) ii-bb))
        (subst (list '= (list 'conjugate (list '- ii-xy)) (list '- (list 'conjugate ii-xy))))
        (crs)))
    (have! (list '<= 0 (list '* ii-bb ii-diff))
      (lambda () (subst (list '= (list '* ii-bb ii-diff) ii-zz)) (ass)))
    (fact 'rr-nonneg-cancel-pos ii-bb ii-diff)
    (have! (list '= ii-ab ii-ba) (lambda () (crs)))
    (have! (list '<= 0 (list '- ii-ab ii-mod2))
      (lambda () (subst (list '= ii-ab ii-ba)) (ass)))
    (fact 'rr-le-from-diff-nonneg ii-mod2 ii-ab)
    (ass))
  ;; --- <y,y> = 0 : y is the zero vector ---
  (lambda ()
    (fact 'eq-sym 0 ii-bb)
    (fact 'cips-ip-zero-vector 'v 'y_)
    (fact 'cips-vzero-in 'v)
    (fact 'cips-ip-zero-right 'v 'x_)
    (fact 'cips-ip-zero-right 'v '(VZERO v))
    (fact 'cc-conjugate-fixes-rr 0)
    (subst '(= y_ (VZERO v)))
    (subst '(= ((IP v) x_ (VZERO v)) 0))
    (subst '(= ((IP v) (VZERO v) (VZERO v)) 0))
    (subst '(= (conjugate 0) 0))
    (have! (list '= (list '* 0 0) 0) (lambda () (crs)))
    (subst (list '= (list '* 0 0) 0))
    (have! (list '= (list '* ii-aa 0) 0) (lambda () (crs)))
    (subst (list '= (list '* ii-aa 0) 0))
    (arith)))
(qed 'cips-schwarz)
(topic! 'cips-schwarz 'inequalities)
(alias! 'cips-schwarz "the Cauchy-Schwarz inequality" "Schwarz inequality")

;;; ====================================================================
;;; MINKOWSKI -- the triangle inequality for the induced norm
;;; ====================================================================
;;; Term abbreviations, `mk-' prefixed.  mk-re is Re<x,y>: the cross term of the
;;; expansion is <x,y> + conj<x,y>, and it is carried in that form ONLY as far as
;;; `cc-plus-conj-is-2re', because `ineq' would decompose the sum into two
;;; complex atoms and refuse the call (see the header).
(define mk-aa   '((IP v) x_ x_))
(define mk-bb   '((IP v) y_ y_))
(define mk-xy   '((IP v) x_ y_))
(define mk-conj (list 'conjugate mk-xy))
(define mk-mod2 (list '* mk-xy mk-conj))
(define mk-re   (list 'real-part mk-xy))
(define mk-sa   (list 'SQRT mk-aa))
(define mk-sb   (list 'SQRT mk-bb))
(define mk-sasb (list '* mk-sa mk-sb))
(define mk-sum  '((VADD v) x_ y_))
(define mk-tt   (list '(IP v) mk-sum mk-sum))
(define mk-ssum (list '+ mk-sa mk-sb))

(sp (make-wff (forall-guarded '(v x_ y_)
   (list '(IS-COMPLEX-INNER-PRODUCT-SPACE v) '(IN x_ (VEC v)) '(IN y_ (VEC v)))
   (list '<= (list 'IP-NORM 'v mk-sum) (list '+ '(IP-NORM v x_) '(IP-NORM v y_))))))
(ii-peel!)
(mac 'ip-norm)
(have! '(IN 0 RR) (lambda () (arith)))
(fact 'cips-vadd-type 'v 'x_ 'y_)
(fact 'cips-ip-self-real 'v 'x_)
(fact 'cips-ip-self-real 'v 'y_)
(fact 'cips-ip-self-real 'v mk-sum)
(fact 'cips-ip-self-nonneg 'v 'x_)
(fact 'cips-ip-self-nonneg 'v 'y_)
(fact 'cips-ip-self-nonneg 'v mk-sum)
(fact 'cips-ip-type 'v 'x_ 'y_)
(fact 'cc-conjugate-closed mk-xy)
(fact 'real-part-in-rr mk-xy)
(fact 'cc-self-conj-nonneg mk-xy)
(ai (list 'AND (list 'IN mk-mod2 'RR) (list '<= 0 mk-mod2)))
(have! (list 'AND (list 'IN mk-aa 'RR) (list '<= 0 mk-aa)))
(fact 'sqrt-nonneg mk-aa)
(ai (list 'AND (list 'IN mk-sa 'RR) (list '<= 0 mk-sa)))
(fact 'sqrt-sq mk-aa)
(have! (list 'AND (list 'IN mk-bb 'RR) (list '<= 0 mk-bb)))
(fact 'sqrt-nonneg mk-bb)
(ai (list 'AND (list 'IN mk-sb 'RR) (list '<= 0 mk-sb)))
(fact 'sqrt-sq mk-bb)
(have! (list 'AND (list 'IN mk-sa 'RR) (list 'IN mk-sb 'RR)))
(fact 'rr-mul-closed mk-sa mk-sb)
(fact 'rr-add-closed mk-sa mk-sb)
(have! (list 'AND (list 'IN mk-ssum 'RR) (list 'IN mk-ssum 'RR)))
(fact 'rr-mul-closed mk-ssum mk-ssum)
(have! (list 'AND (list 'IN mk-aa 'RR) (list 'IN mk-bb 'RR)))
(fact 'rr-mul-closed mk-aa mk-bb)
(have! (list 'AND (list 'IN mk-re 'RR) (list 'IN mk-re 'RR)))
(fact 'rr-mul-closed mk-re mk-re)
(have! (list 'AND (list 'IN mk-sasb 'RR) (list 'IN mk-sasb 'RR)))
(fact 'rr-mul-closed mk-sasb mk-sasb)
(fact 'rr-abs-closed mk-re)
;; 0 <= sa*sb  and  0 <= sa+sb
(have! (list 'AND (list '<= 0 mk-sa) (list '<= 0 mk-sb)))
(fact 'rr-le-scale-nonneg mk-sa 0 mk-sb)
(have! (list '= (list '* mk-sa 0) 0) (lambda () (crs)))
(have! (list '<= 0 mk-sasb) (lambda () (subst (list '= 0 (list '* mk-sa 0))) (ass)))
(have! (list '<= 0 mk-ssum)
       (lambda () (ineq (ii-idx (list '<= 0 mk-sa)) (ii-idx (list '<= 0 mk-sb)))))
;; Re(<x,y>)^2 <= |<x,y>|^2 <= <x,x><y,y> = (sa sb)^2
(fact 'cips-schwarz 'v 'x_ 'y_)
(fact 'cc-re-sq-le-mod-sq mk-xy)
(have! (list '<= (list '* mk-re mk-re) (list '* mk-aa mk-bb))
   (lambda () (ineq (ii-idx (list '<= (list '* mk-re mk-re) mk-mod2))
                    (ii-idx (list '<= mk-mod2 (list '* mk-aa mk-bb))))))
;; (sa sb)^2 = A B.  Substituting A -> sa*sa would rewrite the A INSIDE
;; sa = SQRT(A) as well (replace-term is a Leibniz walk), so the equation is
;; built the other way round: crs first, then the two sqrt-sq rewrites FORWARD.
(have! (list '= (list '* mk-sasb mk-sasb) (list '* (list '* mk-sa mk-sa) (list '* mk-sb mk-sb)))
   (lambda () (crs)))
(have! (list '= (list '* mk-sasb mk-sasb) (list '* mk-aa mk-bb))
   (lambda ()
     (subst (list '= (list '* mk-sasb mk-sasb) (list '* (list '* mk-sa mk-sa) (list '* mk-sb mk-sb))))
     (subst (list '= (list '* mk-sa mk-sa) mk-aa))
     (subst (list '= (list '* mk-sb mk-sb) mk-bb))
     (crs)))
(have! (list '<= (list '* mk-re mk-re) (list '* mk-sasb mk-sasb))
   (lambda () (subst (list '= (list '* mk-sasb mk-sasb) (list '* mk-aa mk-bb))) (ass)))
;; Re <= sa*sb, through abs and sqrt-mono
(fact 'sqrt-of-sq mk-re)
(fact 'rr-le-abs mk-re)
(fact 'rr-sq-nonneg mk-re)
(fact 'sqrt-of-sq mk-sasb)
(have! (list 'AND (list 'IN mk-sasb 'RR) (list '<= 0 mk-sasb)))
(fact 'rr-abs-of-nonneg mk-sasb)
(have! (list 'AND (list 'IN (list '* mk-re mk-re) 'RR) (list '<= 0 (list '* mk-re mk-re))))
(have! (list 'AND (list 'IN (list '* mk-sasb mk-sasb) 'RR)
                  (list '<= (list '* mk-re mk-re) (list '* mk-sasb mk-sasb))))
(fact 'sqrt-mono (list '* mk-re mk-re) (list '* mk-sasb mk-sasb))
(have! (list '<= (list 'abs mk-re) mk-sasb)
   (lambda ()
     (subst (list '= (list 'abs mk-re) (list 'SQRT (list '* mk-re mk-re))))
     (subst (list '= mk-sasb (list 'abs mk-sasb)))
     (subst (list '= (list 'abs mk-sasb) (list 'SQRT (list '* mk-sasb mk-sasb))))
     (ass)))
(have! (list '<= mk-re mk-sasb)
   (lambda () (ineq (ii-idx (list '<= mk-re (list 'abs mk-re)))
                    (ii-idx (list '<= (list 'abs mk-re) mk-sasb)))))
;; T = A + 2Re + B  <=  A + 2 sa sb + B  =  (sa+sb)^2
(fact 'cips-expand-sum 'v 'x_ 'y_)
(fact 'cc-plus-conj-is-2re mk-xy)
(have! (list '= mk-tt (list '+ (list '+ mk-aa (list '* 2 mk-re)) mk-bb))
   (lambda ()
     (subst (list '= mk-tt (list '+ (list '+ mk-aa mk-xy) (list '+ mk-conj mk-bb))))
     (subst (list '= (list '* 2 mk-re) (list '+ mk-xy mk-conj)))
     (crs)))
(have! (list '= (list '* mk-ssum mk-ssum)
              (list '+ (list '+ (list '* mk-sa mk-sa) (list '* 2 mk-sasb)) (list '* mk-sb mk-sb)))
   (lambda () (crs)))
(have! (list '= (list '* mk-ssum mk-ssum) (list '+ (list '+ mk-aa (list '* 2 mk-sasb)) mk-bb))
   (lambda ()
     (subst (list '= (list '* mk-ssum mk-ssum)
                   (list '+ (list '+ (list '* mk-sa mk-sa) (list '* 2 mk-sasb)) (list '* mk-sb mk-sb))))
     (subst (list '= (list '* mk-sa mk-sa) mk-aa))
     (subst (list '= (list '* mk-sb mk-sb) mk-bb))
     (crs)))
(have! (list '<= mk-tt (list '* mk-ssum mk-ssum))
   (lambda ()
     (subst (list '= (list '* mk-ssum mk-ssum) (list '+ (list '+ mk-aa (list '* 2 mk-sasb)) mk-bb)))
     (ineq (ii-idx (list '= mk-tt (list '+ (list '+ mk-aa (list '* 2 mk-re)) mk-bb)))
           (ii-idx (list '<= mk-re mk-sasb)))))
;; ... and take square roots
(have! (list 'AND (list 'IN mk-tt 'RR) (list '<= 0 mk-tt)))
(have! (list 'AND (list 'IN (list '* mk-ssum mk-ssum) 'RR) (list '<= mk-tt (list '* mk-ssum mk-ssum))))
(fact 'sqrt-mono mk-tt (list '* mk-ssum mk-ssum))
(fact 'sqrt-of-sq mk-ssum)
(have! (list 'AND (list 'IN mk-ssum 'RR) (list '<= 0 mk-ssum)))
(fact 'rr-abs-of-nonneg mk-ssum)
(subst (list '= mk-ssum (list 'abs mk-ssum)))
(subst (list '= (list 'abs mk-ssum) (list 'SQRT (list '* mk-ssum mk-ssum))))
(ass)
(qed 'cips-minkowski)

(topic! 'cips-minkowski 'inequalities)
(alias! 'cips-minkowski "the Minkowski inequality" "the triangle inequality for an inner-product norm")
