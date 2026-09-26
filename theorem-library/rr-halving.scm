;;; rr-halving.scm -- every positive real splits into two equal positive
;;; halves, PROVEN.
;;;
;;;     rr-pos-halvable:  POS-RR(eps)  =>  forsome d. POS-RR(d) and d + d = eps
;;;
;;; It was a warranted support in structure-library/order-predicates.scm
;;; ("Standard (d = eps/2)"), and that file's own header named it as one of the
;;; five facts that "are now DERIVABLE, and each is a theorem waiting for a
;;; driver rather than a permanent assertion".  This is the driver.  Nothing new
;;; is needed: the witness is eps * recip(1+1), and every step below is an
;;; ordered-FIELD fact -- completeness is not involved, exactly as the header
;;; said ("halvable and shrink need only the field axioms").
;;;
;;; WHAT UNBLOCKED IT.  Not an axiom but two theorems that did not exist when
;;; the support was written: `rr-mul-pos' and `rr-recip-pos'
;;; (theorem-library/rr-recip-order.scm, which loads immediately above and whose
;;; header says in as many words that `rr-pos-halvable wants the witness
;;; eps * recip(1+1) to be positive.  Nothing in the tree said a reciprocal of a
;;; positive is positive.  That is what rr-recip-pos is').  With those, the
;;; positivity of the half is two citations.
;;;
;;; THE ARITHMETIC, and the one place it is not `crs'.  The equation
;;; d + d = eps is a ring identity ONLY modulo (1+1) * recip(1+1) = 1, which is
;;; rr-recip-inverse and not a ring fact at all.  So the closing move is a chain
;;; of two `subst's around one `crs': normalise d + d to eps * ((1+1) * r) by
;;; the ring simplifier (r = recip(1+1) is an opaque generator to it), rewrite
;;; the inverse product to 1, and let `crs' drop the unit.
;;;
;;; The witness is spelled `recip(1 + 1)', never `1 / 2': `/' is surface syntax
;;; that the parser desugars, and a quoted (/ a b) written in Scheme source
;;; leaves a head no axiom mentions (see the SPELLING note in
;;; structure-library/order-predicates.scm).
;;;
;;; Loads after rr-recip-order (rr-mul-pos, rr-recip-pos), rr-order-basics
;;; (rr-pos-ne-zero), equality-basics (neq-sym) and driver-kit -- and BEFORE its
;;; two citers, theorem-library/cauchy-subseq-proof and
;;; theorem-library/rr-complete-proof.

;;; ---- file-local driver helpers (the `rh-' prefix) --------------------
;;; (rh-peel! became dk-peel!, and the conjunction split after `ew' below
;;; dk-conj-close!, both driver-kit.scm, 2026-09-14.)
(define rh-two '(+ 1 1))
(define rh-r   (list 'recip rh-two))
(define rh-d   (list '* 'eps rh-r))

(sp (make-wff '(FORALL eps (IMPLIES (POS-RR eps)
     (FORSOME d (AND (POS-RR d) (= (+ d d) eps)))))))
(dk-peel!)

;;; eps > 0 in the strict-order spelling the multiplicative lemmas want.
(mac-h 'pos-rr '(POS-RR eps))
(dk-split! '(AND (IN eps RR) (AND (<= 0 eps) (NOT (= 0 eps)))))
(fact 'neq-sym 0 'eps)
(have! '(< 0 eps) (lambda () (mac '<) (from-context!)))

;;; 1 + 1 is a nonzero positive real, so it has a positive reciprocal.
(fact 'rr-one-in)
(have! '(AND (IN 1 RR) (IN 1 RR)))
(fact 'rr-add-closed 1 1)
(have! (list '< 0 rh-two) (lambda () (ineq)))       ; ground: the oracle decides it
(fact 'rr-pos-ne-zero rh-two)
(have! (list 'AND (list 'IN rh-two 'RR) (list 'NOT (list '= rh-two 0))))
(fact 'rr-recip-closed rh-two)
(fact 'rr-recip-inverse rh-two)                     ; (1+1) * recip(1+1) = 1
(fact 'rr-recip-pos rh-two)                         ; 0 < recip(1+1)

;;; d = eps * recip(1+1) is a positive real.
(have! (list 'AND '(IN eps RR) (list 'IN rh-r 'RR)))
(fact 'rr-mul-closed 'eps rh-r)
(fact 'rr-mul-pos 'eps rh-r)
(mac-h '< (list '< 0 rh-d))
(dk-split! (list 'AND (list '<= 0 rh-d) (list 'NOT (list '= 0 rh-d))))

(ew rh-d)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'POS-RR)
       (begin (mac 'pos-rr) (from-context!))
       (begin
         ;; d + d = eps * ((1+1) * recip(1+1)) -- a ring identity in the two
         ;; generators eps and recip(1+1), the latter opaque to `crs'.
         (have! (list '= (list '+ rh-d rh-d) (list '* 'eps (list '* rh-two rh-r)))
                (lambda () (crs)))
         (subst (list '= (list '+ rh-d rh-d) (list '* 'eps (list '* rh-two rh-r))))
         (subst (list '= (list '* rh-two rh-r) 1))   ; rr-recip-inverse
         (crs)))))                                   ; eps * 1 = eps
(qed 'rr-pos-halvable)
(topic! 'rr-pos-halvable 'inequalities)
