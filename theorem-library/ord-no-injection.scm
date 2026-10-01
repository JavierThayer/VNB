;;; ord-no-injection.scm -- NO SET RECEIVES AN INJECTIVE CLASS FUNCTION FROM ORD.
;;;
;;;   ord-no-injection-into-set :
;;;     grd in SET  and  (forall alpha in ORD. phi(alpha) in grd)
;;;     and phi injective on ORD   =>   FALSITY
;;;
;;; This is the Burali-Forti endgame, factored out.  It is the whole reason the
;;; SECOND route to Zorn's lemma is cheaper than the first.
;;;
;;; ROUTE ONE (theorem-library/zorn-proof.scm) walks a well-ordering of grd and
;;; keeps the elements that dominate everything kept so far; the kept set is a
;;; chain (rung 3, proven there), and its upper bound is maximal BECAUSE anything
;;; strictly above it would have been phi(beta) for some beta and so would have
;;; been kept.  That last step needs the enumeration to be SURJECTIVE onto grd,
;;; and the general-ordinal enumeration supports for that do not exist.  Rung 4
;;; has been stuck there.
;;;
;;; ROUTE TWO never enumerates grd at all.  Assume the inductive partial order
;;; has NO maximal element and build, by transfinite recursion, a STRICTLY
;;; INCREASING F : ORD -> grd:
;;;     F(0)        = some element of grd                     (grd nonempty)
;;;     F(succ a)   = some element strictly above F(a)         (a is not maximal)
;;;     F(lim)      = an upper bound of { F(b) : b ORD-LT lim }  (INDUCTIVITY)
;;; Inductivity is used at the LIMIT stages only -- and there it is enough on its
;;; own: an upper bound u of a strictly increasing family is automatically
;;; STRICTLY above every member (if u = F(b) then F(succ b) > F(b) = u >= F(succ b),
;;; against antisymmetry), so no appeal to "not maximal" is needed at limits.
;;; Strictly increasing gives injective, and this file closes the argument.
;;;
;;; ================= THE ARGUMENT, IN SEVEN CLAIMS =========================
;;;
;;;   R := { y in grd : y = phi(b) for some ordinal b }    -- the image of ORD
;;;   INV(x) := CHOICE { c in ORD : phi(c) = phi(x) }      -- an inverse for phi
;;;   H := w |-> CHOICE { c in ORD : phi(c) = w }          -- INV as a class map
;;;
;;;   1.  R is a set.                                 SEPARATION (not replacement)
;;;   2.  phi(x) in R,          for every ordinal x.  definition of R, witness x
;;;   3.  INV(x) = x,           for every ordinal x.  choice, then INJECTIVITY
;;;   4.  ORD is contained in IMAGE(H, R).            2 + 3
;;;   5.  IMAGE(H, R) is a set.                       REPLACEMENT (image-set)
;;;   6.  ORD is a set.                               4 + 5, subclass of a set
;;;   7.  Contradiction.                              burali-forti
;;;
;;; Claims 2 and 3 are proved as standalone universal statements rather than
;;; inline inside 4; that is what keeps 4 down to "cite them both".  Claim 3 is
;;; stated in the BETA-REDUCED form INV(x), so nothing in this file has to dig a
;;; sub-term out of a goal: `lam-b' in claim 4 turns H(phi(x)) into INV(x) and
;;; the two meet.
;;;
;;; WHAT IT COSTS.  Everything is already installed: image-set
;;; (structure-library/injection.scm:99, whose own comment names it
;;; "replacement"), subclass-of-set-is-set (set-basics.scm), burali-forti
;;; (ordinals.scm:17), and choice-axiom (library.scm:311) -- GLOBAL choice, so the
;;; SEP inside H may range over the proper class ORD.  Nothing new is asserted.

(define oni-R '(SEP y_ grd (FORSOME b_ (AND (IN b_ ORD) (= (phi b_) y_)))))
(define oni-H '(VNB-LAMBDA w_ grd (CHOICE (SEP c_ ORD (= (phi c_) w_)))))
(define (oni-fibre x) `(SEP c_ ORD (= (phi c_) (phi ,x))))   ; the fibre over phi(x)
(define (oni-inv   x) `(CHOICE ,(oni-fibre x)))              ; H(phi(x)), beta-reduced

(define oni-claim2 `(FORALL x (IMPLIES (IN x ORD) (IN (phi x) ,oni-R))))
(define oni-claim3 `(FORALL x (IMPLIES (IN x ORD) (= ,(oni-inv 'x) x))))

(sp (make-wff
      (nest-quantifiers 'FORALL '(grd phi)
        (fold-right (lambda (a acc) `(IMPLIES ,a ,acc))
          'FALSITY
          (list '(IN grd SET)
                (forall-guarded '(alpha) '((IN alpha ORD)) '(IN (phi alpha) grd))
                (forall-guarded '(a1_) '((IN a1_ ORD))
                  (forall-guarded '(a2_) '((IN a2_ ORD))
                    '(IMPLIES (= (phi a1_) (phi a2_)) (= a1_ a2_)))))))))
(di) (di) (di) (di)
(define oni-inj (car  (dk-asms)))      ; forall a1,a2 in ORD. phi a1 = phi a2 => a1 = a2
(define oni-typ (cadr (dk-asms)))      ; forall alpha in ORD. phi(alpha) in grd

;;; 1.  R is a set -- it separates the set grd.  No replacement here.
(have! `(IN ,oni-R SET) (lambda () (sep-set) (ass)))

;;; 2.  Every phi-value lies in R, witnessed by the ordinal it came from.
;;;
;;; The (IN (phi x) grd) landed by inst*! is doing DOUBLE duty: it is the domain
;;; half of the SEP membership, and it is the DEFINEDNESS witness `rfl' needs for
;;; (= (phi x) (phi x)).  `=' is partial -- t = t IS the definedness claim -- and
;;; phi is only a variable, so nothing here is defined syntactically;
;;; pi-reflexivity! accepts a context (IN t _) instead.
(have! oni-claim2
  (lambda ()
    (di)
    (inst*! oni-typ 'x)
    (in-sep! (lambda () (ass))                            ; phi(x) is in grd
             (lambda ()
               (witness! 'x (lambda ()                    ; ... and x is the b that gives it
                 (both! (lambda () (ass))                 ;     x is an ordinal
                        (lambda () (rfl)))))))))          ;     phi(x) = phi(x)

;;; 3.  INV inverts phi on the ordinals.  INV(x) is SOME ordinal with the same
;;; phi-value as x -- choice gives that much -- and injectivity says there is
;;; only one, namely x itself.
(have! oni-claim3
  (lambda ()
    (di)
    (inst*! oni-typ 'x)                                   ; again, for rfl below
    (choose! (oni-fibre 'x) 'x                            ; the fibre is inhabited: x is in it
             (lambda () (in-sep! (lambda () (ass)) (lambda () (rfl)))))
    ;; choose! has landed (IN INV(x) ORD) and (= (phi INV(x)) (phi x)).
    (inst*! oni-inj (oni-inv 'x) 'x)
    (ass)))

;;; 4.  Hence ORD sits inside the image of R under H: an ordinal x is H applied
;;; to the member phi(x).
(have! `(SUBSET ORD (IMAGE ,oni-H ,oni-R))
  (lambda ()
    (let ((x (subset-by-element!)))
      ;; H has domain grd, and it is applied at phi(x) below; oni-typ at x is
      ;; what says phi(x) IS in grd, so land it before the reduction rather
      ;; than reducing first and typing afterwards.
      (inst*! oni-typ x)
      (dk-image-goal!)
      (witness! `(phi ,x)
        (lambda ()
          (both! (lambda () (inst*! oni-claim2 x) (ass))          ; phi(x) is in R
                 (lambda () (lam-b)                              ; H(phi(x)) = INV(x)
                            (inst*! oni-claim3 x) (ass))))))))    ;         ... = x

;;; 5, 6, 7.  Replacement, then subclass-of-a-set, then Burali-Forti.
(dk-fact! 'image-set oni-H oni-R)
(dk-fact! 'subclass-of-set-is-set 'ORD `(IMAGE ,oni-H ,oni-R))
(ta 'burali-forti)
(ai '(NOT (IN ORD SET)))
(qed 'ord-no-injection-into-set)
(topic! 'ord-no-injection-into-set 'set-quotient)
