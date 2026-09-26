;;; theorem-library/rake-infinity-points.scm -- the five DERIVABLE axioms of
;;; structure-library/extended-reals.scm, proven.  Rake "infinity points".
;;;
;;; The file extended-reals.scm installs eight facts about the two points at
;;; infinity.  On 2026-09-18 the user stamped THREE of them `primitive'
;;; (neg-inf-not-in-rr, pos-inf-upper-bound, neg-inf-lower-bound), beside the
;;; earlier `pos-inf-above-reals'; the other five were left warranted
;;; `well-known' with the note "Derivable ...; the derivation is
;;; theorem-library/rake-infinity-points.scm".  This file runs that derivation.
;;;
;;;   rr-subset-rr-star     (SUBSET RR RR-STAR)         extended-reals.scm:41
;;;   pos-inf-in-rr-star    (IN POS-INF RR-STAR)        extended-reals.scm:45
;;;   neg-inf-in-rr-star    (IN NEG-INF RR-STAR)        extended-reals.scm:48
;;;   pos-inf-neq-neg-inf   (NOT (= POS-INF NEG-INF))   extended-reals.scm:56
;;;   pos-inf-not-in-rr     (NOT (IN POS-INF RR))       extended-reals.scm:59
;;;
;;; THE ROUTES.
;;; The first three are one disjunct of `rr-star-membership' (extended-reals.scm:30,
;;; stamped `definitional' by structure-library/definitional-reclass.scm:29, so it
;;; contributes {} to every bill):
;;;     x in RR-STAR  iff  x in RR  or  (x = POS-INF  or  x = NEG-INF).
;;; For the SUBSET goal `mac subset-def' turns it into the elementwise
;;; implication first; at the two infinities the disjunct is the reflexive
;;; equation, and POS-INF / NEG-INF are atomic constants, so `pi--defined?'
;;; certifies them with no typing and `rfl' fires (primitive-inferences.scm).
;;;
;;; pos-inf-not-in-rr: assume (IN POS-INF RR).  `pos-inf-above-reals'
;;; (extended-reals.scm, PRIMITIVE) at x := POS-INF then gives
;;; NOT (POS-INF <= POS-INF), while `rr-leq-reflexive' (number-systems.scm,
;;; primitive) at the same term gives POS-INF <= POS-INF.  Both instantiations
;;; are licensed by the assumption itself.
;;;
;;; pos-inf-neq-neg-inf: assume POS-INF = NEG-INF.  0 is a real, hence in
;;; RR-STAR, so `neg-inf-lower-bound' (PRIMITIVE) gives NEG-INF <= 0 and
;;; `pos-inf-above-reals' gives NOT (POS-INF <= 0).  `subst' rewrites LEFT TO
;;; RIGHT only, so the equation is used in a `have!' LANE whose GOAL is
;;; POS-INF <= 0: there the rewrite POS-INF -> NEG-INF turns the goal into the
;;; hypothesis NEG-INF <= 0.  (There is no hypothesis-side `subst'.)
;;;
;;; NO CIRCULARITY.  Nothing here cites any of the five, nor anything proven
;;; from them: theorem-library/rake-rr-pos-star, rake-extended-order,
;;; rake-eplus-defined, rake-etimes-defined, rake-measure*, rake-series are all
;;; downstream and none is named.  The only infinity facts cited are
;;; `rr-star-membership' (definitional), `pos-inf-above-reals' and
;;; `neg-inf-lower-bound' (both primitive since 2026-09-18).
;;;
;;; LOAD WINDOW [142, 191).  lo = 142 is forced by the TACTICS, not by the
;;; mathematics: `prop' is load position 141 (interactive 134, driver-kit 138,
;;; proof-debt 139 below it).  The mathematical citations are all far lower --
;;; number-systems 34 (rr-zero-in, rr-leq-reflexive), the base theory
;;; (subset-def), structure-library/extended-reals 75, and the provenance stamp
;;; on rr-star-membership is applied by structure-library/definitional-reclass
;;; 104.  hi = 191 is theorem-library/rake-rr-pos-star, the earliest proof that
;;; cites any of the five.
;;;
;;; Helper prefix: r7i-.

;;; ---------------------------------------------------------------------------
;;; Shared machinery.  `rr-star-membership' at TM, weakened to the surviving
;;; disjunct KEEPER, then `prop'.  The context is cut down before `prop' because
;;; `fact' lands its whole instantiation chain and prop's atom cap (12) drops
;;; the pair it needs in a deep context (CLAUDE.md).
;;;
;;; The `-close!' form is for a leaf whose goal IS (IN TM RR-STAR); a `have!' of
;;; the focus goal is an alpha self-loop with no main branch.  The `-have!' form
;;; is the lane, for a caller that goes on using its context.

(define (r7i-close-in-rr-star! tm keeper)
  (let ((inst (dk-fact! 'rr-star-membership tm)))
    (dk-only! inst keeper)
    (prop)))

(define (r7i-have-in-rr-star! tm keeper)
  (have! (list 'IN tm 'RR-STAR)
         (lambda () (r7i-close-in-rr-star! tm keeper))))

;;; (= C C) for an atomic constant C: `pi--defined?' certifies it with no
;;; typing, so `rfl' fires unaided.
(define (r7i-refl! c)
  (have! (list '= c c) (lambda () (rfl))))

;;; ---------------------------------------------------------------------------
;;; rr-subset-rr-star -- copied literally from extended-reals.scm:41.
;;; `mac subset-def' gives the elementwise implication; the peeled typing
;;; (IN x RR) IS the left disjunct of the membership iff.

(sp (make-wff '(SUBSET RR RR-STAR)))
(mac 'subset-def)
;;; The eigenvariable is read off the LANDED typing, never guessed: `di'
;;; renames when the name is taken.
(let ((r7i-typing (car (dk-peel!))))
  (r7i-close-in-rr-star! (cadr r7i-typing) r7i-typing))
(qed 'rr-subset-rr-star)
(topic! 'rr-subset-rr-star 'analysis)

;;; ---------------------------------------------------------------------------
;;; pos-inf-in-rr-star -- copied literally from extended-reals.scm:45.
;;; The middle disjunct, (= POS-INF POS-INF).

(sp (make-wff '(IN POS-INF RR-STAR)))
(r7i-refl! 'POS-INF)
(r7i-close-in-rr-star! 'POS-INF '(= POS-INF POS-INF))
(qed 'pos-inf-in-rr-star)
(topic! 'pos-inf-in-rr-star 'analysis)

;;; ---------------------------------------------------------------------------
;;; neg-inf-in-rr-star -- copied literally from extended-reals.scm:48.
;;; The right disjunct, (= NEG-INF NEG-INF).

(sp (make-wff '(IN NEG-INF RR-STAR)))
(r7i-refl! 'NEG-INF)
(r7i-close-in-rr-star! 'NEG-INF '(= NEG-INF NEG-INF))
(qed 'neg-inf-in-rr-star)
(topic! 'neg-inf-in-rr-star 'analysis)

;;; ---------------------------------------------------------------------------
;;; pos-inf-not-in-rr -- copied literally from extended-reals.scm:59.
;;; `di' assumes (IN POS-INF RR) and leaves FALSITY; the assumption licenses
;;; both citations at POS-INF and they contradict each other.

(sp (make-wff '(NOT (IN POS-INF RR))))
(di)
(fact 'pos-inf-above-reals 'POS-INF)    ; (NOT (<= POS-INF POS-INF))
(fact 'rr-leq-reflexive 'POS-INF)       ; (<= POS-INF POS-INF)
(ai '(NOT (<= POS-INF POS-INF)))
(qed 'pos-inf-not-in-rr)
(topic! 'pos-inf-not-in-rr 'analysis)

;;; ---------------------------------------------------------------------------
;;; pos-inf-neq-neg-inf -- copied literally from extended-reals.scm:56.
;;; `di' assumes the equation and leaves FALSITY.  0 is in RR, hence in RR-STAR
;;; by the left disjunct, so NEG-INF <= 0 and NOT (POS-INF <= 0).  The `have!'
;;; lane is where the equation is usable: its GOAL is POS-INF <= 0 and `subst'
;;; rewrites POS-INF -> NEG-INF there.

(sp (make-wff '(NOT (= POS-INF NEG-INF))))
(di)
(fact 'rr-zero-in)                      ; (IN 0 RR)
(r7i-have-in-rr-star! 0 '(IN 0 RR))     ; (IN 0 RR-STAR)
(fact 'neg-inf-lower-bound 0)           ; (<= NEG-INF 0)
(fact 'pos-inf-above-reals 0)           ; (NOT (<= POS-INF 0))
(have! '(<= POS-INF 0)
       (lambda ()
         (subst '(= POS-INF NEG-INF))
         (ass)))
(ai '(NOT (<= POS-INF 0)))
(qed 'pos-inf-neq-neg-inf)
(topic! 'pos-inf-neq-neg-inf 'analysis)
