;;; theorem-library/rake-rr-pos-star.scm -- the six CARRIER facts of
;;; RR-POS-STAR = [0, +inf], proven.  Rake batch 5c-K.
;;;
;;; All six were `theory-add-axiom!' forms in structure-library/extended-reals-pos.scm,
;;; warranted `well-known' on 2026-09-18 with the text "one case split off the
;;; membership iff rr-pos-star-membership plus the RR-STAR axioms.  Provable; not
;;; yet proven."  That warrant was an accurate plan; this file runs it.
;;;
;;;   zero-in-rr-pos-star          (IN 0 RR-POS-STAR)
;;;   pos-inf-in-rr-pos-star       (IN POS-INF RR-POS-STAR)
;;;   neg-inf-not-in-rr-pos-star   (NOT (IN NEG-INF RR-POS-STAR))
;;;   rr-pos-star-nonneg           x in RR-POS-STAR => 0 <= x
;;;   rr-pos-star-subset-rr-star   SUBSET RR-POS-STAR RR-STAR
;;;   rr-pos-star-below-pos-inf    x in RR-POS-STAR => x <= POS-INF
;;;
;;; THE ROUTE, for all six.  `rr-pos-star-membership' (extended-reals-pos.scm,
;;; stamped definitional) says
;;;     x in RR-POS-STAR  iff  (x in RR and 0 <= x)  or  x = POS-INF,
;;; so each fact is one case split.  The REAL case is closed by the RR axioms of
;;; number-systems.scm (rr-zero-in, rr-leq-reflexive) or by the split conjunct
;;; itself; the POS-INF case by the RR-STAR axioms of extended-reals.scm
;;; (rr-star-membership, pos-inf-in-rr-star, pos-inf-upper-bound,
;;; pos-inf-neq-neg-inf, neg-inf-not-in-rr).  Nothing here needs
;;; `pos-inf-above-reals' -- that axiom is what the ORDER theory of RR-POS-STAR
;;; needs (theorem-library/rake-extended-order.scm), not the carrier.
;;;
;;; THE BILLS, and the three leaves on them are a FINDING rather than a failure:
;;;     zero-in-rr-pos-star          modulo 0
;;;     pos-inf-in-rr-pos-star       modulo 0
;;;     rr-pos-star-subset-rr-star   modulo 0
;;;     rr-pos-star-nonneg           modulo {pos-inf-upper-bound}          trust: none
;;;     rr-pos-star-below-pos-inf    modulo {pos-inf-upper-bound}          trust: none
;;;     neg-inf-not-in-rr-pos-star   modulo {neg-inf-not-in-rr,
;;;                                          pos-inf-neq-neg-inf}          trust: none
;;; Those three are axioms of structure-library/extended-reals.scm installed as
;;; bare `theory-add-axiom!' forms with NO warrant, so any bill naming one reads
;;; `trust: none':
;;;     pos-inf-upper-bound     extended-reals.scm:73
;;;     pos-inf-neq-neg-inf     extended-reals.scm:56
;;;     neg-inf-not-in-rr       extended-reals.scm:62
;;; extended-reals.scm's own comment at :92 says so ("The sibling axioms of this
;;; file ... are NOT stamped: they were installed `asserted' with no warrant and
;;; no decision has been taken about them").  They are of the same species as the
;;; carrier facts proven here -- statements of what the symbols MEAN -- and their
;;; provenance is the user's decision, not this file's.  Each of the three is
;;; irreducible for its leaf: pos-inf-upper-bound is the only statement in the
;;; tree that puts ANYTHING below POS-INF, and the two distinctness axioms ARE
;;; the content of "NEG-INF is not in [0,+inf]".
;;;
;;; Two axioms of that file are NOT on any bill here, and deliberately:
;;; `rr-star-membership' (:30) is stamped `definitional'
;;; (structure-library/definitional-reclass.scm:29), so (IN t RR-STAR) is taken
;;; off the membership iff at a cost of nothing; and `pos-inf-in-rr-star' (:43),
;;; which the obvious route cites twice, is then never needed.  Citing it cost
;;; two of these six bills their `modulo 0' on the first probe.
;;;
;;; LOAD WINDOW [142, 234).  The latest MATHEMATICAL
;;; citation is structure-library/extended-reals-pos (76, rr-pos-star-membership);
;;; the others are number-systems (34), structure-library/extended-reals (75),
;;; theorem-library/axioms (15, equality-symmetry) and the base theory
;;; (subset-def).  What forces lo = 142 is the TACTICS: `prop' is position 141,
;;; and `interactive' 134, `driver-kit' 138 are below it.  (The provenance stamp
;;; on rr-star-membership is applied by structure-library/definitional-reclass,
;;; 104, so it is in place here; a slot below 104 would bill it.)  hi = 234 is
;;; theorem-library/rake-extended-order, which `fact's zero-in-rr-pos-star and
;;; rr-pos-star-below-pos-inf, and it is the ONLY proven citer of any of the six:
;;; theorem-library/rake-measure2 (198) uses the membership iff
;;; `rr-pos-star-membership' directly (its r6f-in-rr-pos-star! lane) and names
;;; none of these.  structure-library/extended-arith.scm:87 mentions
;;; zero-in-rr-pos-star in a COMMENT only.
;;;
;;; Helper prefix: r7k-.

;;; ---------------------------------------------------------------------------
;;; The case split every proof in this file opens with.  `fact' lands the
;;; membership instance; the context is weakened to it plus the typing before
;;; `prop', because prop's atom cap drops the pair it needs in a deep context
;;; and then reports "not propositional" (CLAUDE.md).

(define (r7k-real-case tm) (list 'AND (list 'IN tm 'RR) (list '<= 0 tm)))
(define (r7k-inf-case  tm) (list '= tm 'POS-INF))

(define (r7k-star-cases! tm real-body inf-body)
  (have! (list 'OR (r7k-real-case tm) (r7k-inf-case tm))
         (lambda ()
           (let ((inst (dk-fact! 'rr-pos-star-membership tm)))
             (dk-only! inst (list 'IN tm 'RR-POS-STAR))
             (prop))))
  (use-cases (list (r7k-real-case tm) (r7k-inf-case tm)) real-body inf-body))

;;; (IN TM RR-STAR) out of `rr-star-membership' -- which is stamped
;;; `definitional' (structure-library/definitional-reclass.scm:29, load position
;;; 104, so the stamp is in place long before this file) and therefore contributes
;;; NOTHING to a bill.  KEEPER is the disjunct that holds: (IN TM RR) for a real,
;;; (= POS-INF POS-INF) at the top.  Going this way rather than through the
;;; UNWARRANTED `pos-inf-in-rr-star' is what keeps two of these six bills clean.
;;;
;;; The `-close!' form is for a leaf whose goal IS (IN TM RR-STAR): a `have!' of
;;; the focus goal is an alpha self-loop with no main branch (CLAUDE.md).  The
;;; `-have!' form is the lane, for when the caller still needs its context.
(define (r7k-close-in-rr-star! tm keeper)
  (let ((inst (dk-fact! 'rr-star-membership tm)))
    (dk-only! inst keeper)
    (prop)))

(define (r7k-have-in-rr-star! tm keeper)
  (have! (list 'IN tm 'RR-STAR)
         (lambda () (r7k-close-in-rr-star! tm keeper))))

;;; (= POS-INF POS-INF): POS-INF is an atomic constant, so `pi--defined?'
;;; certifies it with no typing (primitive-inferences.scm:993) and `rfl' fires.
(define (r7k-pos-inf-refl!)
  (have! '(= POS-INF POS-INF) (lambda () (rfl))))

;;; ---------------------------------------------------------------------------
;;; zero-in-rr-pos-star -- copied literally from extended-reals-pos.scm:50.
;;; 0 is a real and 0 <= 0, so the left disjunct of the membership iff holds.

(sp (make-wff '(IN 0 RR-POS-STAR)))
(fact 'rr-zero-in)                      ; (IN 0 RR)
(fact 'rr-leq-reflexive 0)              ; (<= 0 0), detached off (IN 0 RR)
(let ((inst (dk-fact! 'rr-pos-star-membership 0)))
  (dk-only! inst '(IN 0 RR) '(<= 0 0))
  (prop))
(qed 'zero-in-rr-pos-star)
(topic! 'zero-in-rr-pos-star 'analysis)

;;; ---------------------------------------------------------------------------
;;; pos-inf-in-rr-pos-star -- copied literally from extended-reals-pos.scm:53.
;;; The right disjunct, (= POS-INF POS-INF).  No typing of POS-INF is cited and
;;; none is needed: POS-INF is an atomic constant, and `pi--defined?'
;;; (primitive-inferences.scm:993) certifies every non-compound term, so neither
;;; the instantiation of the membership iff at POS-INF nor the `rfl' owes a side
;;; leaf.  Citing `pos-inf-in-rr-star' here would have put an unwarranted axiom
;;; on this bill for nothing.

(sp (make-wff '(IN POS-INF RR-POS-STAR)))
(r7k-pos-inf-refl!)
(let ((inst (dk-fact! 'rr-pos-star-membership 'POS-INF)))
  (dk-only! inst '(= POS-INF POS-INF))
  (prop))
(qed 'pos-inf-in-rr-pos-star)
(topic! 'pos-inf-in-rr-pos-star 'analysis)

;;; ---------------------------------------------------------------------------
;;; neg-inf-not-in-rr-pos-star -- copied literally from extended-reals-pos.scm:57.
;;; Assume the membership; both cases contradict an axiom of extended-reals.scm.
;;; The equality case needs `equality-symmetry', the axiom being stated as
;;; (NOT (= POS-INF NEG-INF)) and the case giving (= NEG-INF POS-INF).

(sp (make-wff '(NOT (IN NEG-INF RR-POS-STAR))))
(di)                                    ; assume the membership; goal FALSITY
(r7k-star-cases! 'NEG-INF
  (lambda ()
    (dk-split! (r7k-real-case 'NEG-INF))
    (fact 'neg-inf-not-in-rr)
    (ai '(NOT (IN NEG-INF RR))))
  (lambda ()
    (fact 'equality-symmetry 'NEG-INF 'POS-INF)
    (fact 'pos-inf-neq-neg-inf)
    (ai '(NOT (= POS-INF NEG-INF)))))
(qed 'neg-inf-not-in-rr-pos-star)
(topic! 'neg-inf-not-in-rr-pos-star 'analysis)

;;; ---------------------------------------------------------------------------
;;; rr-pos-star-nonneg -- copied literally from extended-reals-pos.scm:64.
;;; The real case carries 0 <= x as its own second conjunct.  At POS-INF the
;;; claim is 0 <= POS-INF, which is `pos-inf-upper-bound' at 0 once 0 is known
;;; to be in RR-STAR.

(sp (make-wff '(FORALL x (IMPLIES (IN x RR-POS-STAR) (<= 0 x)))))
(dk-peel!)
(r7k-star-cases! 'x
  (lambda ()
    (dk-split! (r7k-real-case 'x))
    (ass))
  (lambda ()
    (subst '(= x POS-INF))
    (fact 'rr-zero-in)
    (r7k-have-in-rr-star! 0 '(IN 0 RR))
    (fact 'pos-inf-upper-bound 0)
    (ass)))
(qed 'rr-pos-star-nonneg)
(topic! 'rr-pos-star-nonneg 'analysis)

;;; ---------------------------------------------------------------------------
;;; rr-pos-star-below-pos-inf -- copied literally from extended-reals-pos.scm:68.
;;; Both cases land (IN x RR-STAR) off the membership iff and then cite
;;; `pos-inf-upper-bound', which is the ONLY statement in the tree that puts
;;; anything below POS-INF and so cannot be kept off this bill.

(sp (make-wff '(FORALL x (IMPLIES (IN x RR-POS-STAR) (<= x POS-INF)))))
(dk-peel!)
(r7k-star-cases! 'x
  (lambda ()
    (dk-split! (r7k-real-case 'x))
    (r7k-have-in-rr-star! 'x '(IN x RR))
    (fact 'pos-inf-upper-bound 'x)
    (ass))
  (lambda ()
    (subst '(= x POS-INF))
    (r7k-pos-inf-refl!)
    (r7k-have-in-rr-star! 'POS-INF '(= POS-INF POS-INF))
    (fact 'pos-inf-upper-bound 'POS-INF)
    (ass)))
(qed 'rr-pos-star-below-pos-inf)
(topic! 'rr-pos-star-below-pos-inf 'analysis)

;;; ---------------------------------------------------------------------------
;;; rr-pos-star-subset-rr-star -- copied literally from extended-reals-pos.scm:46.
;;; `mac subset-def' turns the goal into the elementwise implication; then the
;;; same case split, with `rr-star-membership' closing the real case and
;;; `pos-inf-in-rr-star' the other.  The real case may NOT use
;;; `r7k-have-in-rr-star!' here: (IN x RR-STAR) IS the focus goal, and a `have!'
;;; of the goal is an alpha self-loop with no main branch (CLAUDE.md).

(sp (make-wff '(SUBSET RR-POS-STAR RR-STAR)))
(mac 'subset-def)
(dk-peel!)
(r7k-star-cases! 'x
  (lambda ()
    (dk-split! (r7k-real-case 'x))
    (r7k-close-in-rr-star! 'x '(IN x RR)))
  (lambda ()
    (subst '(= x POS-INF))
    (r7k-pos-inf-refl!)
    (r7k-close-in-rr-star! 'POS-INF '(= POS-INF POS-INF))))
(qed 'rr-pos-star-subset-rr-star)
(topic! 'rr-pos-star-subset-rr-star 'analysis)
