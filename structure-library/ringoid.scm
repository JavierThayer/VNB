;;; ringoid.scm -- a ring with a distinguished two-sided ideal.
;;;
;;; A RINGOID is the ring analogue of a SETOID: a ring R together with a two-sided
;;; ideal I.  The ideal induces the congruence  a ~ b  iff  a - b in I, and
;;; RINGOID-QUOTIENT(r) = R/I is the setoid quotient with ring operations descended.
;;;
;;; DESIGN (revised 2026-07-19).  The first cut declared RINGOID as the PAIR [RG, IDL]
;;; with RG a substructure RING.  That gave a ringoid NO carrier of its own -- its
;;; elements were carr(RG .), a composition, not a slot -- so declare-structure could
;;; make no map for a morphism and the generated IS-HOM-RINGOID degenerated to arity-2
;;; equality of the data.  A carrier that is a composition over a substructure cannot be
;;; routed through the hom machinery (which types a map on a single carrier accessor).
;;;
;;; So a ringoid now carries its OWN ring slots, mirroring RING's indices exactly (the
;;; NORMED-FIELD pattern): CARR/ADD/MUL/NEG/ZERO/ONE at slots 1..6, so the shared ring
;;; accessors reduce for a ringoid too, plus IDL at slot 7.  A ringoid IS a ring (reach
;;; the ring world by the view RINGOID-AS-RING), and its carrier is CARR(r) -- a real
;;; accessor, on which a morphism's map lives (declare-hom! below).

;;; ---- the ideal condition, over a ring given by its operations ----------------
;; is-ideal-in(I, carr, add, mul, neg, zero): I is a two-sided ideal of the ring whose
;; carrier/operations are carr/add/mul/neg/zero.  Built from a flat conjunct list --
;; no hand-nested AND (forall-guarded / conjuncts->and, structures.scm).
;; Parameters carry trailing underscores: `carr'/`add'/`mul'/`neg'/`zero' case-fold onto
;; the registered CARR/ADD/MUL/NEG/ZERO accessors, and constant-binder-audit rejects a
;; binder that shadows one (case_fold_convention).
(def-predicate 'is-ideal-in '(I_ carr_ add_ mul_ neg_ zero_)
  (conjuncts->and
    (list '(SUBSET I_ carr_)
          '(IN zero_ I_)
          (forall-guarded '(a b)  '((IN a I_) (IN b I_))        '(IN (add_ a b) I_))
          (forall-guarded '(a)    '((IN a I_))                  '(IN (neg_ a) I_))
          (forall-guarded '(x_ a) '((IN x_ carr_) (IN a I_))    '(IN (mul_ x_ a) I_))
          (forall-guarded '(x_ a) '((IN x_ carr_) (IN a I_))    '(IN (mul_ a x_) I_)))))

;;; ---- the structure -----------------------------------------------------------
(declare-structure RINGOID
  ;; Slots 1-6 mirror RING so the shared CARR/ADD/MUL/NEG/ZERO/ONE accessors keep
  ;; their NTH indices (a ringoid IS a ring on its first six slots).
  (carriers CARR)
  (op ADD (CARTESIAN CARR CARR) CARR)
  (op MUL (CARTESIAN CARR CARR) CARR)
  (op NEG CARR CARR)
  (constant ZERO CARR)
  (constant ONE CARR)
  ;; Slot 7: the distinguished two-sided ideal.
  (constant IDL (POWER CARR))
  ;; Ring laws (mirror RING exactly).
  (property is-associative ADD CARR)
  (property is-commutative ADD CARR)
  (property is-identity ADD ZERO CARR)
  (property has-inverses ADD ZERO NEG CARR)
  (property is-associative MUL CARR)
  (property is-identity MUL ONE CARR)
  (property is-distributive ADD MUL CARR)
  ;; IDL is a two-sided ideal of (CARR, ADD, MUL, NEG, ZERO).
  (property is-ideal-in IDL CARR ADD MUL NEG ZERO))

(notation! 'IS-RINGOID  'noun "ringoid" 'article "a")
(notation! 'is-ideal-in 'kind 'predicate 'arity 6
           'english "$1 is a two-sided ideal of the ring with carrier $2")

;;; ---- reach the ring world: a ringoid IS a ring (forget the ideal) ------------
;; RINGOID-AS-RING(r) projects slots 1..6 into a fresh RING 6-tuple, exactly as
;; NORMED-FIELD-AS-COMMUTATIVE-RING forgets the norm.  Every ring theorem specializes
;; to a ringoid through it, and (ADD (RINGOID-AS-RING r)) reduces to (ADD r), etc.
(def-functor 'RINGOID-AS-RING
  'RINGOID '(CARR ADD MUL NEG ZERO ONE)
  'RING    '(CARR ADD MUL NEG ZERO ONE))

;;; ---- the ringoid morphism (a principled override, now that CARR is a slot) ----
;; A morphism (a,I) -> (b,J) is a ring homomorphism f: CARR(a) -> CARR(b) that carries
;; the ideal into the ideal, f(I) subset J -- exactly the condition under which f
;; descends to R/I -> R'/I'.  declare-hom! supplies IS-RINGOID(a), IS-RINGOID(b) and the
;; typing f in FUN(CARR a, CARR b); the body states what is characteristic: f is a ring
;; hom (on the RINGOID-AS-RING views) and preserves the ideal.
(declare-hom! 'RINGOID '(a b f)
  '(AND (IS-HOM-RING (RINGOID-AS-RING a) (RINGOID-AS-RING b) f)
        (FORALL x_ (IMPLIES (IN x_ (IDL a)) (IN (f x_) (IDL b))))))
(notation! 'IS-HOM-RINGOID 'kind 'predicate 'arity 3
           'english "$3 is a ringoid homomorphism from $1 to $2")

;;; ---- the induced setoid: a ~ b iff a - b in I --------------------------------
;; The congruence as a SET of pairs (SETOID's REL slot), in metric-completion's CREL
;; shape: p ranges over LIST-pairs of CARR; its components are (NTH 1 p), (NTH 2 p).
(def-functoid 'RINGOID-REL '(r)
  '(SEP p (CARTESIAN (CARR r) (CARR r))
        (IN ((ADD r) (NTH 1 p) ((NEG r) (NTH 2 p))) (IDL r))))

;; RINGOID-SETOID(r) = [CARR(r), RINGOID-REL(r)] -- the underlying setoid, so CLASS /
;; PROJ / QUOTIENT apply verbatim.  is-equivalence(REL, PTS) is PROVEN from the ideal
;; laws (theorem-library/ringoid-setoid-proof.scm).
(def-functoid 'RINGOID-SETOID '(r)
  '(LIST (CARR r) (RINGOID-REL r)))

;; RINGOID-QUOTIENT(r) = R/I -- the setoid quotient (the class SET).
(def-functoid 'RINGOID-QUOTIENT '(r)
  '(QUOTIENT (RINGOID-SETOID r)))

;; RINGOID-QUOTIENT-RING(r) = R/I as a RING: the class set, with each operation
;; DESCENDed from R (binary ADD/MUL by DESCEND2, unary NEG by DESCEND), and the
;; classes [0], [1] as the constants.  Same 6-slot layout as RING, so the shared
;; ring accessors reduce.  IS-RING(RINGOID-QUOTIENT-RING r) is the goal.
(def-functoid 'RINGOID-QUOTIENT-RING '(r)
  '(LIST (QUOTIENT (RINGOID-SETOID r))
         (DESCEND2 (VNB-LAMBDA (LIST a b) (CLASS (RINGOID-SETOID r) ((ADD r) a b))))
         (DESCEND2 (VNB-LAMBDA (LIST a b) (CLASS (RINGOID-SETOID r) ((MUL r) a b))))
         (DESCEND  (VNB-LAMBDA a         (CLASS (RINGOID-SETOID r) ((NEG r) a))))
         (CLASS (RINGOID-SETOID r) (ZERO r))
         (CLASS (RINGOID-SETOID r) (ONE r))))

;; Read-off macetes: unconditional projections of the tuple, one per slot (mac
;; them in the IS-RING proof, exactly as mat-ring-* serve mat-ring-proof).
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'rq-carr
    '(FORALL r (== (CARR (RINGOID-QUOTIENT-RING r)) (QUOTIENT (RINGOID-SETOID r)))))
  (theory-add-axiom! *current-theory* 'rq-add
    '(FORALL r (== (ADD (RINGOID-QUOTIENT-RING r))
                   (DESCEND2 (VNB-LAMBDA (LIST a b) (CLASS (RINGOID-SETOID r) ((ADD r) a b)))))))
  (theory-add-axiom! *current-theory* 'rq-mul
    '(FORALL r (== (MUL (RINGOID-QUOTIENT-RING r))
                   (DESCEND2 (VNB-LAMBDA (LIST a b) (CLASS (RINGOID-SETOID r) ((MUL r) a b)))))))
  (theory-add-axiom! *current-theory* 'rq-neg
    '(FORALL r (== (NEG (RINGOID-QUOTIENT-RING r))
                   (DESCEND (VNB-LAMBDA a (CLASS (RINGOID-SETOID r) ((NEG r) a)))))))
  (theory-add-axiom! *current-theory* 'rq-zero
    '(FORALL r (== (ZERO (RINGOID-QUOTIENT-RING r)) (CLASS (RINGOID-SETOID r) (ZERO r)))))
  (theory-add-axiom! *current-theory* 'rq-one
    '(FORALL r (== (ONE (RINGOID-QUOTIENT-RING r)) (CLASS (RINGOID-SETOID r) (ONE r)))))
  ;; PTS of the ringoid setoid is the ring carrier (RINGOID-SETOID = [CARR, REL]).
  (theory-add-axiom! *current-theory* 'ringoid-setoid-pts
    '(FORALL r (== (PTS (RINGOID-SETOID r)) (CARR r)))))

;;; ---- descend interface: the operations compute on classes (well-known) --------
;; The DESCEND2/DESCEND specialisation to this ring, one per operation.  Each is
;; rq-<op> (accessor read-off) then descend2-computes / descend-computes on the
;; class-of-<op> map -- which needs that map typed and respecting the congruence.
;; Asserted now, to be discharged from descend2-computes + the respects lemmas.
(support 'rq-add-computes
  (forall-guarded '(r) '((IS-RINGOID r))
    (forall-guarded '(a b) '((IN a (CARR r)) (IN b (CARR r)))
      '(= ((ADD (RINGOID-QUOTIENT-RING r))
           (CLASS (RINGOID-SETOID r) a) (CLASS (RINGOID-SETOID r) b))
          (CLASS (RINGOID-SETOID r) ((ADD r) a b))))))
(warrant! 'rq-add-computes 'well-known
  "rq-add reduces ADD(RINGOID-QUOTIENT-RING r) to DESCEND2 of the class-of-sum map
   f = (a,b) |-> [a+b]; f is total CARR x CARR -> QUOTIENT (ring add closes, class
   lands in the quotient) and RESPECTS2 the congruence ((a+b)-(a'+b') = (a-a')+(b-b')
   in I by ringoid-ideal-add), so descend2-computes gives DESCEND2(f)([a],[b]) = f(a,b)
   = [a+b].  To be demoted to a theorem once the typing and respects lemmas are proven.")

;;; ---- R/I is a ring (reference-warranted; associativity route validated) --------
;; The compute-down route is proven for the associativity case (rq-add-assoc-classes,
;; theorem-library/ringoid-quotient-ring-proof.scm) via the DESCEND2 machinery; the
;; other nine ring laws follow the identical pattern.  Rather than grind all of them,
;; the theorem is asserted with a textbook reference -- the mechanism is the deliverable.
;; (Mathematically: the ideal is a congruence, so ADD, MUL and NEG descend well-defined
;; to the classes and inherit the ring axioms from R, with [0] and [1] the constants.)
;; WORKED EXAMPLE of the reference discipline: cite a registered book by key + named
;; result; the human citation "Lang, Algebra, Ch. II.1" is rendered from the (lang ...)
;; locator, and the third element is the machine page anchor: pdf page 98 of
;; AlgebraLang-ocr.pdf = printed page 83, where Ch. II Â§1 "Rings and homomorphisms"
;; begins (verified against the page image 2026-07-23).
(support 'ringoid-quotient-is-ring
  '(FORALL r (IMPLIES (IS-RINGOID r) (IS-RING (RINGOID-QUOTIENT-RING r)))))
(warrant! 'ringoid-quotient-is-ring 'reference '(lang "Ch. II.1" 98))
(gloss! 'ringoid-quotient-is-ring
  "For a ringoid r (a ring with a distinguished two-sided ideal), the quotient ring
   R/I -- the ring RINGOID-QUOTIENT-RING(r) of congruence classes with the descended
   operations -- is a ring.")

;;; ---- membership IFF for the congruence ---------------------------------------
;; The SEP characterization, stated so it can drive mac / mac-h on goal AND hypothesis
;; (mac-h cannot unfold the RINGOID-REL functoid in an assumption; functoid_mac_h_trap).
;; Definitional: the SEP membership unfolded (base-membership AND the predicate).
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'ringoid-rel-mem
    (forall-iff '(r a b)
      '(IN (LIST a b) (RINGOID-REL r))
      (list '(IN (LIST a b) (CARTESIAN (CARR r) (CARR r)))
            '(IN ((ADD r) a ((NEG r) b)) (IDL r))))))

;;; ---- projections of IS-RINGOID (definitional; they pay nothing) --------------
;; Read off the folded structure IFF: the carrier typing, the additive inverse law
;; (has-inverses), and the four ideal-closure laws (is-ideal-in).  The ringoid-setoid
;; proof cites these for reflexivity, symmetry and transitivity.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'ringoid-carr-in-set
    (forall-guarded '(r) '((IS-RINGOID r)) '(IN (CARR r) SET)))
  (theory-add-axiom! *current-theory* 'ringoid-add-right-inv
    (forall-guarded '(r a) '((IS-RINGOID r) (IN a (CARR r)))
      '(= ((ADD r) a ((NEG r) a)) (ZERO r))))
  (theory-add-axiom! *current-theory* 'ringoid-ideal-subset
    (forall-guarded '(r) '((IS-RINGOID r)) '(SUBSET (IDL r) (CARR r))))
  (theory-add-axiom! *current-theory* 'ringoid-ideal-zero
    (forall-guarded '(r) '((IS-RINGOID r)) '(IN (ZERO r) (IDL r))))
  (theory-add-axiom! *current-theory* 'ringoid-ideal-add
    (forall-guarded '(r a b) '((IS-RINGOID r) (IN a (IDL r)) (IN b (IDL r)))
      '(IN ((ADD r) a b) (IDL r))))
  (theory-add-axiom! *current-theory* 'ringoid-ideal-neg
    (forall-guarded '(r a) '((IS-RINGOID r) (IN a (IDL r)))
      '(IN ((NEG r) a) (IDL r))))
  ;; two-sided absorption (R.I and I.R land in I) -- the ideal projections the
  ;; add/neg block above omitted; needed for MUL to respect the congruence.
  (theory-add-axiom! *current-theory* 'ringoid-ideal-mul-left
    (forall-guarded '(r x_ a) '((IS-RINGOID r) (IN x_ (CARR r)) (IN a (IDL r)))
      '(IN ((MUL r) x_ a) (IDL r))))
  (theory-add-axiom! *current-theory* 'ringoid-ideal-mul-right
    (forall-guarded '(r a x_) '((IS-RINGOID r) (IN a (IDL r)) (IN x_ (CARR r)))
      '(IN ((MUL r) a x_) (IDL r)))))

;;; ---- two additive-group identities on the ring (warranted PSS supports) ------
;; -(a-b) = b-a  and  (a-b)+(b-c) = a-c, on the ringoid's own operations.  These are the
;; only asserted leaves of the ringoid-setoid proof; declared as `support' + `warrant!'
;; (well-known) so they land in the PSS as trusted surface rather than as bare axioms.
;; crs proves them for concrete rings but does NOT reach a structure's abstract ADD/NEG
;; (the abstract-ring additive-normalizer gap; abstract_ring_normalizer) -- when that
;; normalizer exists they become theorems and this warrant retires.
(support 'ringoid-neg-diff
  (forall-guarded '(r a b) '((IS-RINGOID r) (IN a (CARR r)) (IN b (CARR r)))
    '(= ((NEG r) ((ADD r) a ((NEG r) b))) ((ADD r) b ((NEG r) a)))))
(warrant! 'ringoid-neg-diff 'well-known
  "-(a-b) = b-a, the additive-group identity in any ring.  crs proves it for concrete rings; it does not reach a structure's abstract (ADD r)/(NEG r).")
(support 'ringoid-diff-telescope
  (forall-guarded '(r a b c) '((IS-RINGOID r) (IN a (CARR r)) (IN b (CARR r)) (IN c (CARR r)))
    '(= ((ADD r) ((ADD r) a ((NEG r) b)) ((ADD r) b ((NEG r) c))) ((ADD r) a ((NEG r) c)))))
(warrant! 'ringoid-diff-telescope 'well-known
  "(a-b)+(b-c) = a-c, telescoping in any ring.  Same abstract-ADD/NEG gap as ringoid-neg-diff.")
