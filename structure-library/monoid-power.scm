;;; RETIRED 2026-09-17 (proven): mpow-type -- was an unwarranted axiom; theorem-library/rake-algebra2.scm
;;; (mpow-type-ind, exponent outermost, then one fact).
;;; monoid-power.scm -- MPOW: the natural-number power x^n in a monoid.
;;;
;;; MPOW(m, x, n) = x * x * ... * x   (n factors, MUL of m), with MPOW(m,x,0)=IDEN(m).
;;; Needs ONLY a monoid -- commutative or not.  Written multiplicatively here;
;;; under the additive view of an abelian group the very same operation is the
;;; n-fold sum  n.a  (see zz-action.scm, which extends it to a ZZ action).
;;;
;;; The homomorphism law  x^(j+k) = x^j * x^k  (mpow-add) holds in ANY monoid:
;;; it just says  n |-> x^n  is a monoid hom  (NN,+,0) -> (A,*,E).  Commutativity
;;; is required only for the cross law  (x*y)^n = x^n * y^n  (mpow-mult), which is
;;; therefore stated over COMM-MONOID.
;;;
;;; Asserted laws carry an `informal' warrant: each is a routine NN induction
;;; from the two defining equations plus the monoid laws -- a paper-proof
;;; SKETCH lives in each warrant string, NOT a machine-checked VNB proof (that
;;; would rate `proof', the top trust tier).  Installed directly during the
;;; library-build phase (see sequences.scm for the same pattern).
;;;
;;; Dependencies: monoid.scm (IS-MONOID, IS-COMM-MONOID, MUL, E),
;;; number-systems.scm (NN, succ, +).

;;; Defining recursion (installs mpow-zero and mpow-succ):
;;;   MPOW(m, x, 0)       = IDEN(m)
;;;   MPOW(m, x, succ(n)) = (OPR m)(x, MPOW(m, x, n))
(def-by-nn-recursion 'MPOW '(m x)
  '(IDEN m)                               ; base value
  '(n val)                             ; step vars
  '((OPR m) x val))                    ; MPOW(m,x,succ n) = x * MPOW(m,x,n)

;;; Singleton: MPOW(m, x, 1) = x.
;;; From mpow-succ at n=0, mpow-zero, and the right-identity law.
;;; mpow-one RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-zz-act.scm

;;; Type: the power stays in the carrier.
;;; NN induction: base mpow-zero + (IDEN m) in CARR(m); step mpow-succ + carrier
;;; closure of MUL.

;;; Homomorphism law (no commutativity):  x^(j+k) = x^j * x^k.
;;; This is the defining property the user asked for.  NN induction on k:
;;; base k=0 uses mpow-zero + right identity; step uses mpow-succ + associativity.
;;; mpow-add RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-zz-act.scm

;;; Cross law (commutativity required):  (x*y)^n = x^n * y^n.
;;; Holds in a COMMUTATIVE monoid only.  NN induction on n, reordering factors
;;; by commutativity at each step.
;;; mpow-mult RAKE-ASM-2 2026-10-12: PROVEN in theorem-library/rake-asm-2.scm under this name; the assumption is retired.

;;; Retroactive transport.  ABELIAN-GROUP-AS-MONOID is declared in views.scm,
;;; which loads BEFORE this file, so its one-shot auto-specialization ran when
;;; the MPOW theorems above did not yet exist.  view-as-auto-specialize! is
;;; idempotent (it skips names already installed), so re-running it here -- now
;;; that mpow-one/type/add (and the comm-monoid mpow-mult) are in the theorem
;;; table -- finally lowers them onto ABELIAN-GROUP (and, by view composition,
;;; onto the additive group of every ring/field/integral-domain/normed-field).
(view-as-auto-specialize! 'ABELIAN-GROUP-AS-MONOID)
