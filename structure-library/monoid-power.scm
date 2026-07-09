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
;;;   MPOW(m, x, succ(n)) = (MUL m)(x, MPOW(m, x, n))
(def-by-nn-recursion 'MPOW '(m x)
  '(IDEN m)                               ; base value
  '(n val)                             ; step vars
  '((MUL m) x val))                    ; MPOW(m,x,succ n) = x * MPOW(m,x,n)

;;; Singleton: MPOW(m, x, 1) = x.
;;; From mpow-succ at n=0, mpow-zero, and the right-identity law.
(theory-add-axiom! *current-theory* 'mpow-one
  '(FORALL m
     (IMPLIES (IS-MONOID m)
       (FORALL x (IMPLIES (IN x (CARR m))
         (= (MPOW m x 1) x))))))
(warrant! 'mpow-one 'informal
  "MPOW(m,x,1)=MUL(x,MPOW(m,x,0))=MUL(x,IDEN(m))=x by mpow-succ(0), mpow-zero, right identity.")

;;; Type: the power stays in the carrier.
;;; NN induction: base mpow-zero + (IDEN m) in CARR(m); step mpow-succ + carrier
;;; closure of MUL.
(theory-add-axiom! *current-theory* 'mpow-type
  '(FORALL m
     (IMPLIES (IS-MONOID m)
       (FORALL x (IMPLIES (IN x (CARR m))
         (FORALL n (IMPLIES (IN n NN)
           (IN (MPOW m x n) (CARR m)))))))))
(warrant! 'mpow-type 'informal
  "NN induction on n: base (IDEN m) in CARR(m); step closes under MUL by mpow-succ.")

;;; Homomorphism law (no commutativity):  x^(j+k) = x^j * x^k.
;;; This is the defining property the user asked for.  NN induction on k:
;;; base k=0 uses mpow-zero + right identity; step uses mpow-succ + associativity.
(theory-add-axiom! *current-theory* 'mpow-add
  '(FORALL m
     (IMPLIES (IS-MONOID m)
       (FORALL x (IMPLIES (IN x (CARR m))
         (FORALL j (IMPLIES (IN j NN)
           (FORALL k (IMPLIES (IN k NN)
             (= (MPOW m x (+ j k))
                ((MUL m) (MPOW m x j) (MPOW m x k))))))))))))
(warrant! 'mpow-add 'informal
  "n|->x^n is a monoid hom (NN,+,0)->(A,*,E).  NN induction on k: base k=0 by mpow-zero+right id; step by mpow-succ+associativity.  No commutativity used.")

;;; Cross law (commutativity required):  (x*y)^n = x^n * y^n.
;;; Holds in a COMMUTATIVE monoid only.  NN induction on n, reordering factors
;;; by commutativity at each step.
(theory-add-axiom! *current-theory* 'mpow-mult
  '(FORALL m
     (IMPLIES (IS-COMM-MONOID m)
       (FORALL x (IMPLIES (IN x (CARR m))
         (FORALL y (IMPLIES (IN y (CARR m))
           (FORALL n (IMPLIES (IN n NN)
             (= (MPOW m ((MUL m) x y) n)
                ((MUL m) (MPOW m x n) (MPOW m y n))))))))))))
(warrant! 'mpow-mult 'well-known
  "(xy)^n = x^n y^n in a commutative monoid; NN induction on n using commutativity to interleave factors.  Fails without commutativity.")

;;; Retroactive transport.  ABELIAN-GROUP-AS-MONOID is declared in views.scm,
;;; which loads BEFORE this file, so its one-shot auto-specialization ran when
;;; the MPOW theorems above did not yet exist.  view-as-auto-specialize! is
;;; idempotent (it skips names already installed), so re-running it here -- now
;;; that mpow-one/type/add (and the comm-monoid mpow-mult) are in the theorem
;;; table -- finally lowers them onto ABELIAN-GROUP (and, by view composition,
;;; onto the additive group of every ring/field/integral-domain/normed-field).
(view-as-auto-specialize! 'ABELIAN-GROUP-AS-MONOID)
