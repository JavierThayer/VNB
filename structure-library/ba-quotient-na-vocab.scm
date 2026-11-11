;;; ba-quotient-na-vocab.scm -- wave of 2026-11-09/10 (agent BA-1E), wired 2026-11-10 from scratchpad/ba1e-1109/ba-quotient-na-vocab.scm.
;;; Library: operator-algebras.

;;; ba-quotient-na-vocab.scm -- BANACH ALGEBRAS: the quotient algebra A/I (Thayer, 1.11, 1.12).
;;; Agent BA-1E, wave 2026-11-09.  Destination: structure-library/ba-quotient-na-vocab.scm.
;;; Library: operator-algebras.  No proof in this file.  Binders bqn*_, used by no other file.
;;; LOAD WINDOW: after structure-library/ba-vocab, structure-library/ba-quotient-vocab and
;;; structure-library/la-z3-vocab (QUOTIENT-MODULE, QMOD-SETOID).
;;;
;;; For a unital algebra a and a two-sided ideal ii, the cosets x + ii are the classes of the
;;; setoid QMOD-SETOID(UBA-AS-MODULE(a), ii) (x ~ y iff x - y in ii), and A/I as a module is
;;; QUOTIENT-MODULE(UBA-AS-MODULE(a), ii) (la-z3-vocab, with its proven module laws).  The
;;; quotient algebra takes the six module slots from there and adds
;;;   7 VNRM: the norm of a coset c, COSET-NORM(a, ii, c) = inf { ||u|| : u in c }, which at
;;;     c = x + ii is QUOT-NORM(a, ii, x) = inf { ||x - y|| : y in ii } (ba-quotient-vocab;
;;;     the equation is the theorem coset-norm-class-quot-norm);
;;;   8 VMUL: the product (x + ii)(y + ii) = xy + ii, the DESCEND2 of the class of the product;
;;;   9 VONE (QUOTIENT-BA only): the coset of 1.
;;; The norm is read off the coset itself, not off a representative, so it needs no
;;; representative-independence argument; the bridge to QUOT-NORM is one theorem.

(def-functoid 'COSET-NORM '(bqna_ bqni_ bqnc_)
  '(EINF (SEP bqnw_ RR (FORSOME bqnu_ (AND (IN bqnu_ bqnc_) (= bqnw_ ((VNRM bqna_) bqnu_)))))))

(def-functoid 'QNA-VNRM '(bqna_ bqni_)
  '(VNB-LAMBDA bqnc_ (QUOTIENT (QMOD-SETOID (UBA-AS-MODULE bqna_) bqni_)) (COSET-NORM bqna_ bqni_ bqnc_)))

(def-functoid 'QNA-VMUL '(bqna_ bqni_)
  '(DESCEND2 (QMOD-SETOID (UBA-AS-MODULE bqna_) bqni_)
     (VNB-LAMBDA (LIST bqnx_ bqny_) (CARTESIAN (VEC bqna_) (VEC bqna_))
       (CLASS (QMOD-SETOID (UBA-AS-MODULE bqna_) bqni_) ((VMUL bqna_) bqnx_ bqny_)))))

;;; A/I as a normed algebra (8 slots, the shape of COMPLEX-NORMED-ALGEBRA)
(def-functoid 'QUOTIENT-NA '(bqna_ bqni_)
  '(LIST (SCAL (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (VEC (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (VADD (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (VZERO (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (VNEG (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (ACT (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (QNA-VNRM bqna_ bqni_)
         (QNA-VMUL bqna_ bqni_)))

;;; A/I as a Banach algebra with unit (9 slots, the shape of UNITAL-BANACH-ALGEBRA)
(def-functoid 'QUOTIENT-BA '(bqna_ bqni_)
  '(LIST (SCAL (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (VEC (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (VADD (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (VZERO (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (VNEG (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (ACT (QUOTIENT-MODULE (UBA-AS-MODULE bqna_) bqni_))
         (QNA-VNRM bqna_ bqni_)
         (QNA-VMUL bqna_ bqni_)
         (CLASS (QMOD-SETOID (UBA-AS-MODULE bqna_) bqni_) (VONE bqna_))))

(notation! 'COSET-NORM 'kind 'functoid 'arity 3 'english "the norm of the coset $3 of $2 in $1")
(notation! 'QNA-VNRM 'kind 'functoid 'arity 2 'english "the quotient norm of $1 modulo $2")
(notation! 'QNA-VMUL 'kind 'functoid 'arity 2 'english "the product of $1 modulo $2")
(notation! 'QUOTIENT-NA 'kind 'functoid 'arity 2 'english "the quotient normed algebra $1/$2" 'tex "{$1}/{$2}")
(notation! 'QUOTIENT-BA 'kind 'functoid 'arity 2 'english "the quotient Banach algebra $1/$2" 'tex "{$1}/{$2}")
