;;; structure-library/zz-nt-vocab.scm -- vocabulary for ch. 1 of the algebraic-numbers notes (ALGNUM, 2026-10-26).
;;; DEFINITIONS ONLY.  Library: algebra.  Load window: after zz-divisibility.
;;;
;;;   EULER-PHI(n)        the number of k in {1, ..., n} relatively prime to n (the notes, section 4)
;;;   ZZ-RESIDUE(k, m)    the r in {1, ..., m} with k = r (mod m): a CHOICE, which is that unique element for m >= 1
;;;                       (zz-residue-in, zz-residue-unique); the notes' residue classes Z/(m) read off {1..m}
(def-functoid 'EULER-PHI '(n)
  '(CARD (SEP ephk_ (INTERVAL 1 n) (ZZ-COPRIME ephk_ n))))
(notation! 'EULER-PHI 'kind 'functoid 'arity 1 'english "Euler's totient of $1")
(def-functoid 'ZZ-RESIDUE '(k m)
  '(CHOICE (SEP zrr_ (INTERVAL 1 m) (ZZ-DIVIDES m (- k zrr_)))))
(notation! 'ZZ-RESIDUE 'kind 'functoid 'arity 2 'english "the residue of $1 modulo $2 in 1..$2")
;;;   IS-MULTIPLICATIVE(f) f : N -> R with f(m n) = f(m) f(n) for relatively prime m, n >= 1 (the notes, Lemma 1.24)
(def-predicate 'IS-MULTIPLICATIVE '(f)
  '(AND (IN f (FUN NN RR))
        (FORALL mlm_ (IMPLIES (IN mlm_ NN) (FORALL mln_ (IMPLIES (IN mln_ NN)
          (IMPLIES (<= 1 mlm_) (IMPLIES (<= 1 mln_) (IMPLIES (ZZ-COPRIME mlm_ mln_)
            (= (f (* mlm_ mln_)) (* (f mlm_) (f mln_))))))))))))
(notation! 'IS-MULTIPLICATIVE 'kind 'predicate 'arity 1 'english "$1 is multiplicative")
