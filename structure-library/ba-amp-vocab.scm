;;; ba-amp-vocab.scm -- Thayer, Banach Algebras and Applications, ch. 6 (the amplification in the proof of
;;; the bicommutant theorem 6.1): the canonical injections, projections and diagonal operators of the
;;; Hilbert direct sum HSUM(w, v) (ba-ops-vocab.scm), the one-step amplification phi |-> (T |-> phi(T) (+) T),
;;; the identity representation, the image of a set of operators under a representation, unital
;;; *-representations of L(H) and the intertwining property used to carry the bicommutant through the
;;; amplification.  DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Agent BA-1111-C2, 2026-11-11.  DESTINATION: structure-library/ba-amp-vocab.scm, after
;;; structure-library/ba-ops-vocab.scm (HSUM, BOUNDED-OPS, BOP-*) and ba-vn-vocab.scm (BICOMMUTANT).
;;; Library: operator-algebras.  Binders am*_ (amw_ amv_ amx_ amy_ amp_ ama_ amb_ amf_ amt_ amu_ amz_
;;; amr_ amq_ amk_ amc_ ams_), used by no other file.
;;;
;;;   HSUM-IN1(w, v), HSUM-IN2(w, v)     x |-> (x, 0) : w -> w (+) v,   y |-> (0, y) : v -> w (+) v
;;;   HSUM-PR1(w, v), HSUM-PR2(w, v)     (x, y) |-> x,   (x, y) |-> y
;;;   HSUM-DIAG(w, v, a, b)              (x, y) |-> (a x, b y), the operator a (+) b
;;;   AMP-STEP(v, w, f)                  T |-> f(T) (+) T on L(v): from a representation f of L(v) on w,
;;;                                      a representation on w (+) v.  Iterated from ID-REP it is the
;;;                                      amplification T |-> T (+) ... (+) T of the notes.
;;;   ID-REP(v)                          T |-> T on L(v)
;;;   REP-IMAGE(v, w, f, s)              f(s) = {f(T) : T in s}, a set of operators on w
;;;   IS-STAR-REP(v, w, f)               f : L(v) -> L(w) preserves +, scalar multiples, composition, the
;;;                                      identity and the adjoint
;;;   IS-AMPLIFICATION(v, s, w, f)       w is a Hilbert space, f a unital *-representation of L(v) on w, and
;;;                                      f carries s'' into f(s)'' in the strong sense that every operator
;;;                                      v -> w, w -> v, w -> w intertwining id / f with f / id on s
;;;                                      intertwines them on s''
;;;   IS-INTERTWINED(u, z, r, q, v, s)   every bounded K : u -> z with K r(A) = q(A) K for all A in s has
;;;                                      K r(T) = q(T) K for all T in the bicommutant s'' (pointwise)

(def-functoid 'HSUM-IN1 '(amw_ amv_) '(VNB-LAMBDA amx_ (VEC amw_) (LIST amx_ (VZERO amv_))))
(def-functoid 'HSUM-IN2 '(amw_ amv_) '(VNB-LAMBDA amy_ (VEC amv_) (LIST (VZERO amw_) amy_)))
(def-functoid 'HSUM-PR1 '(amw_ amv_) '(VNB-LAMBDA amp_ (CARTESIAN (VEC amw_) (VEC amv_)) (NTH 1 amp_)))
(def-functoid 'HSUM-PR2 '(amw_ amv_) '(VNB-LAMBDA amp_ (CARTESIAN (VEC amw_) (VEC amv_)) (NTH 2 amp_)))
(def-functoid 'HSUM-DIAG '(amw_ amv_ ama_ amb_)
  '(VNB-LAMBDA amp_ (CARTESIAN (VEC amw_) (VEC amv_)) (LIST (ama_ (NTH 1 amp_)) (amb_ (NTH 2 amp_)))))
(def-functoid 'AMP-STEP '(amv_ amw_ amf_)
  '(VNB-LAMBDA amt_ (BOUNDED-OPS amv_ amv_) (HSUM-DIAG amw_ amv_ (amf_ amt_) amt_)))
(def-functoid 'ID-REP '(amv_) '(VNB-LAMBDA amt_ (BOUNDED-OPS amv_ amv_) amt_))
(def-functoid 'REP-IMAGE '(amv_ amw_ amf_ ams_)
  '(SEP amb_ (BOUNDED-OPS amw_ amw_) (FORSOME amt_ (AND (IN amt_ ams_) (= amb_ (amf_ amt_))))))

(def-predicate 'IS-STAR-REP '(amv_ amw_ amf_)
  (conjuncts->and
    (list
      '(IN amf_ (FUN (BOUNDED-OPS amv_ amv_) (BOUNDED-OPS amw_ amw_)))
      '(FORALL ama_ (IMPLIES (IN ama_ (BOUNDED-OPS amv_ amv_)) (FORALL amb_ (IMPLIES (IN amb_ (BOUNDED-OPS amv_ amv_))
         (= (amf_ (BOP-SUM amv_ amv_ ama_ amb_)) (BOP-SUM amw_ amw_ (amf_ ama_) (amf_ amb_)))))))
      '(FORALL amc_ (IMPLIES (IN amc_ CC) (FORALL ama_ (IMPLIES (IN ama_ (BOUNDED-OPS amv_ amv_))
         (= (amf_ (BOP-SCALE amv_ amv_ amc_ ama_)) (BOP-SCALE amw_ amw_ amc_ (amf_ ama_)))))))
      '(FORALL ama_ (IMPLIES (IN ama_ (BOUNDED-OPS amv_ amv_)) (FORALL amb_ (IMPLIES (IN amb_ (BOUNDED-OPS amv_ amv_))
         (= (amf_ (BOP-COMP amv_ ama_ amb_)) (BOP-COMP amw_ (amf_ ama_) (amf_ amb_)))))))
      '(= (amf_ (BOP-ID amv_)) (BOP-ID amw_))
      '(FORALL ama_ (IMPLIES (IN ama_ (BOUNDED-OPS amv_ amv_))
         (= (amf_ (OP-ADJOINT amv_ amv_ ama_)) (OP-ADJOINT amw_ amw_ (amf_ ama_))))))))

(def-predicate 'IS-INTERTWINED '(amu_ amz_ amr_ amq_ amv_ ams_)
  '(FORALL amk_ (IMPLIES (IN amk_ (BOUNDED-OPS amu_ amz_))
     (IMPLIES (FORALL ama_ (IMPLIES (IN ama_ ams_) (FORALL amx_ (IMPLIES (IN amx_ (VEC amu_))
                (= (amk_ ((amr_ ama_) amx_)) ((amq_ ama_) (amk_ amx_)))))))
              (FORALL amt_ (IMPLIES (IN amt_ (BICOMMUTANT amv_ ams_)) (FORALL amx_ (IMPLIES (IN amx_ (VEC amu_))
                (= (amk_ ((amr_ amt_) amx_)) ((amq_ amt_) (amk_ amx_)))))))))))

(def-predicate 'IS-AMPLIFICATION '(amv_ ams_ amw_ amf_)
  (conjuncts->and
    (list '(IS-HILBERT-SPACE amw_)
          '(IS-STAR-REP amv_ amw_ amf_)
          '(IS-INTERTWINED amv_ amw_ (ID-REP amv_) amf_ amv_ ams_)
          '(IS-INTERTWINED amw_ amv_ amf_ (ID-REP amv_) amv_ ams_)
          '(IS-INTERTWINED amw_ amw_ amf_ amf_ amv_ ams_))))

(notation! 'HSUM-IN1 'kind 'functoid 'arity 2 'english "the injection of $1 into the Hilbert direct sum of $1 and $2" 'tex "\\iota_1")
(notation! 'HSUM-IN2 'kind 'functoid 'arity 2 'english "the injection of $2 into the Hilbert direct sum of $1 and $2" 'tex "\\iota_2")
(notation! 'HSUM-PR1 'kind 'functoid 'arity 2 'english "the projection of the Hilbert direct sum of $1 and $2 onto $1" 'tex "\\pi_1")
(notation! 'HSUM-PR2 'kind 'functoid 'arity 2 'english "the projection of the Hilbert direct sum of $1 and $2 onto $2" 'tex "\\pi_2")
(notation! 'HSUM-DIAG 'kind 'functoid 'arity 4 'english "the diagonal operator $3 (+) $4" 'tex "{$3} \\oplus {$4}")
(notation! 'AMP-STEP 'kind 'functoid 'arity 3 'english "the representation T |-> $3(T) (+) T" 'tex "{$3} \\oplus \\mathrm{id}")
(notation! 'ID-REP 'kind 'functoid 'arity 1 'english "the identity representation of the operators on $1" 'tex "\\mathrm{id}")
(notation! 'REP-IMAGE 'kind 'functoid 'arity 4 'english "the image of $4 under $3" 'tex "{$3}({$4})")
(notation! 'IS-STAR-REP 'kind 'predicate 'arity 3 'english "$3 is a unital *-representation of the operators on $1 on $2")
(notation! 'IS-AMPLIFICATION 'kind 'predicate 'arity 4 'english "$4 is an amplification of the operators on $1 on $3 adapted to $2")
(notation! 'IS-INTERTWINED 'kind 'predicate 'arity 6 'english "every operator from $1 to $2 intertwining $3 and $4 on $6 intertwines them on the bicommutant of $6")
