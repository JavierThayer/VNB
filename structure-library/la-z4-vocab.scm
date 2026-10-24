;;; la-z4-vocab.scm -- the free module Z^n, the image of a sequence under a map, the
;;; direct sum of cyclic groups of a sequence of integers, and invariant factors
;;; (LA-Z4, 2026-10-24).  No proof in this file.
;;;
;;; THE SOURCE.  The user's linear-algebra notes, section "Structure of Finitely
;;; Generated Abelian Groups": Proposition 3.50 (E is isomorphic to Z/(a_1) + ... +
;;; Z/(a_l) with a_1 | a_2 | ... | a_l non-negative, unique), Corollaries 3.51, 3.52.
;;; An abelian group is a ZZ-module (SCAL = ZZ-RING), as in la-z2-vocab / la-z3-vocab.
;;;
;;; THE DEFINITIONS.
;;;   ZZ-POW(n) -- Z^n: the direct sum of n copies of Z (RING-AS-MODULE(ZZ-RING)); its
;;;       vectors are the functions x on [1, n] with integer values.
;;;   ZZ-UNITS(n) -- the column of the unit vectors e_1, ..., e_n of Z^n; e_k is the
;;;       function t |-> (UNITROW(ZZ-RING, n, k))_{1t}, i.e. 1 at k and 0 elsewhere.
;;;   ZZ-ROW(n, x) -- the coefficient row (x(1), ..., x(n)) of a vector x of Z^n.
;;;   MAP-SEQ(h, n, u) -- the sequence h(u_1), ..., h(u_n), for a column sequence u
;;;       of length n (a matrix in MAT(n, 1, _), as in mod-seq.scm).
;;;   CYCLIC-SUM(l, a) -- Z/(a_1) + ... + Z/(a_l) for a function a on [1, l] with
;;;       integer values: DIRECT-SUM over ZZ-RING of the ZZ-MOD(a_i).  A summand
;;;       Z/(0) is a copy of Z, so the free part of a group is a run of zeros at the
;;;       end of the sequence.
;;;   IS-INVARIANT-FACTORS(l, a) -- a is a function on [1, l] with integer values,
;;;       each a_i >= 0 and a_i /= 1, and a_i divides a_j for i <= j.  The reading of
;;;       3.50 / 3.51 settled for this session: the invariant-factor form, no Z/(1)
;;;       summand (a_1 /= 1; with the chain and non-negativity this is the same as
;;;       a_i /= 1 for every i), Z/(0) standing for a copy of Z.
;;;
;;; Binders: zpi_ zut_ zua_ zub_ zra_ zrb_ msa_ msb_ csi_ ifi_ ifj_ -- names no
;;; predicate body, statement or driver uses elsewhere.
;;; Needs: structure-library/la-z3-vocab (DIRECT-SUM, RING-AS-MODULE, ZZ-MOD), matrix
;;; (MATOF, ENTRY, UNITROW), zz-divisibility (ZZ-DIVIDES), numeric-instances (ZZ-RING).
;;; Destination structure-library/; LOAD WINDOW after la-z3-vocab, before
;;; theorem-library/la-z4-free.  Library: linear-algebra.  No axiom, support or stamp.

(def-functoid 'ZZ-POW '(n)
  '(DIRECT-SUM ZZ-RING n (VNB-LAMBDA zpi_ (INTERVAL 1 n) (RING-AS-MODULE ZZ-RING))))

(def-functoid 'ZZ-UNITS '(n)
  '(MATOF n 1 (VNB-LAMBDA (LIST zua_ zub_) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 1))
                (VNB-LAMBDA zut_ (INTERVAL 1 n) (ENTRY (UNITROW ZZ-RING n zua_) 1 zut_)))))

(def-functoid 'ZZ-ROW '(n x)
  '(MATOF 1 n (VNB-LAMBDA (LIST zra_ zrb_) (CARTESIAN (INTERVAL 1 1) (INTERVAL 1 n)) (x zrb_))))

(def-functoid 'MAP-SEQ '(h n u)
  '(MATOF n 1 (VNB-LAMBDA (LIST msa_ msb_) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 1)) (h (ENTRY u msa_ msb_)))))

(def-functoid 'CYCLIC-SUM '(l a)
  '(DIRECT-SUM ZZ-RING l (VNB-LAMBDA csi_ (INTERVAL 1 l) (ZZ-MOD (a csi_)))))

(def-predicate 'IS-INVARIANT-FACTORS '(l a)
  '(AND (IN a (FUN (INTERVAL 1 l) ZZ))
   (AND (FORALL ifi_ (IMPLIES (IN ifi_ (INTERVAL 1 l)) (<= 0 (a ifi_))))
   (AND (FORALL ifi_ (IMPLIES (IN ifi_ (INTERVAL 1 l)) (NOT (= (a ifi_) 1))))
        (FORALL ifi_ (FORALL ifj_ (IMPLIES (IN ifi_ (INTERVAL 1 l)) (IMPLIES (IN ifj_ (INTERVAL 1 l))
          (IMPLIES (<= ifi_ ifj_) (ZZ-DIVIDES (a ifi_) (a ifj_)))))))))))

(notation! 'ZZ-POW 'kind 'functoid 'arity 1
           'english "the free module Z^$1")
(notation! 'ZZ-UNITS 'kind 'functoid 'arity 1
           'english "the unit vectors of Z^$1")
(notation! 'ZZ-ROW 'kind 'functoid 'arity 2
           'english "the coefficient row of $2 in Z^$1")
(notation! 'MAP-SEQ 'kind 'functoid 'arity 3
           'english "the image under $1 of the sequence $3 of length $2")
(notation! 'CYCLIC-SUM 'kind 'functoid 'arity 2
           'english "the direct sum of the cyclic groups Z/($2_i), i = 1, ..., $1")
(notation! 'IS-INVARIANT-FACTORS 'kind 'predicate 'arity 2
           'english "$2_1, ..., $2_$1 are invariant factors (non-negative, none equal to 1, each dividing the next)")


;;; ---- for the uniqueness half of 3.50 (Schanuel's comparison of two presentations) ----
;;;   DIAG-MAT(n, f) -- the n-by-n integer diagonal matrix with diagonal f(1), ..., f(n)
;;;       (f(i) times the identity matrix entry, so no case split is written).
;;;   PAD-ONES(m, k, f) -- the sequence 1, ..., 1 (k times), f(1), ..., f(m - k) on [1, m].
;;;   SEQ-HEAD(n, z), SEQ-SHIFT(n, z) -- for z on [1, 2n]: the sequences z(1), ..., z(n)
;;;       and z(n + 1), ..., z(n + n), on [1, n].
;;;   SEQ-JOIN(m, n, hd, tl) -- the sequence hd(1), ..., hd(n), tl(1), ..., tl(m - n) on [1, m].
;;; Binders: dga_ dgb_ poj_ shi_ sfi_ jnj_.
(def-functoid 'DIAG-MAT '(n f)
  '(MATOF n n (VNB-LAMBDA (LIST dga_ dgb_) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
                ((MUL ZZ-RING) (f dga_) (ENTRY (IDENTMAT ZZ-RING n) dga_ dgb_)))))

(def-functoid 'PAD-ONES '(m k f)
  '(VNB-LAMBDA poj_ (INTERVAL 1 m) (IF (<= poj_ k) 1 (f (NN-MINUS poj_ k)))))

(def-functoid 'SEQ-HEAD '(n z)
  '(VNB-LAMBDA shi_ (INTERVAL 1 n) (z shi_)))

(def-functoid 'SEQ-SHIFT '(n z)
  '(VNB-LAMBDA sfi_ (INTERVAL 1 n) (z (+ n sfi_))))

(def-functoid 'SEQ-JOIN '(m n hd tl)
  '(VNB-LAMBDA jnj_ (INTERVAL 1 m) (IF (<= jnj_ n) (hd jnj_) (tl (NN-MINUS jnj_ n)))))

(notation! 'DIAG-MAT 'kind 'functoid 'arity 2
           'english "the diagonal matrix with diagonal $2(1), ..., $2($1)")
(notation! 'PAD-ONES 'kind 'functoid 'arity 3
           'english "the sequence of $2 ones followed by $3, of length $1")
(notation! 'SEQ-HEAD 'kind 'functoid 'arity 2
           'english "the first $1 terms of $2")
(notation! 'SEQ-SHIFT 'kind 'functoid 'arity 2
           'english "the terms $1 + 1, ..., $1 + $1 of $2")
(notation! 'SEQ-JOIN 'kind 'functoid 'arity 4
           'english "$3 followed by $4, of length $1")

;;;   SCHANUEL-MAP(m, n, la, lb) -- on Z^m, m = n + n, written z = (t, b) with t the first n
;;;       and b the last n coordinates: (t, b) |-> (u, t + la(u)), u = b - lb(t).  With la, lb
;;;       homomorphisms of Z^n this is the automorphism of Schanuel's lemma; its inverse is
;;;       SCHANUEL-MAP(m, n, lb, la).  Binder scz_.
(def-functoid 'SCHANUEL-MAP '(m n la lb)
  '(VNB-LAMBDA scz_ (VEC (ZZ-POW m))
     (SEQ-JOIN m n ((VADD (ZZ-POW n)) (SEQ-SHIFT n scz_) ((VNEG (ZZ-POW n)) (lb (SEQ-HEAD n scz_))))
                   ((VADD (ZZ-POW n)) (SEQ-HEAD n scz_)
                      (la ((VADD (ZZ-POW n)) (SEQ-SHIFT n scz_) ((VNEG (ZZ-POW n)) (lb (SEQ-HEAD n scz_)))))))))
(notation! 'SCHANUEL-MAP 'kind 'functoid 'arity 4
           'english "the map (t, b) |-> (b - $4(t), t + $3(b - $4(t))) on Z^$1")
