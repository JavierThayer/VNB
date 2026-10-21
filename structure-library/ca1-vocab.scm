;;; ca1-vocab.scm -- THE COMPLEX NUMBERS AS 2-BY-2 REAL MATRICES (complex-analysis.pdf,
;;; Proposition 1.3).  DEFINITIONS ONLY; the laws and the proposition are proven in
;;; theorem-library/ca1-matrix-rep.scm.  Agent CA-1, 2026-10-19 (NEW DEFINITIONS, the
;;; user's to confirm).
;;;
;;;     CC-MATRIX-OF(a, b)   the 2-by-2 matrix [[a, b], [-b, a]], written as the literal
;;;                          list of its two rows (a matrix in the tree IS the list of its
;;;                          rows: structure-library/matrix.scm).
;;;     CC-MATRICES          the set of the 2-by-2 real matrices of that form:
;;;                          { P in MAT(2, 2, RR) : P = CC-MATRIX-OF(a, b) for some
;;;                          a, b in RR }  -- the set of the notes, "the 2 x 2 matrices of
;;;                          real numbers of the form [[a, b], [-b, a]], a, b in R".
;;;     CC-MATRIX-REP        the map Phi : a + b i |-> [[a, b], [-b, a]], i.e.
;;;                          z |-> CC-MATRIX-OF(real-part(z), imag-part(z)), an element of
;;;                          FUN(CC, MAT(2, 2, RR)).
;;;
;;; WHY THESE FORMS.  The notes define Phi on the formal expression a + b i; in the tree
;;; a complex number is not a pair, and its two coordinates are real-part and
;;; imag-part (characterised by z = real-part(z) + i imag-part(z), cc-re-im-decompose),
;;; so Phi reads them off.  CC-MATRIX-REP is a def-constant and not a def-functoid for the
;;; reason CC-COORDS is (structure-library/cc-coords.scm): it is ONE function, an element
;;; of FUN(CC, ...), which BIJECTION(CC, CC-MATRICES) has to be able to name, and
;;; def-functoid refuses an empty parameter list.  The defining equations are written
;;; with `==', as CC-COORDS's is.  CC-MATRIX-OF is a def-functoid (two parameters): the
;;; literal list keeps the entries readable as the notes write them, and the four ENTRY
;;; read-offs are `mac ENTRY' plus two `nth-r' each.
;;;
;;; The real matrices are matrices over the ring of reals as the tree has it, the
;;; six-slot view NORMED-FIELD-AS-COMMUTATIVE-RING(RR-NORMED-FIELD) (rr-scalar-ring-*,
;;; whose carrier is RR): the ring that MATADD / MATMUL / IDENTMAT take as argument.
;;; No new constant is introduced for it.
;;;
;;; BINDERS.  cmq_, cma_, cmb_, cmz_: used by no other body (the rule of CLAUDE.md,
;;; "Writing proof drivers": a binder of a term the driver rebuilds must be spelled like
;;; nothing a predicate body binds).
;;;
;;; WHERE IT LOADS.  After structure-library/matrix (MAT, ENTRY); CC, real-part,
;;; imag-part are in number-systems.

(def-functoid 'CC-MATRIX-OF '(a b)
  '(LIST (LIST a b) (LIST (- b) a)))
(notation! 'CC-MATRIX-OF 'kind 'functoid 'arity 2
           'english "the 2-by-2 matrix with rows [$1, $2] and [-$2, $1]")

(def-constant 'CC-MATRICES
  (list 'cc-matrices-def
        '(== CC-MATRICES
             (SEP cmq_ (MAT 2 2 RR)
               (FORSOME cma_ (AND (IN cma_ RR)
                 (FORSOME cmb_ (AND (IN cmb_ RR)
                   (= cmq_ (CC-MATRIX-OF cma_ cmb_))))))))))
(notation! 'CC-MATRICES 'kind 'constant 'arity 0
           'english "the set of 2-by-2 real matrices of the form [[a, b], [-b, a]]")

(def-constant 'CC-MATRIX-REP
  (list 'cc-matrix-rep-def
        '(== CC-MATRIX-REP
             (VNB-LAMBDA cmz_ CC (CC-MATRIX-OF (real-part cmz_) (imag-part cmz_))))))
(notation! 'CC-MATRIX-REP 'kind 'constant 'arity 0
           'english "the representation of a complex number a + b i as the matrix [[a, b], [-b, a]]")
