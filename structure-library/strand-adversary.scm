;;; strand-adversary.scm -- THE ADVERSARY: its traces, the infiltrated strand space
;;; (The paper's Definitions 3.1 and 3.2, Thayer, Herzog, Guttman, ~/docs/jcs_strand_spaces.pdf,
;;;  section 3.1, on the user's model of notes-60 with ENCRYPTION (the user's decision of
;;;  2026-10-06 16:40Z): the binary C and S traces made n-ary, the E and D traces back, the paper's
;;;  K trace subsumed by M (ADV-TOKENS may hold keys, which are tokens).  The word is ADVERSARY
;;;  (the user, 2026-10-06); the paper's "penetrator" appears only when quoting it.)
;;; DEFINITIONS ONLY; the laws and the adversary bound are PROVEN in
;;; theorem-library/strand-adversary-bound.scm.  Agent S-2, week 3, 2026-10-06; E and D added by
;;; agent S-2b the same day (S-2's key-free version: archive/2026-10-06/s2b/strand-adversary.scm).
;;; Binders: sa*_.
;;;
;;; THE TRACES of a strand space sp (A = MSG-SET(TOKENS sp, KEYS sp)), with P the tokens the
;;; adversary knows initially.  Every trace predicate takes the SPACE (S-2 took the token set):
;;; the D trace needs the key inverse KINV(sp), and one parameter shape for all seven keeps the
;;; disjunction uniform.
;;;   IS-TEXT-TRACE(sp, P, s)      M: s = [[SENT, a]] for some a in P
;;;   IS-FLUSH-TRACE(sp, s)        F: s = [[RECEIVED, g]] for some message g
;;;   IS-TEE-TRACE(sp, s)          T: s = [[RECEIVED, g], [SENT, g], [SENT, g]]
;;;   IS-CONCAT-TRACE(sp, s)       C: for a list l = [m1, ..., mk] of messages,
;;;                                   s = [[RECEIVED, m1], ..., [RECEIVED, mk], [SENT, LST(l)]]
;;;   IS-SEPARATE-TRACE(sp, s)     S: for a list l = [m1, ..., mk] of messages,
;;;                                   s = [[RECEIVED, LST(l)], [SENT, m1], ..., [SENT, mk]]
;;;   IS-ENCRYPT-TRACE(sp, s)      E: for a key k and a message m,
;;;                                   s = [[RECEIVED, k], [RECEIVED, m], [SENT, ENCR(m, k)]]
;;;   IS-DECRYPT-TRACE(sp, s)      D: for a key k and a message m,
;;;                                   s = [[RECEIVED, KINV(k)], [RECEIVED, ENCR(m, k)], [SENT, m]]
;;;   IS-ADVERSARY-TRACE(sp, P, s) the disjunction of the seven.
;;; M, F, T, E, D are literal lists.  C and S are n-ary, so the trace is stated through the list
;;; QUANTIFIED and characterised by its LENGTH and its entries (NTH); the EXISTENCE of the traces
;;; for every list of messages is proven from `tuple-tabulation' (separate-trace-exists,
;;; concat-trace-exists in the bound file).  The list SENT by C and RECEIVED by S is the MESSAGE
;;; LST(l) (the tag of S-2b); its components are the entries of l.
;;; E and D follow the paper's order (key first).  The key k is RECEIVED by E: the adversary
;;; encrypts only under keys it has; D receives the INVERSE key KINV(k), which for a symmetric
;;; key (a fixpoint of KINV) is k itself.
;;;
;;; THE INFILTRATED STRAND SPACE (Definition 3.2): a `declare-structure' with
;;;     substructure ISPACE      the strand space
;;;     carriers     ADV-IDS     the adversary's strand identifiers (a subset of IDS)
;;;                  ADV-TOKENS  the tokens the adversary knows initially (a subset of TOKENS;
;;;                              the paper's K_P is its keys)
;;;     law          every strand of an adversary identifier is an adversary trace
;;; ADV-IDS, not ADV: a short accessor collides with binders.  A bundle "of" an infiltrated space
;;; isp is a bundle c with BSPACE(c) = ISPACE(isp): the statements say so by that equation.
;;; IS-ADVERSARY-NODE(isp, n): the identifier of n is in ADV-IDS; IS-REGULAR-NODE its negation.
;;;
;;; Dependencies: strand-messages (MSG-SET, LST, ENCR), strand-spaces (SENT, RECEIVED,
;;; STRAND-SPACE with KEYS and KINV, NODES).

(def-predicate 'IS-TEXT-TRACE '(sasp_ sap_ sas_)
  '(FORSOME saa_ (AND (IN saa_ sap_) (= sas_ (LIST (LIST SENT saa_))))))
(notation! 'IS-TEXT-TRACE 'kind 'predicate 'arity 3
           'english "$3 is a text trace of the adversary knowing $2 in the strand space $1")

(def-predicate 'IS-FLUSH-TRACE '(sasp_ sas_)
  '(FORSOME sag_ (AND (IN sag_ (MSG-SET (TOKENS sasp_) (KEYS sasp_))) (= sas_ (LIST (LIST RECEIVED sag_))))))
(notation! 'IS-FLUSH-TRACE 'kind 'predicate 'arity 2 'english "$2 is a flushing trace in the strand space $1")

(def-predicate 'IS-TEE-TRACE '(sasp_ sas_)
  '(FORSOME sag_ (AND (IN sag_ (MSG-SET (TOKENS sasp_) (KEYS sasp_)))
                      (= sas_ (LIST (LIST RECEIVED sag_) (LIST SENT sag_) (LIST SENT sag_))))))
(notation! 'IS-TEE-TRACE 'kind 'predicate 'arity 2 'english "$2 is a tee trace in the strand space $1")

(def-predicate 'IS-CONCAT-TRACE '(sasp_ sas_)
  '(FORSOME sal_ (AND (IN sal_ (TUPLES (MSG-SET (TOKENS sasp_) (KEYS sasp_))))
     (AND (= (LENGTH sas_) (succ (LENGTH sal_)))
          (AND (FORALL sai_ (IMPLIES (IN sai_ NN) (IMPLIES (<= 1 sai_) (IMPLIES (<= sai_ (LENGTH sal_))
                 (= (NTH sai_ sas_) (LIST RECEIVED (NTH sai_ sal_)))))))
               (= (NTH (succ (LENGTH sal_)) sas_) (LIST SENT (LST sal_))))))))
(notation! 'IS-CONCAT-TRACE 'kind 'predicate 'arity 2
           'english "$2 is a concatenation trace in the strand space $1")

(def-predicate 'IS-SEPARATE-TRACE '(sasp_ sas_)
  '(FORSOME sal_ (AND (IN sal_ (TUPLES (MSG-SET (TOKENS sasp_) (KEYS sasp_))))
     (AND (= (LENGTH sas_) (succ (LENGTH sal_)))
          (AND (= (NTH 1 sas_) (LIST RECEIVED (LST sal_)))
               (FORALL sai_ (IMPLIES (IN sai_ NN) (IMPLIES (<= 1 sai_) (IMPLIES (<= sai_ (LENGTH sal_))
                 (= (NTH (succ sai_) sas_) (LIST SENT (NTH sai_ sal_))))))))))))
(notation! 'IS-SEPARATE-TRACE 'kind 'predicate 'arity 2
           'english "$2 is a separation trace in the strand space $1")

(def-predicate 'IS-ENCRYPT-TRACE '(sasp_ sas_)
  '(FORSOME sak_ (AND (IN sak_ (KEYS sasp_))
     (FORSOME sag_ (AND (IN sag_ (MSG-SET (TOKENS sasp_) (KEYS sasp_)))
       (= sas_ (LIST (LIST RECEIVED sak_) (LIST RECEIVED sag_) (LIST SENT (ENCR sag_ sak_)))))))))
(notation! 'IS-ENCRYPT-TRACE 'kind 'predicate 'arity 2
           'english "$2 is an encryption trace in the strand space $1")

(def-predicate 'IS-DECRYPT-TRACE '(sasp_ sas_)
  '(FORSOME sak_ (AND (IN sak_ (KEYS sasp_))
     (FORSOME sag_ (AND (IN sag_ (MSG-SET (TOKENS sasp_) (KEYS sasp_)))
       (= sas_ (LIST (LIST RECEIVED ((KINV sasp_) sak_)) (LIST RECEIVED (ENCR sag_ sak_)) (LIST SENT sag_))))))))
(notation! 'IS-DECRYPT-TRACE 'kind 'predicate 'arity 2
           'english "$2 is a decryption trace in the strand space $1")

(def-predicate 'IS-ADVERSARY-TRACE '(sasp_ sap_ sas_)
  '(OR (IS-TEXT-TRACE sasp_ sap_ sas_)
       (OR (IS-FLUSH-TRACE sasp_ sas_)
           (OR (IS-TEE-TRACE sasp_ sas_)
               (OR (IS-CONCAT-TRACE sasp_ sas_)
                   (OR (IS-SEPARATE-TRACE sasp_ sas_)
                       (OR (IS-ENCRYPT-TRACE sasp_ sas_) (IS-DECRYPT-TRACE sasp_ sas_))))))))
(notation! 'IS-ADVERSARY-TRACE 'kind 'predicate 'arity 3
           'english "$3 is an adversary trace for the adversary knowing $2 in the strand space $1")

(declare-structure INFILTRATED-SPACE
  (instance-var s)
  (substructure ISPACE STRAND-SPACE)
  (carriers ADV-IDS ADV-TOKENS)
  (law (FORALL sap_ (IMPLIES (IN sap_ (ADV-IDS s)) (IN sap_ (IDS (ISPACE s))))))
  (law (FORALL sat_ (IMPLIES (IN sat_ (ADV-TOKENS s)) (IN sat_ (TOKENS (ISPACE s))))))
  (law (FORALL sap_ (IMPLIES (IN sap_ (ADV-IDS s))
         (IS-ADVERSARY-TRACE (ISPACE s) (ADV-TOKENS s) ((STRAND-MAP (ISPACE s)) sap_))))))

(notation! 'IS-INFILTRATED-SPACE 'noun "infiltrated strand space" 'article "an")
(notation! 'IS-HOM-INFILTRATED-SPACE 'kind 'predicate 'arity 3
           'english "$3 is a morphism of infiltrated strand spaces from $1 to $2")

(def-predicate 'IS-ADVERSARY-NODE '(sai_ san_) '(IN (NTH 2 san_) (ADV-IDS sai_)))
(notation! 'IS-ADVERSARY-NODE 'kind 'predicate 'arity 2 'english "$2 is an adversary node of $1")

(def-predicate 'IS-REGULAR-NODE '(sai_ san_) '(NOT (IN (NTH 2 san_) (ADV-IDS sai_))))
(notation! 'IS-REGULAR-NODE 'kind 'predicate 'arity 2 'english "$2 is a regular node of $1")
