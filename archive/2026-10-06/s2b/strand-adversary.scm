;;; strand-adversary.scm -- THE ADVERSARY: its traces, the infiltrated strand space
;;; (The paper's Definitions 3.1 and 3.2, Thayer, Herzog, Guttman, ~/docs/jcs_strand_spaces.pdf,
;;;  section 3.1, on the user's model of notes-60: key-free, the K / E / D traces dropped, the
;;;  binary C and S traces made n-ary.  The word is ADVERSARY (the user, 2026-10-06); the paper's
;;;  "penetrator" appears only when quoting it.)
;;; DEFINITIONS ONLY; the laws and the adversary bound are PROVEN in
;;; theorem-library/strand-adversary-bound.scm.  Agent S-2, week 3, 2026-10-06.  Binders: sa*_.
;;;
;;; THE TRACES over the tokens T, with P the tokens the adversary knows initially:
;;;   IS-TEXT-TRACE(T, P, s)      M: s = [[SENT, a]] for some a in P
;;;   IS-FLUSH-TRACE(T, s)        F: s = [[RECEIVED, g]] for some message g
;;;   IS-TEE-TRACE(T, s)          T: s = [[RECEIVED, g], [SENT, g], [SENT, g]]
;;;   IS-CONCAT-TRACE(T, s)       C: for a list l = [m1, ..., mk] of messages,
;;;                                  s = [[RECEIVED, m1], ..., [RECEIVED, mk], [SENT, l]]
;;;   IS-SEPARATE-TRACE(T, s)     S: for a list l = [m1, ..., mk] of messages,
;;;                                  s = [[RECEIVED, l], [SENT, m1], ..., [SENT, mk]]
;;;   IS-ADVERSARY-TRACE(T, P, s) the disjunction of the five.
;;; M, F and T are literal lists.  C and S are n-ary, so the trace is stated through the list
;;; QUANTIFIED and the trace characterised by its LENGTH and its entries (NTH): a list is
;;; determined by its length and entries (`tuple-extensionality'), so this IS "the trace built
;;; from l"; no constructor function is needed to state it, and none is needed to use it -- every
;;; proof reads entries.  The EXISTENCE of the traces -- for every list l of messages there is a
;;; C trace and an S trace -- is proven from `tuple-tabulation' (separate-trace-exists,
;;; concat-trace-exists in the bound file), so the characterisations are satisfiable; no list law
;;; was missing (finding (g) of S-2).
;;;
;;; THE INFILTRATED STRAND SPACE (Definition 3.2): a `declare-structure' (a structure is a
;;; declare-structure, the user's standing rule) with
;;;     substructure ISPACE      the strand space
;;;     carriers     ADV-IDS     the adversary's strand identifiers (a subset of IDS)
;;;                  ADV-TOKENS  the tokens the adversary knows initially (a subset of TOKENS)
;;;     law          every strand of an adversary identifier is an adversary trace
;;; ADV-IDS, not ADV: a short accessor collides with binders.  A bundle "of" an infiltrated space
;;; isp is a bundle c with BSPACE(c) = ISPACE(isp): the statements say so by that equation.
;;; IS-ADVERSARY-NODE(isp, n): the identifier of n is in ADV-IDS; IS-REGULAR-NODE its negation.
;;;
;;; Dependencies: strand-messages, strand-spaces (SENT, RECEIVED, STRAND-SPACE, NODES).

(def-predicate 'IS-TEXT-TRACE '(sat_ sap_ sas_)
  '(FORSOME saa_ (AND (IN saa_ sap_) (= sas_ (LIST (LIST SENT saa_))))))
(notation! 'IS-TEXT-TRACE 'kind 'predicate 'arity 3
           'english "$3 is a text trace of the adversary knowing $2 over the tokens $1")

(def-predicate 'IS-FLUSH-TRACE '(sat_ sas_)
  '(FORSOME sag_ (AND (IN sag_ (MSG-SET sat_)) (= sas_ (LIST (LIST RECEIVED sag_))))))
(notation! 'IS-FLUSH-TRACE 'kind 'predicate 'arity 2 'english "$2 is a flushing trace over the tokens $1")

(def-predicate 'IS-TEE-TRACE '(sat_ sas_)
  '(FORSOME sag_ (AND (IN sag_ (MSG-SET sat_))
                      (= sas_ (LIST (LIST RECEIVED sag_) (LIST SENT sag_) (LIST SENT sag_))))))
(notation! 'IS-TEE-TRACE 'kind 'predicate 'arity 2 'english "$2 is a tee trace over the tokens $1")

(def-predicate 'IS-CONCAT-TRACE '(sat_ sas_)
  '(FORSOME sal_ (AND (IN sal_ (TUPLES (MSG-SET sat_)))
     (AND (= (LENGTH sas_) (succ (LENGTH sal_)))
          (AND (FORALL sai_ (IMPLIES (IN sai_ NN) (IMPLIES (<= 1 sai_) (IMPLIES (<= sai_ (LENGTH sal_))
                 (= (NTH sai_ sas_) (LIST RECEIVED (NTH sai_ sal_)))))))
               (= (NTH (succ (LENGTH sal_)) sas_) (LIST SENT sal_)))))))
(notation! 'IS-CONCAT-TRACE 'kind 'predicate 'arity 2
           'english "$2 is a concatenation trace over the tokens $1")

(def-predicate 'IS-SEPARATE-TRACE '(sat_ sas_)
  '(FORSOME sal_ (AND (IN sal_ (TUPLES (MSG-SET sat_)))
     (AND (= (LENGTH sas_) (succ (LENGTH sal_)))
          (AND (= (NTH 1 sas_) (LIST RECEIVED sal_))
               (FORALL sai_ (IMPLIES (IN sai_ NN) (IMPLIES (<= 1 sai_) (IMPLIES (<= sai_ (LENGTH sal_))
                 (= (NTH (succ sai_) sas_) (LIST SENT (NTH sai_ sal_))))))))))))
(notation! 'IS-SEPARATE-TRACE 'kind 'predicate 'arity 2
           'english "$2 is a separation trace over the tokens $1")

(def-predicate 'IS-ADVERSARY-TRACE '(sat_ sap_ sas_)
  '(OR (IS-TEXT-TRACE sat_ sap_ sas_)
       (OR (IS-FLUSH-TRACE sat_ sas_)
           (OR (IS-TEE-TRACE sat_ sas_)
               (OR (IS-CONCAT-TRACE sat_ sas_) (IS-SEPARATE-TRACE sat_ sas_))))))
(notation! 'IS-ADVERSARY-TRACE 'kind 'predicate 'arity 3
           'english "$3 is an adversary trace for the adversary knowing $2 over the tokens $1")

(declare-structure INFILTRATED-SPACE
  (instance-var s)
  (substructure ISPACE STRAND-SPACE)
  (carriers ADV-IDS ADV-TOKENS)
  (law (FORALL sap_ (IMPLIES (IN sap_ (ADV-IDS s)) (IN sap_ (IDS (ISPACE s))))))
  (law (FORALL sat_ (IMPLIES (IN sat_ (ADV-TOKENS s)) (IN sat_ (TOKENS (ISPACE s))))))
  (law (FORALL sap_ (IMPLIES (IN sap_ (ADV-IDS s))
         (IS-ADVERSARY-TRACE (TOKENS (ISPACE s)) (ADV-TOKENS s) ((STRAND-MAP (ISPACE s)) sap_))))))

(notation! 'IS-INFILTRATED-SPACE 'noun "infiltrated strand space" 'article "an")
(notation! 'IS-HOM-INFILTRATED-SPACE 'kind 'predicate 'arity 3
           'english "$3 is a morphism of infiltrated strand spaces from $1 to $2")

(def-predicate 'IS-ADVERSARY-NODE '(sai_ san_) '(IN (NTH 2 san_) (ADV-IDS sai_)))
(notation! 'IS-ADVERSARY-NODE 'kind 'predicate 'arity 2 'english "$2 is an adversary node of $1")

(def-predicate 'IS-REGULAR-NODE '(sai_ san_) '(NOT (IN (NTH 2 san_) (ADV-IDS sai_))))
(notation! 'IS-REGULAR-NODE 'kind 'predicate 'arity 2 'english "$2 is a regular node of $1")
