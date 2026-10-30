;;; nso.scm -- THE ORIGINAL NEEDHAM-SCHROEDER PROTOCOL (Thayer, Herzog, Guttman, section 5.3), ON THE
;;; USER'S MODEL.  The NSL vocabulary of structure-library/nsl.scm (the public-key space PK-SPACE is
;;; reused as it is) with the second message {Na Nb}_KA: the responder's name is NOT in it (the paper:
;;; "in the original protocol, B's name is not included").  DEFINITIONS ONLY; Lemma 5.9 is proven in
;;; theorem-library/nso-laws.scm.  Agent SB-1, wave MAP-1026, 2026-10-26.  Destination:
;;; structure-library/nso.scm.  Library: strand.  Load window: after structure-library/nsl (PK-SPACE),
;;; before theorem-library/nso-laws.  Binders: the nl*_ names of nsl.scm (the driver code copied from
;;; nsl.scm rebuilds the space law with them).

(def-predicate 'IS-NSO-INIT-STRAND '(nlp_ nls_ nla_ nlb_ nlm_ nln_)
  '(AND (IN nla_ (NAMES nlp_))
   (AND (IN nlb_ (NAMES nlp_))
   (AND (IN nlm_ (TOKENS (ISPACE (PK-INF nlp_))))
   (AND (IN nln_ (TOKENS (ISPACE (PK-INF nlp_))))
   (AND (NOT (IN nlm_ (NAMES nlp_)))
   (AND (NOT (IN nlm_ (KEYS (ISPACE (PK-INF nlp_)))))
   (AND (NOT (IN nln_ (KEYS (ISPACE (PK-INF nlp_)))))
        (= nls_ (LIST (LIST SENT (ENCR (LST (LIST nlm_ nla_)) ((PUBKEY nlp_) nlb_)))
                      (LIST RECEIVED (ENCR (LST (LIST nlm_ nln_)) ((PUBKEY nlp_) nla_)))
                      (LIST SENT (ENCR nln_ ((PUBKEY nlp_) nlb_)))))))))))))
(notation! 'IS-NSO-INIT-STRAND 'kind 'predicate 'arity 6
           'english "$2 is an original Needham-Schroeder initiator's strand of $1 for the names $3, $4 and the values $5, $6")

(def-predicate 'IS-NSO-RESP-STRAND '(nlp_ nls_ nla_ nlb_ nlm_ nln_)
  '(AND (IN nla_ (NAMES nlp_))
   (AND (IN nlb_ (NAMES nlp_))
   (AND (IN nlm_ (TOKENS (ISPACE (PK-INF nlp_))))
   (AND (IN nln_ (TOKENS (ISPACE (PK-INF nlp_))))
   (AND (NOT (IN nln_ (NAMES nlp_)))
   (AND (NOT (IN nlm_ (KEYS (ISPACE (PK-INF nlp_)))))
   (AND (NOT (IN nln_ (KEYS (ISPACE (PK-INF nlp_)))))
        (= nls_ (LIST (LIST RECEIVED (ENCR (LST (LIST nlm_ nla_)) ((PUBKEY nlp_) nlb_)))
                      (LIST SENT (ENCR (LST (LIST nlm_ nln_)) ((PUBKEY nlp_) nla_)))
                      (LIST RECEIVED (ENCR nln_ ((PUBKEY nlp_) nlb_)))))))))))))
(notation! 'IS-NSO-RESP-STRAND 'kind 'predicate 'arity 6
           'english "$2 is an original Needham-Schroeder responder's strand of $1 for the names $3, $4 and the values $5, $6")

;;; -----------------------------------------------------------------------
;;; The NSL space.

(def-predicate 'IS-NSO-SPACE '(nlp_)
  '(AND (IS-PK-SPACE nlp_)
        (FORALL nli_ (IMPLIES (IN nli_ (IDS (ISPACE (PK-INF nlp_))))
          (OR (IN nli_ (ADV-IDS (PK-INF nlp_)))
              (OR (FORSOME nla_ (FORSOME nlb_ (FORSOME nlm_ (FORSOME nln_
                    (IS-NSO-INIT-STRAND nlp_ ((STRAND-MAP (ISPACE (PK-INF nlp_))) nli_) nla_ nlb_ nlm_ nln_)))))
                  (FORSOME nla_ (FORSOME nlb_ (FORSOME nlm_ (FORSOME nln_
                    (IS-NSO-RESP-STRAND nlp_ ((STRAND-MAP (ISPACE (PK-INF nlp_))) nli_) nla_ nlb_ nlm_ nln_)))))))))))
(notation! 'IS-NSO-SPACE 'kind 'predicate 'arity 1
           'english "$1 is an original Needham-Schroeder space")
