;;; flat-regular.scm -- PUBLIC-KEY SPACES WHOSE REGULAR CONTENTS ARE FLAT: the one property of the
;;; Needham-Schroeder-Lowe space (structure-library/nsl.scm) that sections 4-11 of theorem-library/nsl.scm
;;; use, abstracted so that NSL, the original Needham-Schroeder protocol (structure-library/nso.scm) and
;;; later protocols are INSTANCES (Thayer, Herzog, Guttman, ~/docs/jcs_strand_spaces.pdf, section 5).
;;; DEFINITIONS ONLY; the laws are in theorem-library/flat-regular-laws.scm.  Agent SB-2, wave MAP-1026,
;;; 2026-10-26.  Destination: structure-library/flat-regular.scm.  Library: strand.  Load window: after
;;; structure-library/nsl (PK-SPACE, PK-INF), before theorem-library/flat-regular-laws.
;;;
;;; IS-FLAT-REGULAR(nsp): nsp is a public-key strand space and the content of every regular node is an
;;; encryption, under a key, of a non-key token or of a list of non-key tokens.  (The paper's three
;;; hand-waves -- "no regular node contains an encrypted term as a proper subterm", "no regular node
;;; contains a subterm g h where h contains an encrypted subterm", "no regular strand originates a
;;; private key" -- are all consequences of it: flat-regular-encr-subterm, -list-subterm, -no-key.)
;;; Binders fr*_, used by no other body.

(def-predicate 'IS-FLAT-REGULAR '(frp_)
  '(AND (IS-PK-SPACE frp_)
        (FORALL frn_ (IMPLIES (IN frn_ (NODES (ISPACE (PK-INF frp_))))
          (IMPLIES (IS-REGULAR-NODE (PK-INF frp_) frn_)
            (FORSOME frk_ (AND (IN frk_ (KEYS (ISPACE (PK-INF frp_))))
              (OR (FORSOME frx_ (AND (IN frx_ (SEP frd_ (TOKENS (ISPACE (PK-INF frp_))) (NOT (IN frd_ (KEYS (ISPACE (PK-INF frp_)))))))
                                     (= (NODE-CONTENT (ISPACE (PK-INF frp_)) frn_) (ENCR frx_ frk_))))
                  (FORSOME frl_ (AND (IN frl_ (TUPLES (SEP frd_ (TOKENS (ISPACE (PK-INF frp_))) (NOT (IN frd_ (KEYS (ISPACE (PK-INF frp_))))))))
                                     (= (NODE-CONTENT (ISPACE (PK-INF frp_)) frn_) (ENCR (LST frl_) frk_))))))))))))
(notation! 'IS-FLAT-REGULAR 'kind 'predicate 'arity 1
           'english "$1 is a public-key strand space whose regular contents are flat")
