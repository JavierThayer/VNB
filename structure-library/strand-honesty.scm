;;; strand-honesty.scm -- HONEST IDEALS (Thayer, Herzog, Guttman, ~/docs/jcs_strand_spaces.pdf, Definition 6.10),
;;; on the user's model: an infiltrated space isp, a bundle c, a set I of messages.  The paper: "I is honest
;;; relative to a bundle C iff whenever a penetrator node p is an entry point for I, p is an M node or a K
;;; node."  The model merges the paper's M and K strands into ONE text trace (the adversary's known tokens
;;; ADV-TOKENS hold its keys too), so the conclusion is: p lies on a TEXT trace.
;;; DEFINITIONS ONLY; the laws are in theorem-library/strand-honesty-laws.scm.  Agent SB-2, wave MAP-1026,
;;; 2026-10-26.  Destination: structure-library/strand-honesty.scm.  Library: strand.  Load window: after
;;; structure-library/strand-adversary.  Binders sh*_.

(def-predicate 'IS-HONEST '(shp_ shc_ shi_)
  '(FORALL shn_ (IMPLIES (IN shn_ (BNODES shc_))
     (IMPLIES (IS-ADVERSARY-NODE shp_ shn_)
      (IMPLIES (IS-ENTRY-POINT (ISPACE shp_) shn_ shi_)
               (IS-TEXT-TRACE (ISPACE shp_) (ADV-TOKENS shp_) ((STRAND-MAP (ISPACE shp_)) (NTH 2 shn_))))))))
(notation! 'IS-HONEST 'kind 'predicate 'arity 3
           'english "$3 is honest relative to the bundle $2 of the infiltrated space $1")
