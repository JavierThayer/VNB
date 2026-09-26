;;; subseq-apply.scm -- the VALUE of a subsequence at one TYPED index.
;;;
;;; SUBSEQ is a def-functoid (theorem-library/cauchy-subsequence.scm:63):
;;;
;;;     SUBSEQ(f, phi)  ==  (VNB-LAMBDA k NN (f (phi k)))
;;;
;;; so `mac SUBSEQ' unfolds EVERY occurrence in the goal, including the ones
;;; under a binder, and `lam-b' then reduces the redex under that binder too --
;;; owing the side leaf (IN (phi k) NN) in the OUTER context, where k is still
;;; free and the typing is therefore unprovable.  (Measured twice on
;;; 2026-09-19, in the diagonal-subsequence and block-tower drivers; the rule is
;;; now in CLAUDE.md, "Writing proof drivers".)
;;;
;;; Rewriting by the equation below instead touches only the application at a
;;; peeled, TYPED index, so no unlicensed redex is ever created.  Stated with
;;; `==' (quasi-equality), so it holds whether or not f is defined at phi(k).
;;;
;;; ONE HOME.  This lemma was written three times on 2026-09-19, verbatim and
;;; with the same three-line proof: `subseq-apply' (rake-diagonal-subseq.scm),
;;; `subseq-value-at' (rake-block-tower.scm), `subseq-value'
;;; (rake-lebesgue-number.scm).  It lives here now; the other two names are
;;; retired and their citations re-pointed at `subseq-apply'.
;;;
;;; LOAD POSITION.  SUBSEQ is defined at load.scm position 90
;;; (theorem-library/cauchy-subsequence), which is BELOW `interactive' (135),
;;; `driver-kit' (139) and `proof-debt' (140) -- so the lemma cannot sit
;;; immediately after its definition.  The earliest legal slot is the head of
;;; the theorem-library block that follows driver-kit; this file is wired just
;;; after theorem-library/equality-basics.  Its citers -- rake-lebesgue-number
;;; (309), rake-block-tower (459), rake-diagonal-subseq (470) -- are all far
;;; below.

(sp (make-wff
  '(FORALL f
     (FORALL phi
       (FORALL k_
         (IMPLIES (IN k_ NN)
           (== ((SUBSEQ f phi) k_) (f (phi k_)))))))))
(dk-peel!)
(mac 'SUBSEQ)
(lam-b)
(qrfl)
(qed 'subseq-apply)
(topic! 'subseq-apply 'analysis)
(gloss! 'subseq-apply
  "The reindexed sequence SUBSEQ(f, phi) takes at the natural index k the value
   f(phi(k)).  This is the defining equation of the functoid read at ONE index,
   so that a proof can rewrite a subsequence value without unfolding SUBSEQ
   everywhere in the goal.  Quasi-equality, so it holds whether or not f is
   defined there.")
(alias! 'subseq-apply "the value of a subsequence at an index")
