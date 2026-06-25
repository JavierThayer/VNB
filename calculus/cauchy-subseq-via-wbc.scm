;;; calculus/cauchy-subseq-via-wbc.scm
;;; ====================================================================
;;; FLAGSHIP -- totally-bounded => every sequence has a Cauchy subsequence,
;;; with the CONSTRUCTION discovered and applied by the copilot itself.
;;;
;;; The hard kernel of an existence proof is INVENTION: you must produce the
;;; witness phi.  Here the copilot produces it, by witness-shape backchaining --
;;; (wbc 'name) looks up the produces-witness index for a PSS lemma that builds
;;; the right KIND of object, resolves that lemma's premises against the context,
;;; applies it (fact: instantiate + auto-detach), and skolemizes its output.
;;; Two such steps assemble the whole construction:
;;;
;;;   exists phi : Cauchy subsequence
;;;     <- (wbc 'diagonalization)   needs a nested infinite family s
;;;     <- (wbc 'block-family)      needs TB s + a sequence + null radii  (in context)
;;;
;;; NB: drive the introductions with `di', NOT `grind' -- di keeps
;;; TOTALLY-BOUNDED(s) / NULL-RR-SEQ(rad) / the typing FOLDED, so each producer's
;;; premise can be matched and auto-detached (grind would unfold them; the
;;; grind-unfold-vs-detach tension).
;;;
;;; RESULT: the construction closes to a SINGLE residual -- `is-cauchy-seq s
;;; (subseq f f_3)' -- the estimate.  That residual is VERIFY, not INVENT: unfold
;;; is-cauchy-seq (forall eps>0 exists N ...), halve eps (rr-pos-halvable), pick k
;;; with rad(k) <= eps/2 (null-rr-seq), use the diagonal property (f_3's tail past
;;; k lies in blk_2(k)) so two tail terms sit in one rad(k)-ball, and close with
;;; ball-2r-triangle (already PSS) + crs.  Left as the documented remainder.
;;;
;;; Run: VNB_SKIP_PROOFS=1 mit-scheme --quiet --load load.scm \
;;;        --load calculus/cauchy-subseq-via-wbc.scm --eval '(exit)' 2>&1 | grep ';;C'
;;; ====================================================================

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (ga) (and *ps* (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))
(define (find-pred p)            ; the x of the first (p x ...) hypothesis
  (let loop ((as (ga)))
    (cond ((null? as) #f)
          ((and (pair? (car as)) (eq? (caar as) p)) (cadr (car as)))
          (else (loop (cdr as))))))

(sp (make-wff
  '(FORALL s (IMPLIES (TOTALLY-BOUNDED s)
     (FORALL f (IMPLIES (IN f (FUN NN (X s)))
       (FORALL rad (IMPLIES (NULL-RR-SEQ rad)
         (FORSOME phi (AND (STRICTLY-MONO-NN phi)
           (IS-CAUCHY-SEQ s (SUBSEQ f phi))))))))))))

;; introduce s, TB(s), f, typing, rad, null-rr-seq -- FOLDED (di, not grind)
(di)(di)(di)(di)(di)(di)
(display ";;C goal: ")(write (gf))(newline)
(display ";;C hyps (folded premises the producers will detach): ")
(write (ga))(newline)

(display ";;C --- (wbc 'block-family): build the nested infinite family ---")(newline)
(wbc 'block-family)
(display ";;C   got blk = ")(write (find-pred 'IN))(display " with nesting + small in context")(newline)

(display ";;C --- (wbc 'diagonalization): build the strictly-monotone reindexer ---")(newline)
(wbc 'diagonalization)
(let ((phi0 (find-pred 'STRICTLY-MONO-NN)))
  (display ";;C   got phi = ")(write phi0)(display " (strictly-mono, tail in the blocks)")(newline)
  ;; supply the witness, discharge the strictly-mono conjunct
  (ew phi0)
  (di)
  (ass)
  (display ";;C witness supplied; strictly-mono conjunct CLOSED.")(newline)
  (display ";;C done? = ")(write (proof-done? *ps*))(newline)
  (display ";;C RESIDUAL (the estimate, verify-not-invent) = ")(write (gf))(newline))
