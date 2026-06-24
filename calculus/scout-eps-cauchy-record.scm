;;; calculus/scout-eps-cauchy-record.scm
;;; ====================================================================
;;; A durable, examinable RECORD of two things from the 2026-06-24 session:
;;;
;;;   PART A -- worked examples of `ai' (antecedent inference), i.e. SKOLEMIZE:
;;;             opening an existential HYPOTHESIS by introducing a fresh
;;;             eigenvariable, and how it unlocks a downstream witness (`ew').
;;;
;;;   PART B -- scout's attempt on tb-has-eps-cauchy-subseq: how far the
;;;             ai/ew/inst lanes carry it, and the wall it hits (a CONSTRUCTED
;;;             eps/2 witness + forward CITATION it cannot reach).
;;;
;;; NOT part of load.scm; a probe/record script.  Reproduce with:
;;;   cd ~/prover
;;;   VNB_SKIP_PROOFS=1 mit-scheme --quiet --load load.scm \
;;;       --load calculus/scout-eps-cauchy-record.scm --eval '(exit)' \
;;;       > calculus/printouts/scout-eps-cauchy-record.txt 2>&1
;;;   grep -E '^;;;' calculus/printouts/scout-eps-cauchy-record.txt
;;; (skolem var indices v_k depend on load state, so they may differ run to run.)
;;; ====================================================================

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (ga) (and *ps* (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))
(define (snap tag)
  (display ";;;   [")(display tag)(display "]")(newline)
  (display ";;;     asms: ")(write (ga))(newline)
  (display ";;;     goal: ")(write (gf))(newline))
(define (--- t)(newline)(display ";;; ===== ")(display t)(display " =====")(newline))
(define (find-head h)            ; first assumption whose head is h
  (let loop ((as (ga)))
    (cond ((null? as) #f)
          ((and (pair? (car as)) (eq? (caar as) h)) (car as))
          (else (loop (cdr as))))))
(define (typed-elt cod)          ; the t of a (IN t cod) assumption
  (let loop ((as (ga)))
    (cond ((null? as) #f)
          ((and (pair? (car as)) (eq? (caar as) 'IN) (equal? (caddr (car as)) cod))
           (cadr (car as)))
          (else (loop (cdr as))))))

;;; ====================================================================
;;; PART A -- SKOLEMIZE (ai) worked examples
;;; ====================================================================

(--- "A1  ai skolemizes a bare existential hypothesis")
;; `ai HYP' on an existential assumption (FORSOME v body) introduces a FRESH
;; eigenvariable y (avoiding the goal + other asms) and replaces the hypothesis
;; with body[v := y].  Below: (exists v. v in GUBA) becomes (v_k in GUBA).
(sp (make-wff '(IMPLIES (FORSOME v (IN v GUBA)) (= a a))))
(di)                                            ; move antecedent into the asms
(snap "before ai: existential hypothesis (FORSOME v (IN v GUBA)) present")
(ai '(FORSOME v (IN v GUBA)))                     ; <-- SKOLEMIZE
(snap "after  ai: hypothesis opened to (IN v_k GUBA) with v_k fresh")

(--- "A2  ai on an AND-bodied existential (the Cauchy threshold shape)")
;; (exists N. N in NN and P(N)) -- ai skolemizes to the AND body at a fresh N_k;
;; a SECOND ai (the AND case of antecedent inference) splits that conjunction.
(sp (make-wff '(IMPLIES (FORSOME N (AND (IN N NN) (FUBA N))) (= a a))))
(di)
(ai '(FORSOME N (AND (IN N NN) (FUBA N))))    ; <-- SKOLEMIZE
(snap "after ai: gained ONE assumption (AND (IN N_k NN) (FUBA N_k))")
(ai (find-head 'AND))                           ; <-- ai's AND case = and-elim
(snap "after second ai: conjunction split into (IN N_k NN) and (FUBA N_k)")

(--- "A3  skolemize UNLOCKS a witness: ai then ew, driven to QED by hand")
;; Goal (exists w. w in GUBA) does NOT follow from (exists v. luba(v) in GUBA) by
;; assumption (different bodies).  ai exposes luba(v_k) in GUBA; THAT term is then a
;; legal witness for the goal (ew); ass closes.  This is the skolemize->witness
;; pattern at the heart of every forward existence proof.
(sp (make-wff '(IMPLIES (FORSOME v (IN (luba v) GUBA)) (FORSOME w (IN w GUBA)))))
(snap "start")
(grind)                                         ; di moves the existential hyp in
(snap "after grind")
(ai (find-head 'FORSOME))                       ; <-- SKOLEMIZE the hypothesis
(snap "after ai: luba(v_k) in GUBA now in context -- a usable witness")
(ew (typed-elt 'GUBA))                            ; witness the goal with luba(v_k)
(snap "after ew: goal reduced to (IN (luba v_k) GUBA), which IS an assumption")
(ass)
(display ";;;   done? ")(write (proof-done? *ps*))(newline)

(--- "A4  scout finds that SAME ai+ew proof automatically")
;; The copilot assembles grind -> ai -> ew -> ass on its own (the ai lane feeds
;; the ew lane).  This is the move the morning's lanes + the fresh-var-drift fix
;; made reachable in search.
(sp (make-wff '(IMPLIES (FORSOME v (IN (luba v) GUBA)) (FORSOME w (IN w GUBA)))))
(let ((r (scout 6 3 300)))
  (display ";;;   scout closing branch(es): ")(write (length (list-ref r 4)))(newline)
  (when (pair? (list-ref r 4))
    (display ";;;   branch 1 (note the (ai ...) and (ew ...) steps):")(newline)
    (display ";;;     ")(write (car (list-ref r 4)))(newline)))

;;; ====================================================================
;;; PART B -- scout on tb-has-eps-cauchy-subseq: the record of (2)
;;; ====================================================================

(--- "B  scout on the eps-Cauchy lemma -- how far, and the wall")
(sp (make-wff
  '(FORALL s (IMPLIES (TOTALLY-BOUNDED s)
     (FORALL f (IMPLIES (IN f (FUN NN (X s)))
       (FORALL eps (IMPLIES (POS-RR eps)
         (FORSOME phi (AND (STRICTLY-MONO-NN phi)
           (IS-EPS-CAUCHY-SEQ s eps (SUBSEQ f phi))))))))))))
(grind)                                         ; unfold TB + introduce hyps
(snap "lemma after grind (TB unfolded: the net forall-exists is now a hyp)")
;; Bounded scout so it TERMINATES (the full search explodes -- see below).
(display ";;;   running scout 3 2 50 (bounded so it terminates) ...")(newline)
(let ((r (scout 3 2 50)))
  (display ";;;   nodes examined: ")(write (list-ref r 0))(newline)
  (display ";;;   CLOSING branches: ")(write (length (list-ref r 4)))(newline)
  (display ";;;   best partials:   ")(write (length (list-ref r 3)))(newline))
;; WHY it cannot close (the wall, for the record):
;;  * the net radius eps/2 is a CONSTRUCTED term -- scout's inst lane only
;;    instantiates the net-forall at terms it can TYPE from context (eps itself,
;;    giving radius eps, not eps/2), so the 2r <= eps estimate never lines up;
;;  * pigeonhole-infinite / nn-enum-spec / ball-2r-triangle must be brought in by
;;    FORWARD CITATION (`fact'), a move scout's alphabet does not yet have;
;;  * the classifier pi:NN->F is a CHOICE-defined VNB-LAMBDA -- a construction,
;;    not a context witness.
;; So ai/ew/inst carry the skolemize/witness/instantiate plumbing, but the proof
;; needs a `fact' lane + constructed witnesses.  Those are the next frontiers.
(--- "end of record")
