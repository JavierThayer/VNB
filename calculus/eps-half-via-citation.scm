;;; calculus/eps-half-via-citation.scm
;;; ====================================================================
;;; FINDING (2026-06-25): the "eps/2 constructed-arithmetic witness" is, in
;;; VNB's idiom, NOT a division term (/ eps 2) -- it is the existential half d
;;; from `rr-pos-halvable' (order-predicates.scm):
;;;     forall eps. POS-RR eps  =>  exists d. (POS-RR d and d + d = eps)
;;; cited via `ta' and skolemized.  The lemma's comment is explicit: the
;;; existential form "avoids naming a division operator: eps = d + d with d > 0
;;; ... Standard (d = eps/2)".  d+d=eps is EXACTLY what the 2r-triangle needs
;;; (2*rad <= d+d = eps when rad <= d), POS-RR d is free, no division operator,
;;; no positivity guard to discharge.  Constructing (/ eps 2) would fight the
;;; design AND hit a POS-RR(eps/2) discharge wall.
;;;
;;; This hand-proof closes the minimal eps/2 example to QED (done?=#t).  The ONLY
;;; move scout lacks is `ta rr-pos-halvable' -- FORWARD CITATION of a library
;;; lemma into context.  inst+ / ai (skolemize, now in grind) / ew are all in
;;; scout's alphabet.  Note di (NOT grind) keeps POS-RR eps FOLDED so inst+'s
;;; detach of the (POS-RR eps) guard succeeds -- the grind-unfold-vs-detach
;;; tension again.
;;;
;;; CONCLUSION: the eps/2 witness reduces to a `ta'/`fact' FORWARD-CITATION lane,
;;; which is ALSO what pigeonhole-infinite / nn-enum-spec / ball-2r-triangle need
;;; for the full Cauchy proof.  That lane (relevance-driven library citation) is
;;; the real next build; see project_proof_discovery.
;;;
;;; Run: VNB_SKIP_PROOFS=1 mit-scheme --quiet --load load.scm \
;;;        --load calculus/eps-half-via-citation.scm --eval '(exit)' 2>&1 | grep ';;H2'
;;; ====================================================================

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (ga) (and *ps* (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))
(define (find-head h) (let loop ((as (ga)))
  (cond ((null? as) #f) ((and (pair? (car as)) (eq? (caar as) h)) (car as)) (else (loop (cdr as))))))
(define (sym-in? s e) (cond ((eq? e s) #t) ((pair? e) (or (sym-in? s (car e)) (sym-in? s (cdr e)))) (else #f)))
(define (find-forall-with s)   ; first FORALL hyp whose body mentions symbol s
  (let loop ((as (ga)))
    (cond ((null? as) #f)
          ((and (pair? (car as)) (eq? (caar as) 'FORALL) (sym-in? s (car as))) (car as))
          (else (loop (cdr as))))))
(sp (make-wff '(IMPLIES
  (FORALL x (IMPLIES (POS-RR x) (LUBA x)))
  (FORALL eps (IMPLIES (POS-RR eps)
    (FORSOME d (AND (= (+ d d) eps) (LUBA d))))))))
(di)(di)(di)
(ta 'rr-pos-halvable)
(inst+ (find-forall-with 'd) 'eps)     ; rr-pos-halvable's universal (body mentions d)
(ai (find-head 'FORSOME))
(ai (find-head 'AND))
(let ((d0 (cadr (cadr (find-head '=)))))   ; d0 from (= (+ d0 d0) eps)
  (ew d0)
  (di)
  (ass)
  (inst+ (find-forall-with 'LUBA) d0)    ; forall x.POS-RR x=>LUBA x at d0
  (ass)
  (display ";;H2 done?=")(write (proof-done? *ps*))(display " open=")(write (length (proof-open-goals *ps*)))(newline))
