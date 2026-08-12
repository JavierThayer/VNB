;;; spans-submodule-fg-proof.scm -- THE DESCENT.
;;;
;;; A submodule sm of a submodule bm SPANNED by n elements u is spanned by <= n
;;; elements.  Induction on n inside md -- tex:1651, the lemma Smith cannot supply.
;;; Factored: spans-fg-base (n=0) + spans-fg-step (succ), assembled under `ni`.
;;; USES bc* (empty-matrix witnesses) -- do NOT compile this file.

;;; ---- driver helpers (sd- prefix), on top of the dk- kit (driver-kit.scm).
;;; Everything that used to name an assumption BY SHAPE now names it by what the
;;; tactic LANDED (dk-landed / dk-landed-find / dk-split!).  Shape matching
;;; survives only where the candidates are the goal's own freshly-opened leaves.
(define (sd-goal) (dk-goal))
(define (sd-foc! n) (dk-focus! n))
(define (sd-asms) (dk-asms))
(define (sd-di*)
  (let lp () (let* ((g (sd-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (sd-head? h) (dk-head? h))
(define (sd-find-opt pred) (let loop ((as (sd-asms)))
                             (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (sd-find pred) (or (sd-find-opt pred) (error "sd-find: none")))
(define (sd-mentions? form sub)
  (cond ((equal? form sub) #t)
        ((pair? form) (or (sd-mentions? (car form) sub) (sd-mentions? (cdr form) sub)))
        (else #f)))
(define (sd-mentions-pred sub) (lambda (g) (sd-mentions? g sub)))
;; run branching tactic `act`, dispatch each NEW leaf to the first matching clause
(define (sd-branch! act . clauses)
  (let ((new (dk-opened act)))
    (for-each (lambda (cl)
                (let ((leaf (find-first (lambda (l) ((car cl) (wff-formula (sequent-node-assertion l)))) new)))
                  (if leaf (begin (sd-foc! leaf) ((cdr cl)))
                      (error "sd-branch!: no leaf for a clause"))))
              clauses)))
;; ai a FORSOME assumption; return its eigenvariable, read off the typing IT landed
(define (sd-ai-eigen! forsome typ)
  (let* ((in? (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (caddr a) typ))))
         (conjs (dk-split! forsome))                     ; eigen typing + body, ANDs split
         (typing (find-first in? conjs)))
    (if typing (cadr typing) (error "sd-ai-eigen!: no typing landed for" typ conjs))))
;; inst+ a context universal at t; return the DEEPEST formula it landed (inst+
;; auto-detaches in-context antecedents, so it lands a chain, not one formula)
(define (sd-inst! f t) (dk-deepest (lambda () (inst+ f t))))
(define (sd-cut! p prove-sub)
  (let* ((new (dk-opened (lambda () (cut p))))
         (sub (car (filter (lambda (l) (equal? (wff-formula (sequent-node-assertion l)) p)) new)))
         (cont (car (filter (lambda (l) (not (eq? l sub))) new))))
    (sd-foc! sub) (prove-sub) (sd-foc! cont)))
(define (sd-empty-close! v)                           ; close from (IN v (INTERVAL 1 0))
  (fact 'interval-lo 1 0 v) (fact 'interval-hi 1 0 v)
  (fact 'interval-elt-in-nn 1 0 v) (fact 'nn-not-le-zero-pos v)
  (ai (list 'NOT (list '<= v 0))))

;; the body REST[ntm] of the statement (u, bm, sm, conclusion) at length ntm
(define (sd-rest ntm)
  `(FORALL u (IMPLIES (IN u (MAT ,ntm 1 (VEC md)))
    (FORALL bm (IMPLIES (IS-SUBMODULE md bm)
     (IMPLIES (SPANS md ,ntm u bm)
      (FORALL sm (IMPLIES (IS-SUBMODULE md sm)
       (IMPLIES (SUBSET sm bm)
        (FORSOME k (AND (AND (IN k NN) (<= k ,ntm))
         (FORSOME w (AND (IN w (MAT k 1 (VEC md)))
                         (SPANS md k w sm))))))))))))))
(define sd-w0  '(MATOF 0 1 (VNB-LAMBDA (LIST i_ j_) (CARTESIAN (INTERVAL 1 0) (INTERVAL 1 1)) (VZERO md))))       ; empty column seq
(define sd-ce0 '(MATOF 1 0 (VNB-LAMBDA (LIST i_ j_) (CARTESIAN (INTERVAL 1 1) (INTERVAL 1 0)) (ZERO (SCAL md))))) ; empty coeff row
(define (sd-empty-in! typ)   ; prove (IN (MATOF m n g) typ) with a 0 dimension, via bc*
  (bc* 'matof-in-mat) (sd-di*)
  (sd-empty-close! (cadr (sd-find (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                   (equal? (caddr f) '(INTERVAL 1 0))))))))


;;; ================= spans-fg-base : n = 0 =================
(sp (make-wff `(FORALL md (IMPLIES (AND (IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md)))
                                   ,(sd-rest 0)))))
(di) (di) (ai '(AND (IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md))))
(sd-di*)                                              ; u, bm, sm + their guards; goal FORSOME k
;; every element of bm is 0.u = VZERO -- capture the "combination" conjunct of SPANS md 0 u bm.
;; Name it by what mac-h/ai LANDED, not by its shape: the entries-typing conjunct has the
;; same FORALL/IMPLIES head.
(define sd-bm-comb
  (let ((conjs (dk-split! (dk-landed-1 (lambda () (mac-h 'SPANS '(SPANS md 0 u bm)))))))
    (or (find-first (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (sd-mentions? a 'FORSOME))) conjs)
        (error "spans-fg-base: no combination conjunct among" conjs))))
(ew 0)
(sd-branch! (lambda () (di))
  (cons (sd-head? 'AND)                               ; (AND (IN 0 NN)(<= 0 0))
        (lambda () (sd-branch! (lambda () (di))
                     (cons (sd-head? 'IN) (lambda () (fact 'nn-zero-in) (ass)))
                     (cons (sd-head? '<=) (lambda () (fact 'nn-zero-in) (fact 'nn-zero-le 0) (ass))))))
  (cons (sd-head? 'FORSOME)                           ; witness w = empty column
        (lambda ()
          (sd-cut! (list 'IN sd-w0 '(MAT 0 1 (VEC md))) (lambda () (sd-empty-in! '(MAT 0 1 (VEC md)))))
          (ew sd-w0)
          (sd-branch! (lambda () (di))
            (cons (sd-head? 'IN) (lambda () (ass)))    ; IN w0 (MAT 0 1 VEC)
            (cons (sd-head? 'SPANS)
              (lambda ()
                (mac 'SPANS)
                (sd-branch! (lambda () (di))
                  (cons (sd-mentions-pred 'INTERVAL)   ; entries: vacuous over [1,0]
                        (lambda () (sd-di*) (sd-empty-close! (caddr (cadr (sd-goal))))))
                  (cons (sd-mentions-pred 'FORSOME)     ; every x in sm is a combination
                    (lambda ()
                      (sd-di*)
                      (let ((xx (cadr (sd-find (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                                               (equal? (caddr a) 'sm)))))))
                        ;; x in bm, so x = c'.u = VZERO
                        (fact 'subset-mem-fwd 'sm 'bm xx)
                        (let* ((c1 (sd-inst! sd-bm-comb xx))
                               (cw (sd-ai-eigen! c1 '(MAT 1 0 (CARR (SCAL md))))))
                          (fact 'matact-empty-vzero 'md cw 'u)
                          (let ((xeq (sd-find (lambda (a) (and (pair? a) (eq? (car a) '=) (equal? (cadr a) xx))))))
                            (subst xeq)                 ; x -> c'.u
                            (subst (list '= (list 'ENTRY (list 'MATACT 'md cw 'u) 1 1) '(VZERO md))))
                          ;; goal now: FORSOME c (IN c (MAT 1 0 CARR) AND VZERO = c.w0)
                          (sd-cut! (list 'IN sd-ce0 '(MAT 1 0 (CARR (SCAL md))))
                                   (lambda () (sd-empty-in! '(MAT 1 0 (CARR (SCAL md))))))
                          (ew sd-ce0)
                          (sd-branch! (lambda () (di))
                            (cons (sd-head? 'IN) (lambda () (ass)))
                            (cons (sd-head? '=)
                              (lambda ()
                                (fact 'matact-empty-vzero 'md sd-ce0 sd-w0)
                                (subst (list '= (list 'ENTRY (list 'MATACT 'md sd-ce0 sd-w0) 1 1) '(VZERO md)))
                                (fact 'module-vzero-in 'md)
                                (rfl)))))))))))))))
(qed 'spans-fg-base)
(topic! 'spans-fg-base 'algebra)




;;; ================= spans-fg-step : the inductive step =================
;;;
;;; sm <= bm = span(u_1..u_{succ n}).  Let u' = u_1..u_n, bm' = SPAN(md,n,u'),
;;; sm' = sm ^ bm'.  The last coefficients of the elements of sm form an ideal S
;;; of the (euclidean) scalar ring (lastcoeff-set-is-ideal), so S = (b) for some
;;; b in S (euclidean-ideal-has-generator), and b is the last coefficient of some
;;; x0 = c0.u in sm.  For x = c.u in sm the last coefficient c_{1,succ n} is q.b,
;;; so y = x + (-q).x0 kills it: y lies in bm' (descent-remainder) and in sm (a
;;; submodule), hence in sm'.  The IH at (u',bm',sm') gives w' spanning sm' with
;;; k' <= n, and x = y + q.x0 = (c',q).(w',x0) (matact-snoc): sm is spanned by
;;; SNOC-COL(w',x0), of length succ k' <= succ n.  q = 0 covers S = {0}, so there
;;; is no case split.
;;;
;;; Every assumption below is named by what a tactic LANDED (dk-landed and
;;; friends), never by its shape: this context carries the IH, the instantiated
;;; IH, and the SPANS of both bm and bm' -- four look-alikes.

(define (sd-inst-detach! f t)          ; instantiate, then detach while antecedents are in ctx
  (let loop ((g (sd-inst! f t)))
    (if (and (pair? g) (eq? (car g) 'IMPLIES))
        (loop (dk-deepest (lambda () (detach! g))))
        g)))
(define (sd-conj pred conjs)           ; the unique conjunct satisfying pred
  (or (find-first pred conjs) (error "sd-conj: no conjunct matches among" conjs)))
(define (sd-typed-in typ) (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (caddr a) typ))))
(define (sd-in-mat? a) (and (pair? a) (eq? (car a) 'IN) (pair? (caddr a)) (eq? (car (caddr a)) 'MAT)))
(define (sd-eigen-of a) (cadr a))      ; the eigenvariable of a landed (IN v TYP)
(define (sd-ii-ass!)                   ; goal (IN v (INTERSECTION s1 s2)); both halves in ctx
  (for-each (lambda (l) (sd-foc! l) (ass)) (dk-opened ii)))
(define (sd-cases! orf . clauses)      ; ai an OR: dispatch each new leaf by ITS disjunct
  (let ((new (dk-opened (lambda () (ai orf)))))
    (for-each (lambda (cl)
                (let ((leaf (find-first
                             (lambda (l) (member (car cl)
                                                 (map wff-formula (sequent-node-assumptions l))))
                             new)))
                  (if leaf (begin (sd-foc! leaf) ((cdr cl)))
                      (error "sd-cases!: no leaf assumes" (car cl)))))
              clauses)))

(sp (make-wff `(FORALL md (IMPLIES (AND (IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md)))
                 (FORALL n (IMPLIES (IN n NN)
                   (IMPLIES ,(sd-rest 'n) ,(sd-rest '(succ n)))))))))
(di) (di) (ai '(AND (IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md))))
(di)                                                  ; n -- the typed binder lands (IN n NN)
(define sd-ih (dk-landed-1 di))                       ; the induction hypothesis, REST[n]
(define sd-hyps (dk-landed sd-di*))                   ; u, bm, sm and their guards
(define sd-spans-bm (sd-conj (sd-head? 'SPANS) sd-hyps))
(define sd-sub-hyp  (sd-conj (sd-head? 'SUBSET) sd-hyps))
(define sd-u  (list-ref sd-spans-bm 3))
(define sd-bm (list-ref sd-spans-bm 4))
(define sd-sm (cadr sd-sub-hyp))
(define sd-u2  (list 'BLOCK sd-u 'n 1))               ; u' = u_1..u_n
(define sd-bm2 (list 'SPAN 'md 'n sd-u2))             ; bm' = span(u')
(define sd-sm2 (list 'INTERSECTION sd-sm sd-bm2))     ; sm' = sm ^ bm'
(define sd-S   (list 'LASTCOEFF-SET 'md 'n sd-u sd-sm))

;;; ---- scalar ring, arithmetic, and the truncated data
(fact 'euclidean-ring-is-integral-domain '(SCAL md))
(fact 'integral-domain-is-commutative-ring '(SCAL md))
(fact 'commutative-ring-is-ring '(SCAL md))
(fact 'nn-one-in) (fact 'nn-le-refl 1) (fact 'one-in-interval-1)
(fact 'nn-succ-closed 'n) (fact 'nn-le-succ 'n)
(fact 'nn-one-le-succ 'n) (fact 'nn-le-refl '(succ n))
(fact 'interval-mem-intro 1 '(succ n) '(succ n))      ; succ n in [1,succ n]
(fact 'submodule-subset 'md sd-sm)                    ; SUBSET sm (VEC md)
(fact 'block-type '(succ n) 1 '(VEC md) sd-u 'n 1)    ; u' : MAT n 1 (VEC md)
(fact 'span-is-submodule 'md 'n sd-u2)                ; IS-SUBMODULE md bm'
(fact 'spans-span 'md 'n sd-u2)                       ; SPANS md n u' bm'
(fact 'submodule-intersection 'md sd-sm sd-bm2)       ; IS-SUBMODULE md sm'
(sd-cut! (list 'SUBSET sd-sm2 sd-bm2)                 ; SUBSET sm' bm'
  (lambda ()
    (mac 'subset-def) (di)
    (let ((xx (cadr (sd-goal))))
      (ie (list 'IN xx sd-sm2) 2) (ass))))

;;; ---- the induction hypothesis at (u', bm', sm'):  k' <= n and w' spanning sm'
(define sd-ih-conjs
  (dk-split! (sd-inst-detach! (sd-inst-detach! (sd-inst-detach! sd-ih sd-u2) sd-bm2) sd-sm2)))
(define sd-k2 (sd-eigen-of (sd-conj (sd-typed-in 'NN) sd-ih-conjs)))
(define sd-w2-conjs (dk-split! (sd-conj (sd-head? 'FORSOME) sd-ih-conjs)))
(define sd-w2 (sd-eigen-of (sd-conj sd-in-mat? sd-w2-conjs)))
(define sd-spans-w2 (sd-conj (sd-head? 'SPANS) sd-w2-conjs))   ; SPANS md k' w' sm'

;;; ---- the last-coefficient ideal and its generator b = the last coeff of x0 in sm
(fact 'lastcoeff-set-is-ideal 'md 'n sd-u sd-sm)      ; IS-IDEAL (SCAL md) S
(define sd-gen-conjs
  (dk-split! (dk-fact! 'euclidean-ideal-has-generator '(SCAL md) sd-S)))
(define sd-b-in-S (sd-conj (sd-typed-in sd-S) sd-gen-conjs))
(define sd-b (sd-eigen-of sd-b-in-S))
(define sd-gen (sd-conj (sd-head? 'FORALL) sd-gen-conjs))       ; a in S => a in (b)
(define sd-b-conjs                                              ; unfold b in S
  (dk-split! (dk-landed-1 (lambda () (mac-h 'lastcoeff-set-membership sd-b-in-S)))))
(define sd-c0-conjs (dk-split! (sd-conj (sd-head? 'FORSOME) sd-b-conjs)))
(define sd-c0 (sd-eigen-of (sd-conj sd-in-mat? sd-c0-conjs)))
(define sd-x0 (list 'ENTRY (list 'MATACT 'md sd-c0 sd-u) 1 1))  ; x0 = c0.u, in sm
(fact 'subset-mem-fwd sd-sm '(VEC md) sd-x0)                    ; x0 in VEC md

;;; ---- the witness: k = succ k', w = [w', x0]
(define sd-w (list 'SNOC-COL sd-w2 sd-k2 sd-x0))
(fact 'snoc-col-type '(VEC md) sd-k2 sd-w2 sd-x0)     ; w : MAT (succ k') 1 (VEC md)
(fact 'nn-succ-closed sd-k2)
(fact 'nn-succ-mono sd-k2 'n)                         ; k' <= n  =>  succ k' <= succ n

(ew (list 'succ sd-k2))
(sd-branch! di
  (cons (sd-head? 'AND)                               ; succ k' in NN and <= succ n
        (lambda () (sd-branch! di
                     (cons (sd-head? 'IN) (lambda () (ass)))
                     (cons (sd-head? '<=) (lambda () (ass))))))
  (cons (sd-head? 'FORSOME)
    (lambda ()
      (ew sd-w)
      (sd-branch! di
        (cons (sd-head? 'IN) (lambda () (ass)))       ; w : MAT (succ k') 1 (VEC md)
        (cons (sd-head? 'SPANS)
          (lambda ()
            (mac 'SPANS)
            (sd-branch! di

              ;; (1) every entry of w = [w', x0] lies in sm
              (cons (lambda (g) (not (sd-mentions? g 'FORSOME)))
                (lambda ()
                  (sd-di*)
                  (let* ((jj (caddr (cadr (sd-goal))))          ; goal (IN (ENTRY w j 1) sm)
                         (ivl (list 'succ sd-k2)))
                    (fact 'interval-elt-in-nn 1 ivl jj)
                    (fact 'interval-lo 1 ivl jj) (fact 'interval-hi 1 ivl jj)
                    (fact 'nn-le-succ-cases sd-k2 jj)           ; j <= k'  or  j = succ k'
                    (sd-cases! (sd-find (sd-head? 'OR))
                      (cons (list '<= jj sd-k2)                 ; an entry of w'
                        (lambda ()
                          (fact 'interval-mem-intro 1 sd-k2 jj)
                          (fact 'entry-of-snoc-col sd-w2 sd-k2 sd-x0 jj)
                          (subst (list '= (list 'ENTRY sd-w jj 1) (list 'ENTRY sd-w2 jj 1)))
                          (let* ((w2c (dk-split! (dk-landed-1
                                        (lambda () (mac-h 'SPANS sd-spans-w2)))))
                                 (ents (sd-conj (lambda (a) (not (sd-mentions? a 'FORSOME))) w2c)))
                            (sd-inst-detach! ents jj)           ; w'_j in sm'
                            (ie (list 'IN (list 'ENTRY sd-w2 jj 1) sd-sm2) 1)
                            (ass))))
                      (cons (list '= jj (list 'succ sd-k2))     ; the appended x0
                        (lambda ()
                          (fact 'snoc-col-last sd-w2 sd-k2 sd-x0)
                          (subst (list '= jj (list 'succ sd-k2)))
                          (subst (list '= (list 'ENTRY sd-w (list 'succ sd-k2) 1) sd-x0))
                          (ass)))))))

              ;; (2) every x in sm is a combination of [w', x0]
              (cons (sd-mentions-pred 'FORSOME)
                (lambda ()
                  (sd-di*)
                  (let ((xx (sd-eigen-of (sd-find (sd-typed-in sd-sm)))))
                    (fact 'subset-mem-fwd sd-sm sd-bm xx)       ; x in bm
                    ;; x = c.u, with last coefficient r
                    (let* ((bmc (dk-split! (dk-landed-1 (lambda () (mac-h 'SPANS sd-spans-bm)))))
                           (combo (sd-conj (sd-mentions-pred 'FORSOME) bmc))
                           (cconjs (dk-split! (sd-inst-detach! combo xx)))
                           (cc (sd-eigen-of (sd-conj sd-in-mat? cconjs)))
                           (xeq (sd-conj (sd-head? '=) cconjs))  ; x = c.u
                           (cu (caddr xeq))
                           (rr (list 'ENTRY cc 1 '(succ n))))
                      (fact 'entry-in-carrier 1 '(succ n) '(CARR (SCAL md)) cc 1 '(succ n))
                      (fact 'eq-sym xx cu)                       ; c.u = x
                      ;; r lies in the last-coefficient ideal S, hence r = q.b
                      (sd-cut! (list 'IN rr sd-S)
                        (lambda ()
                          (mac 'lastcoeff-set-membership)
                          (sd-branch! di
                            (cons (sd-head? 'IN) (lambda () (ass)))
                            (cons (sd-head? 'FORSOME)
                              (lambda ()
                                (ew cc)
                                (sd-branch! di
                                  (cons (sd-head? 'IN) (lambda () (ass)))
                                  (cons (sd-head? 'AND)
                                    (lambda ()
                                      (sd-branch! di
                                        (cons (sd-head? '=) (lambda () (rfl)))
                                        (cons (sd-head? 'IN)
                                          (lambda ()
                                            (subst (list '= cu xx)) (ass))))))))))))
                      (let* ((rinb (sd-inst-detach! sd-gen rr))   ; r in (b) -- OUTSIDE the
                             (pic (dk-split! (dk-landed-1          ; thunk below, or its
                                    (lambda () (mac-h 'principal-ideal-membership rinb)))))
                             (qconjs (dk-split! (sd-conj (sd-head? 'FORSOME) pic)))
                             (qq (sd-eigen-of (sd-conj (sd-typed-in '(CARR (SCAL md))) qconjs)))
                             (nq (list '(NEG (SCAL md)) qq)))
                        ;; y = x + (-q).x0 : in bm' by descent-remainder, in sm by closure
                        (let* ((yc (dk-split! (dk-fact! 'descent-remainder 'md 'n sd-u cc
                                                          sd-c0 qq sd-b)))
                               (yy (sd-eigen-of (sd-conj (sd-typed-in sd-bm2) yc)))
                               ;; descent-remainder speaks of c.u, not of the eigen x:
                               ;; y = c.u + (-q).x0  and  c.u = y + q.x0
                               (yeq (sd-conj (lambda (a) (and (pair? a) (eq? (car a) '=)
                                                              (equal? (cadr a) yy))) yc))
                               (xeq2 (sd-conj (lambda (a) (and (pair? a) (eq? (car a) '=)
                                                               (equal? (cadr a) cu))) yc)))
                          (fact 'ring-neg-in-carr '(SCAL md) qq)
                          (fact 'submodule-act-closed 'md sd-sm nq sd-x0)
                          (fact 'submodule-vadd-closed 'md sd-sm xx
                                (list '(ACT md) nq sd-x0))
                          (sd-cut! (list 'IN yy sd-sm)                  ; y = x + (-q).x0 in sm
                            (lambda () (subst yeq) (subst (list '= cu xx)) (ass)))
                          (sd-cut! (list 'IN yy sd-sm2) sd-ii-ass!)
                          ;; y = c'.w' by the IH, so x = y + q.x0 = (c',q).[w',x0]
                          (let* ((w2c (dk-split! (dk-landed-1
                                        (lambda () (mac-h 'SPANS sd-spans-w2)))))
                                 (combo2 (sd-conj (sd-mentions-pred 'FORSOME) w2c))
                                 (cpconjs (dk-split! (sd-inst-detach! combo2 yy)))
                                 (cp (sd-eigen-of (sd-conj sd-in-mat? cpconjs)))
                                 (yeq3 (sd-conj (sd-head? '=) cpconjs))   ; y = c'.w'
                                 (cpw (caddr yeq3)))
                            (fact 'snoc-row-type '(CARR (SCAL md)) sd-k2 cp qq)
                            (ew (list 'SNOC-ROW cp sd-k2 qq))
                            (sd-branch! di
                              (cons (sd-head? 'IN) (lambda () (ass)))
                              (cons (sd-head? '=)
                                (lambda ()
                                  (subst xeq)                   ; x -> c.u (xeq2's phrasing)
                                  (fact 'matact-snoc 'md sd-k2 cp sd-w2 qq sd-x0)
                                  (subst (list '= (list 'ENTRY (list 'MATACT 'md
                                                    (list 'SNOC-ROW cp sd-k2 qq) sd-w) 1 1)
                                               (list '(VADD md) cpw
                                                     (list '(ACT md) qq sd-x0))))
                                  (fact 'eq-sym yy cpw)
                                  (subst (list '= cpw yy))      ; c'.w' -> y
                                  (ass))))))))))))))))))
(qed 'spans-fg-step)
(topic! 'spans-fg-step 'algebra)


;;; ================= assembly =================
(sp (make-wff `(FORALL md (IMPLIES (AND (IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md)))
                 (FORALL n (IMPLIES (IN n NN) ,(sd-rest 'n)))))))
(di) (di)                                             ; md, (AND ...) whole in context
(ni)
;; ni left two leaves: base REST[0] (mentions 0, not (succ n)) and the step.
(for-each (lambda (l)
            (let ((g (wff-formula (sequent-node-assertion l))))
              (sd-foc! l)
              (if (sd-mentions? g '(succ n))
                  (begin (fact 'spans-fg-step 'md) (ass))
                  (begin (fact 'spans-fg-base 'md) (ass)))))
          (proof-leaves))
(qed 'spans-submodule-fg)
(topic! 'spans-submodule-fg 'algebra)


