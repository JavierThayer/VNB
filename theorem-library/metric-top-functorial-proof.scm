;;; metric-top-functorial-proof.scm -- the Met -> Top functor acts on morphisms.
;;;
;;;   metric-top-functorial :  IS-HOM-METRIC-SPACE(a, b, f)
;;;                              => IS-HOM-TOP-SPACE(METRIC-TOP a, METRIC-TOP b, f)
;;;
;;; the FUNCTORIALITY obligation of the constructed functor METRIC-TOP.  Unfolded,
;;; it is: eps-delta continuity implies the preimage of every open set is open --
;;; the theorem the functor exists to force, and a theorem only because
;;; METRIC-SPACE's morphisms are its CONTINUOUS maps (metric-continuity.scm).  Over
;;; the generated isometry hom it would have degenerated into "an isometry is
;;; continuous", true and empty.
;;;
;;; The content is continuous-implies-open-preimage (metric-open-sets.scm, itself
;;; machine-proven in calculus/prop-3-15-proof.scm).  What is left is bookkeeping,
;;; and ONE real obstacle:
;;;
;;;   PREIMAGE(METRIC-TOP a, f, u)  vs  PREIMAGE(a, f, u)
;;;
;;; The support speaks of the metric space; the goal, of its topology.  The two
;;; terms are equal -- PREIMAGE(s,f,V) is SEP over PTS(s), and PTS(METRIC-TOP a) is
;;; PTS(a) -- but the functor's argument sits INSIDE the functoid, where the
;;; projection macete cannot reach it until the functoid is unfolded.  So the
;;; equation is cut, proved by unfolding PREIMAGE on both sides and projecting, and
;;; substituted in.  (`mac' unfolds a functoid in the GOAL; mac-h cannot do it in an
;;; assumption -- the def-functoid/mac-h trap -- which is why it is done this way
;;; round.)

(define (mf-goal-of l) (expression->string (wff-formula (sequent-node-assertion l))))

(define (mf-dump!)
  (display "\n;; FRONTIER:\n")
  (for-each (lambda (l) (display ";;   ") (display (mf-goal-of l)) (newline))
            (proof-leaves)))

(define (mf-focus! str)
  (let ((hits (filter (lambda (l) (string-search-forward str (mf-goal-of l) 0))
                      (proof-leaves))))
    (cond ((null? hits) (mf-dump!) (error "mf-focus!: no leaf containing" str))
          ((pair? (cdr hits)) (mf-dump!) (error "mf-focus!: ambiguous" str))
          (else (dk-focus! (car hits))))))

(define (mf-focus-eq! str)
  (let ((hits (filter (lambda (l) (string=? str (mf-goal-of l))) (proof-leaves))))
    (cond ((null? hits) (mf-dump!) (error "mf-focus-eq!: no leaf" str))
          ((pair? (cdr hits)) (mf-dump!) (error "mf-focus-eq!: ambiguous" str))
          (else (dk-focus! (car hits))))))

(define (mf-longest!)
  (let loop ((ls (proof-leaves)) (best #f) (n -1))
    (cond ((null? ls) (if best (dk-focus! best) (error "mf-longest!: no leaves")))
          ((> (string-length (mf-goal-of (car ls))) n)
           (loop (cdr ls) (car ls) (string-length (mf-goal-of (car ls)))))
          (else (loop (cdr ls) best n)))))

(define mf-hom  '(IS-HOM-METRIC-SPACE a b f))
(define mf-ims  '(IS-METRIC-SPACE a))
(define mf-sepa '(SEP u (POWER (PTS a)) (IS-OPEN a u)))       ; OPENS(METRIC-TOP a)
(define mf-sepb '(SEP u (POWER (PTS b)) (IS-OPEN b u)))       ; OPENS(METRIC-TOP b)

;;; --- set up ---------------------------------------------------------------

(sp (functor-obligation 'metric-top-functorial))

(di)                          ; `di' peels ALL the leading foralls at once: a, b, f
(di)                          ; IS-HOM-METRIC-SPACE(a,b,f) into the context

;;; Unfold the source hom: IS-METRIC-SPACE(a), IS-METRIC-SPACE(b), the typing of f,
;;; and IS-CONTINUOUS(a,b,f) -- the last is the whole content of the hypothesis.
(dk-split! (car (dk-landed (lambda () (mac-h 'is-hom-metric-space-def mf-hom)))))

;;; PTS(a) in SET, for sep-set below.  mac-h REPLACES what it unfolds and every
;;; `fact' here is guarded on IS-METRIC-SPACE(a), so cut the guard back first.
(define mf-conj (car (dk-landed (lambda () (mac-h 'is-metric-space mf-ims)))))
(cut mf-ims)
(mf-focus-eq! "is-metric-space(a)")
(mac 'is-metric-space)
(ass)
(mf-longest!)
(dk-split! mf-conj)           ; lands PTS(a) in SET, the DIST typing, is-metric(...)

(mac 'is-hom-top-space-def)       ; the four conjuncts of the target hom
(slot 'pts)                   ; pts(METRIC-TOP a), pts(METRIC-TOP b) -> pts(a), pts(b)
(slot 'opens)                 ; opens(METRIC-TOP _) -> the separations

(mf-longest!) (di)
(mf-longest!) (di)
(mf-longest!) (di)

;;; --- 1, 2. the two objects are topological spaces -------------------------
;;; Exactly what metric-top-is-top-space says.

(mf-focus! "is-top-space(metric-top(a))")
(fact 'metric-top-is-top-space 'a)
(ass)

(mf-focus! "is-top-space(metric-top(b))")
(fact 'metric-top-is-top-space 'b)
(ass)

;;; --- 3. f is still a map of the underlying sets ---------------------------
;;; `slot' already reduced pts(METRIC-TOP _) to pts(_), so this IS the typing
;;; conjunct of the source hom, in context.

(mf-focus! "f in fun(pts(a), pts(b))")
(ass)

;;; --- 4. preimages of opens are open ---------------------------------------

(mf-focus! "preimage(metric-top(a), f, u)")
(di) (di)
(sep-me `(IN u ,mf-sepb))     ; u in POWER(PTS b), and IS-OPEN(b, u)

;;; THE OBSTACLE, DISSOLVED.  PREIMAGE reads its structure argument only through
;;; PTS, and METRIC-TOP carries PTS across on the nose -- so the functor is
;;; INVISIBLE to the preimage, and functor-invariance.scm proved it, once, for
;;; every r:
;;;
;;;     metric-top@preimage :  PREIMAGE(METRIC-TOP r, f, V) == PREIMAGE(r, f, V)
;;;
;;; It is a `==' (quasi-equality), so it is unconditional -- no metric-space guard,
;;; no sethood of the separation, no definedness owed.  And `macete-equivalence?'
;;; accepts `==', so it rewrites by name.  This replaced a nine-line detour: cut
;;; the `=' equation, cut the SEP's sethood to satisfy rfl's definedness guard,
;;; unfold, project, subst.
(mac 'metric-top@preimage)

(sep-mi)

;; 4a: the preimage lies in POWER(PTS a) -- a set, whose members are points of a.
(mf-focus! "preimage(a, f, u) in power(")
(mac 'power-set-membership)
(di)
(mf-focus! "preimage(a, f, u) in set")
(mac 'preimage)      ; a SEP over PTS(a) ...
(sep-set)            ; ... is a set, because PTS(a) is
(ass)
(mf-focus! "z in preimage(a, f, u)")
(di) (di)
;; mac-h cannot unfold a def-functoid in an assumption -- but preimage-membership
;; IS an installed IFF, so it can rewrite one.
(dk-split! (car (dk-landed (lambda () (mac-h 'preimage-membership '(IN z (PREIMAGE a f u)))))))
(ass)

;; 4b: the preimage is OPEN -- continuity, which is what the source hom asserts.
(mf-focus! "is-open(a, preimage(a, f, u))")
(fact 'continuous-implies-open-preimage 'a 'b 'f 'u)
(ass)

(qed 'metric-top-functorial)
