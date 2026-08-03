;;; metric-top-proof.scm -- the metric open sets form a topology.
;;;
;;;   metric-top-is-top-space :  IS-METRIC-SPACE(md) => IS-TOP-SPACE(METRIC-TOP md)
;;;
;;; the TYPING obligation of the constructed functor METRIC-TOP (top-space.scm).
;;; def-constructed-functor asserts nothing -- a functor you have not proved is a
;;; functor you do not have -- and functor-obligation-audit reports this until it
;;; is a theorem.
;;;
;;; The MATHEMATICS is entirely in metric-open-sets.scm: empty-is-open,
;;; carrier-is-open, inter-of-opens-open, union-of-opens-open.  What is left here
;;; is IS-TOP-SPACE's seven conjuncts over the separation
;;;
;;;     OPENS(METRIC-TOP md)  =  { u in POWER(PTS md) : IS-OPEN(md, u) }
;;;
;;; reached by `slot': def-constructed-functor precomputed its object map's
;;; projections, so the constructed TUPLE never enters the goal.  (By hand it
;;; would: firing the accessor macete rewrites EVERY occurrence, including the
;;; PTS(md) INSIDE the tuple, and the goal collapses into an NTH form that no
;;; support matches.  See install-functor-projections!, structures.scm.)

;;; --- focus helpers.  A focus helper that misses must ERROR, never return #f and
;;; leave focus put: that hides every later command in the wrong branch.

(define (mt-goal-of l) (expression->string (wff-formula (sequent-node-assertion l))))

(define (mt-dump!)
  (display "\n;; FRONTIER:\n")
  (for-each (lambda (l) (display ";;   ") (display (mt-goal-of l)) (newline))
            (proof-leaves)))

(define (mt-focus! str)                 ; the UNIQUE frontier leaf whose goal contains STR
  (let ((hits (filter (lambda (l) (string-search-forward str (mt-goal-of l) 0))
                      (proof-leaves))))
    (cond ((null? hits) (mt-dump!) (error "mt-focus!: no leaf containing" str))
          ((pair? (cdr hits)) (mt-dump!) (error "mt-focus!: ambiguous" str))
          (else (dk-focus! (car hits))))))

;;; Where a goal alone does not discriminate, a CONTEXT formula does (CLAUDE.md:
;;; never navigate by goal shape alone).
(define (mt-focus-ctx! goal-str ctx-str)
  (let ((hits (filter
                (lambda (l)
                  (and (string-search-forward goal-str (mt-goal-of l) 0)
                       (there-exists?
                         (sequent-node-assumptions l)
                         (lambda (a)
                           (string-search-forward
                             ctx-str (expression->string (wff-formula a)) 0)))))
                (proof-leaves))))
    (cond ((null? hits) (mt-dump!) (error "mt-focus-ctx!: no leaf" goal-str ctx-str))
          ((pair? (cdr hits)) (mt-dump!) (error "mt-focus-ctx!: ambiguous" goal-str ctx-str))
          (else (dk-focus! (car hits))))))

(define (mt-focus-eq! str)              ; goal EXACTLY str -- "is-open(md, u)" is a
  (let ((hits (filter (lambda (l) (string=? str (mt-goal-of l)))   ; SUBSTRING of the
                      (proof-leaves))))                            ; separation's printout
    (cond ((null? hits) (mt-dump!) (error "mt-focus-eq!: no leaf" str))
          ((pair? (cdr hits)) (mt-dump!) (error "mt-focus-eq!: ambiguous" str))
          (else (dk-focus! (car hits))))))

(define (mt-longest!)                   ; the leaf with the longest goal = the unpeeled rest
  (let loop ((ls (proof-leaves)) (best #f) (n -1))
    (cond ((null? ls) (if best (dk-focus! best) (error "mt-longest!: no leaves")))
          ((> (string-length (mt-goal-of (car ls))) n)
           (loop (cdr ls) (car ls) (string-length (mt-goal-of (car ls)))))
          (else (loop (cdr ls) best n)))))

(define mt-ims  '(IS-METRIC-SPACE md))
(define mt-sep  '(SEP u (POWER (PTS md)) (IS-OPEN md u)))
;; The identity family, indexed BY fam -- not by the SEP of all opens.  fam is
;; the domain the family is actually used at (union-of-opens-open puts no typing
;; hypothesis on g at all; it applies it at every i in the index class), and it
;; is the domain that makes the two beta steps below licensed: inside
;; BIG-UNION i fam ((j_ |-> j_) i) the binder i is in fam on the nose, whereas
;; membership in the SEP is only reachable through subset-mem-fwd, which no
;; reduction under a binder can perform.
(define mt-id   '(VNB-LAMBDA j_ fam j_))

;;; --- the typing facts, landed ONCE at the top so every branch inherits them.
;;;
;;; mac-h REPLACES the assumption it unfolds, and every `fact' below is guarded on
;;; IS-METRIC-SPACE(md) -- so the guard is CUT back in before it is unfolded away.
;;; (A cut of a formula already in context up to alpha is a silent self-loop; this
;;; one is not in context, mac-h having just consumed it.)

;;; First, the underlying fact as a named theorem: the metric opens form a topology.
;;; (It used to be METRIC-TOP's typing obligation; since the functor retargeted to
;;; METRIZABLE-TOP-SPACE, that obligation is now the wrapper at the foot of this file,
;;; and this is the lemma it cites.)
(sp (make-wff '(FORALL md (IMPLIES (IS-METRIC-SPACE md) (IS-TOP-SPACE (METRIC-TOP md))))))

(di)                          ; forall md
(di)                          ; IS-METRIC-SPACE(md) into the context

(define mt-conj (car (dk-landed (lambda () (mac-h 'is-metric-space mt-ims)))))

(cut mt-ims)                  ; the side goal IS the guard, and the conjunction proves it
(mt-focus! "is-metric-space(md)")
(mac 'is-metric-space)
(ass)

(mt-longest!)                 ; back to the main line
(dk-split! mt-conj)           ; lands PTS(md) in SET, the DIST typing, is-metric(...)
(fact 'power-set '(PTS md))   ; lands POWER(PTS md) in SET -- sep-set will want it

(mac 'is-top-space)           ; the seven conjuncts
(slot 'pts)                   ; pts(METRIC-TOP md)   -> pts(md)
(slot 'opens)                 ; opens(METRIC-TOP md) -> the separation

;;; `di' on an AND goal peels ONE conjunct and takes focus with it, so the
;;; unpeeled remainder -- always the longest goal on the frontier -- is re-focused
;;; each time.  Six peels, seven conjuncts.
(mt-longest!) (di)
(mt-longest!) (di)
(mt-longest!) (di)
(mt-longest!) (di)
(mt-longest!) (di)
(mt-longest!) (di)

;;; --- 1. length(METRIC-TOP md) = 2 -----------------------------------------
;;; The one conjunct that wants the tuple: unfold the functoid HERE, where no
;;; other occurrence of PTS(md) is around for the reduction to disturb.

(mt-focus! "length(metric-top")
(mac 'metric-top)
(len-r)
(rfl)

;;; --- 2. PTS(md) in SET ----------------------------------------------------

(mt-focus! "pts(md) in set")
(ass)

;;; --- 3. the separation lies in POWER(POWER(PTS md)) -----------------------
;;; power-set-membership: x in POWER(a) iff x is a set and every member of x is
;;; in a.  Sethood is sep-set; membership gives POWER(PTS md) back by sep-me.

(mt-focus! "} in power(power(")
(mac 'power-set-membership)
(di)
(mt-focus! "} in set")
(sep-set)
(mt-focus! "power(pts(md)) in set")
(ass)
(mt-focus! "z in power(pts(md))")
(di) (di)
(sep-me `(IN z ,mt-sep))
(ass)

;;; --- 4. EMPTY-SET is open -------------------------------------------------

(mt-focus! "empty-set in {")
(sep-mi)
;; 4a: EMPTY-SET in POWER(PTS md) -- a set, with no members to check.
(mt-focus! "empty-set in power(")
(mac 'power-set-membership)
(di)
(mt-focus! "empty-set in set")
(fact 'empty-set-is-set)
(ass)
(mt-focus! "in empty-set")
(di) (di)
(fact 'empty-set-has-no-members 'z)   ; NOT (z in EMPTY-SET), against the hypothesis
(pbc)                                 ; goal FALSITY
(ai '(NOT (IN z EMPTY-SET)))          ; not-elim: its body is in context, so FALSITY closes
;; 4b: IS-OPEN(md, EMPTY-SET)
(mt-focus! "is-open(md, empty-set)")
(fact 'empty-is-open 'md)
(ass)

;;; --- 5. PTS(md) is open ---------------------------------------------------

(mt-focus! "pts(md) in {")
(sep-mi)
;; 5a: PTS(md) in POWER(PTS md) -- a set, and a subset of itself.
;; The sethood half needs no work: dg-post! hash-conses sequent nodes by assertion
;; (up to alpha) and context, so this branch's "PTS(md) in SET" IS the node
;; conjunct 2 already closed.  It is not on the frontier, and looking for it would
;; (rightly) error.
(mt-focus! "pts(md) in power(")
(mac 'power-set-membership)
(di)
(mt-focus! "z in pts(md)")
(di) (di)
(ass)
;; 5b: IS-OPEN(md, PTS md)
(mt-focus! "is-open(md, pts(md))")
(fact 'carrier-is-open 'md)
(ass)

;;; --- 6. binary intersections ----------------------------------------------

(mt-focus! "intersection(u, v) in {")
(di) (di) (di) (di)
(sep-me `(IN u ,mt-sep))
(sep-me `(IN v ,mt-sep))
(sep-mi)
;; 6a: INTERSECTION(u,v) in POWER(PTS md) -- a set, because u is ...
(mt-focus! "intersection(u, v) in power(")
(mac 'power-set-membership)
(di)
(mt-focus! "intersection(u, v) in set")
(fact 'membership-implies-sethood 'u '(POWER (PTS md)))
(cut '(OR (IN u SET) (IN v SET)))     ; intersection-set-closure wants the disjunction
(mt-focus! "u in set or v in set")
(oi-l)
(ass)
(mt-focus! "intersection(u, v) in set")
(fact 'intersection-set-closure 'u 'v)
(ass)
;; ... and its members are members of u, hence of PTS(md).
(mt-focus! "z in intersection(u, v)")
(di) (di)
(ie '(IN z (INTERSECTION u v)) 1)
(dk-split! (car (dk-landed (lambda () (mac-h 'power-set-membership '(IN u (POWER (PTS md))))))))
(inst+ '(FORALL z (IMPLIES (IN z u) (IN z (PTS md)))) 'z)   ; in-context FORALL: inst+, not fact
(ass)
;; 6b: IS-OPEN(md, INTERSECTION(u,v)).  `fact' will not split a CONJUNCTIVE
;; antecedent, and inter-of-opens-open's is one -- so cut it and prove both halves.
(mt-focus! "is-open(md, intersection(")
(cut '(AND (IS-OPEN md u) (IS-OPEN md v)))
(mt-focus! "is-open(md, u) and is-open(md, v)")
(di)
(mt-focus-eq! "is-open(md, u)")
(ass)
(mt-focus-eq! "is-open(md, v)")
(ass)
(mt-focus! "is-open(md, intersection(")
(fact 'inter-of-opens-open 'md 'u 'v)
(ass)

;;; --- 7. arbitrary unions --------------------------------------------------
;;;
;;; union-of-opens-open is stated for an INDEXED family -- (BIG-UNION i A (g i)),
;;; g a function -- while the TOP-SPACE law unions a SUBFAMILY directly,
;;; (BIG-UNION u fam u).  That IS the identity family, and the gap is pure syntax:
;;; no first-order match sends (g i) to i.  So the goal is normalised to the
;;; theorem's shape -- cut the identity-family equation, prove it by beta, subst
;;; it in.  (A `lam-b' that reduced a cited ASSUMPTION -- lam-b's mac-h -- would
;;; do this with no detour at all.  Worth having.)

(mt-focus! "big-union(u, fam, u) in {")
(di) (di)

;;; The union's SETHOOD is landed BEFORE the split, because both halves want it:
;;; sep-mi's POWER branch as a conjunct, and -- less obviously -- `rfl', whose
;;; definedness guard closes t = t only for a term that is syntactically total or
;;; carries an (IN t _) in context.  VNB's `=' is partial: t = t IS the definedness
;;; assertion, so a BIG-UNION of unknown sethood is not reflexive.
;;;
;;; bu-set asks two things: fam is a set, and so is each of its members.  fam is a
;;; subclass of the topology, which is a set (sep-set) -- hence a set, by the NBG
;;; principle the library did not have until this proof wanted it
;;; (subclass-of-set-is-set, set-basics.scm).  Members of fam lie in POWER(PTS md),
;;; hence are sets by membership-implies-sethood.

(cut '(IN (BIG-UNION u fam u) SET))
(mt-focus! "big-union(u, fam, u) in set")
(bu-set)
(mt-focus! "fam in set")
(cut `(IN ,mt-sep SET))
(mt-focus! "} in set")
(sep-set)
(mt-focus! "power(pts(md)) in set")
(ass)
(mt-focus! "fam in set")
(fact 'subclass-of-set-is-set 'fam mt-sep)
(ass)
;; the member obligation binds a MACHINE-CHOSEN eigenvariable (u_852, ...), read
;; off the assumption `di' lands -- never guessed.
(mt-focus-ctx! "in set" "fam subset")
(define mt-w (cadr (dk-landed-1 (lambda () (di) (di)))))
(fact 'subset-mem-fwd 'fam mt-sep mt-w)      ; fam subset SEP, w in fam => w in SEP
(sep-me `(IN ,mt-w ,mt-sep))
(fact 'membership-implies-sethood mt-w '(POWER (PTS md)))
(ass)

;;; ... and now the membership itself.
(mt-focus! "big-union(u, fam, u) in {")
(sep-mi)

;; 7a: the union lies in POWER(PTS md) -- a set, and each of its points comes from
;; some member of fam, which is a subset of PTS(md).
(mt-focus! "big-union(u, fam, u) in power(")
(mac 'power-set-membership)
(di)
(mt-focus! "big-union(u, fam, u) in set")
(ass)
(mt-focus! "z in big-union(")
(di) (di)
(define mt-u (cadr (dk-landed-find (lambda () (bu-me '(IN z (BIG-UNION u fam u))))
                                   (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                    (eq? (caddr f) 'fam))))))
(fact 'subset-mem-fwd 'fam mt-sep mt-u)      ; the member of fam that z came from
(sep-me `(IN ,mt-u ,mt-sep))
(dk-split! (car (dk-landed (lambda () (mac-h 'power-set-membership `(IN ,mt-u (POWER (PTS md))))))))
(inst+ `(FORALL z (IMPLIES (IN z ,mt-u) (IN z (PTS md)))) 'z)
(ass)

;; 7b: IS-OPEN(md, BIG-UNION u fam u), via the identity family.
(mt-focus! "is-open(md, big-union(")
(cut `(FORALL i_ (IMPLIES (IN i_ fam) (IS-OPEN md (,mt-id i_)))))
(mt-focus! "forall([i_ in fam]")
(di) (di)
(lam-b)                                      ; licensed: (IN i_ fam) is in context
(fact 'subset-mem-fwd 'fam mt-sep 'i_)
(sep-me `(IN i_ ,mt-sep))
(ass)
(mt-focus! "is-open(md, big-union(u, fam, u))")
;; `fact' at the identity family lands the APPLIED lambda in the CONTEXT:
;;     is-open(md, big-union(i, fam, (j_ |-> j_)(i)))
;; where the goal-side `lam-b' cannot reach it.  lam-b-h -- lam-b's hypothesis-side
;; twin, what mac-h is to mac -- reduces it in place, and `ass' closes on the
;; alpha-equivalent result.  (This replaced a cut-the-beta-equation-and-subst
;; detour, which is what a missing tactic costs you.)
(define mt-uoo (dk-fact! 'union-of-opens-open 'md 'fam mt-id))
(lam-b-h mt-uoo)
(ass)

(qed 'metric-top-is-top-space)

;;; -----------------------------------------------------------------------
;;; The functor's TYPING obligation: METRIC-TOP(md) is a METRIZABLE-TOP-SPACE.
;;; IS-METRIZABLE-TOP-SPACE folds (same-shape-as TOP-SPACE) to
;;;   IS-TOP-SPACE(s) AND (exists md_. is-metric-space(md_) and s == metric-top(md_)).
;;; The first conjunct is the theorem above; the second holds with md itself the
;;; witness -- METRIC-TOP(md) is on the nose the metric topology of md.
(sp (functor-obligation 'metric-top-is-metrizable-top-space))
(di)                                  ; forall md
(di)                                  ; is-metric-space(md)
(mac 'is-metrizable-top-space-def)    ; refinement: the macete is the -def axiom name
(di)                                  ; split the AND
(mt-focus! "is-top-space(metric-top")
(fact 'metric-top-is-top-space 'md)
(ass)
(mt-focus! "forsome")
(ew 'md)                              ; witness: md
(di)                                  ; split  is-metric-space(md)  AND  == 
(mt-focus! "is-metric-space(md)")
(ass)
(mt-focus! "metric-top(md) ==")
(mac 'metric-top)                     ; both sides become [pts(md), {u : is-open(md,u)}]
(qrfl)
(qed 'metric-top-is-metrizable-top-space)
