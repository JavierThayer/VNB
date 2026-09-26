;;; theorem-library/rake-finsum-welldef.scm -- rake batch N (2026-09-17), part 2 of 2
;;; (part 1 is theorem-library/rake-inverse-bij.scm, which this file needs).
;;;
;;; ENUMERATION INDEPENDENCE -- the floor under every finsum bill.  All of it is
;;; `modulo 0'.
;;;
;;; RETIRED SUPPORTS (statements copied LITERALLY from their sites):
;;;   sum-ag-permutation-invariance             theorem-library/sum-ag-permutation-invariance.scm:18
;;;   finsum-comm-monoid-permutation-invariance theorem-library/finsum-comm-monoid.scm:49
;;;   finsum-well-defined                       theorem-library/finsum-well-defined.scm:15
;;;   finsum-comm-monoid-well-defined           theorem-library/finsum-comm-monoid.scm:77
;;;
;;; NEW, and the reusable part:
;;;   opr-rearrange-laws             (a*b)*c = (a*c)*b
;;;   sum-ag-type-laws               the fold stays in the carrier
;;;   sum-ag-replace-entry-laws      SUM(g,n)*gp(k) = SUM(gp,n)*g(k) when g = gp off k
;;;   sum-ag-permutation-invariance-laws
;;;   seg-perm-restrict-is-bijection a permutation of OS(succ n) restricted to OS(n)
;;; and two names that finsum-insert.scm also proves (see the integrator note):
;;;   ord-segment-self, sum-ag-segment-congruence
;;;
;;; WHY "-laws".  SUM-AG is defined by NN-recursion out of (OPR s) and (IDEN s)
;;; alone, so permutation invariance is a fact about an operation with four
;;; properties -- identity in the carrier, closure, associativity, commutativity --
;;; and not about a structure PREDICATE.  IS-COMM-MONOID pins a 3-slot tuple and
;;; IS-ABELIAN-GROUP a 4-slot one, neither is an instance of the other, and there
;;; is no view between them (finsum-additive.scm says so), so the abelian-group
;;; and comm-monoid statements would otherwise be two copies of one 400-line
;;; proof.  The four laws are CURRIED, never conjoined, so a forward `fact'
;;; auto-detaches them one at a time.
;;;
;;; THE ARGUMENT, and it is NOT the archived one.  archive/proven-theorems-archive.scm
;;; proves this by splicing the top summand out of the fold (sum-ag-splice-out) and
;;; re-indexing with DELETE-AT + INVERSE-BIJ(DELETE-AT inv K) -- about 1200 lines,
;;; and it bills the eight UNWARRANTED delete-at-*/inverse-bij-* axioms of
;;; structure-library/bijection.scm.  Two observations remove all of that:
;;;
;;;  (1) The combinatorial content is ONE-ENTRY REPLACEMENT, not splicing:
;;;        k in OS(n), g = gp off k  =>  SUM(g,n)*gp(k) = SUM(gp,n)*g(k)
;;;      whose induction peels the TOP index and uses nothing but sum-ag-succ and
;;;      (a*b)*c = (a*c)*b.  No index is ever shifted, so DELETE-AT never appears.
;;;  (2) The induced permutation of OS(n) is phi RE-ROUTED, not phi compressed:
;;;        rho(i) = IF phi(i) = n THEN phi(n) ELSE phi(i),
;;;      a bijection OS(n) -> OS(n) (seg-perm-restrict-is-bijection).  The only
;;;      ordinal facts it needs are "n is not in OS(n)" and "OS(succ n) = OS(n) u {n}".
;;;
;;; The step then reads: let gp be g with the entries at n and phi(n) SWAPPED (an
;;; explicit VNB-LAMBDA on NN, so it is a total family and `lam-t' types it).  The
;;; swap costs one replacement (1); the IH along rho (2) turns SUM(h,n) into
;;; SUM(gp,n); and h(n) = g(phi n) = gp(n) closes the top term.
;;;
;;; finsum-well-defined is then the same permutation, read off the enumerations:
;;; psi = INVERSE-BIJ(enm) o FIN-ENUM(S) is a bijection OS(|S|) -> OS(|S|) with
;;; enm(psi i) = FIN-ENUM(S)(i) (inverse-bij-right), so the two enumerated families
;;; agree pointwise along psi.
;;;
;;; NOT PROVEN, and the obstacle is a MISSING FACT ABOUT CARD, not about sums:
;;; `finsum-reindex' (finsum-additive.scm:236) and `finsum-reindex-ag' (:276) say
;;; SUM over S equals SUM over T along a bijection phi : T -> S.  Both sides are
;;; folds, of lengths CARD(S) and CARD(T), so the statement is only reachable once
;;; CARD(S) = CARD(T) -- and the tree cannot conclude that from a bijection.  CARD
;;; is AXIOMATISED (cardinality.scm's own header says so); `card-finite-bij' runs
;;; the wrong way (cardinal to bijection) and `card-star-bij' (theorem-library/
;;; card-finite.scm:~110) is about the DEFINED cardinal CARD-STAR, which nothing
;;; identifies with CARD.  The route, if someone wants it: compose FIN-ENUM(T)
;;; with phi and with the inverse of FIN-ENUM(S) to get a bijection
;;; OS(|T|) -> OS(|S|), then `pigeonhole-segments-gen' (theorem-library/
;;; pigeonhole-segments.scm, position 218) both ways plus ordinal trichotomy.
;;; That lemma -- "a bijection between finite sets equates their cardinals" --
;;; belongs in the card layer, not here, and it is worth stating on its own.
;;;
;;; CITATIONS (load position, 0-based over load.scm's quoted file names):
;;;   theory.scm / number-systems (primitive): choice-axiom, nn-succ-closed, nn-is-set
;;;   structure-library/ordinals (77, primitive): nn-subset-ord, ord-lt-iff,
;;;     ord-segment-membership, ord-segment-is-set
;;;   structure-library/bijection (81, definitional): bijection-membership-iff
;;;   structure-library/cardinality (82, primitive): card-finite-bij
;;;   structure-library/sequences (92, definitional): sum-ag-zero, sum-ag-succ
;;;   structure-library/finsum (93): the FIN-ENUM / ENUM-FAM / FINSUM unfolds
;;;   theorem-library/equality-basics (148): eq-sym, eq-trans, neq-sym
;;;   theorem-library/ord-segment-nn-succ-proof (153), ord-segment-nn-subset-proof (154):
;;;     ord-segment-nn-succ, ord-segment-nn-subset, ord-segment-zero-no-members
;;;   theorem-library/fun-apply-type-proof (163): fun-apply-type-c
;;;   theorem-library/rake-analysis2 (194): bijection-compose, fun-domain-in-set
;;;   structure-library/subtype-laws (199): abelian-group-is-group, group-assoc,
;;;     group-identity-in, abelian-group-opr-comm
;;;   theorem-library/rake-inverse-bij (NEW, ~200): the four inverse-bij facts,
;;;     fin-enum-is-bijection
;;;   theorem-library/finsum-type-proof (201): group-carrier-closed-opr
;;;   theorem-library/rake-finsum-typing (229): comm-monoid-identity-in-carr,
;;;     comm-monoid-carrier-closed-opr                            -- the LATEST
;;;
;;; LOAD WINDOW [230, 243).  lo = after rake-finsum-typing (229).  hi = before
;;; theorem-library/rake-finsum-laws (243), which needs sum-ag-segment-congruence
;;; out of finsum-insert, and finsum-insert must load AFTER this file (it cites
;;; finsum-well-defined and finsum-comm-monoid-well-defined).  So the order is
;;;     ... rake-finsum-typing (229), THIS FILE, finsum-insert (moved from 155),
;;;     ... interval-card-in-nn, rake-finsum-laws, rake-finsum-laws2 ...
;;;
;;; FOR THE INTEGRATOR.  Four supports to retire, one file to MOVE, three blocks
;;; to delete, and two load.scm slots:
;;;   retire  sum-ag-permutation-invariance             theorem-library/sum-ag-permutation-invariance.scm:18 (+ warrant :27)
;;;   retire  finsum-well-defined                       theorem-library/finsum-well-defined.scm:15 (+ warrant :28)
;;;   retire  finsum-comm-monoid-permutation-invariance theorem-library/finsum-comm-monoid.scm:49 (+ warrant :57)
;;;   retire  finsum-comm-monoid-well-defined           theorem-library/finsum-comm-monoid.scm:77 (+ warrant :89)
;;;   retire  the four INVERSE-BIJ axioms of structure-library/bijection.scm
;;;           (:84 inverse-bij-in-fun, :93 inverse-bij-left, :104 inverse-bij-right,
;;;            :113 inverse-bij-is-bijection) -- part 1 proves all four
;;;   MOVE    theorem-library/finsum-insert from load position 155 to the slot
;;;           immediately AFTER this file.  It cites finsum-well-defined and
;;;           finsum-comm-monoid-well-defined, so it can no longer precede them;
;;;           nothing between 156 and 242 cites anything it proves (checked:
;;;           sum-ag-segment-congruence and finsum-insert-ag/-insert are named
;;;           only by rake-finsum-laws / -laws2 at 243/244, and fin-enum-is-bijection
;;;           by finsum-type-proof at 201, which part 1 now supplies at ~200).
;;;   DELETE  from theorem-library/finsum-insert.scm the three blocks that
;;;           re-prove names this batch proves EARLIER -- ord-segment-self (:157-172)
;;;           and sum-ag-segment-congruence (:190-246) here, fin-enum-is-bijection
;;;           (:174-188) in part 1 -- or install-duplicate-audit goes 0 -> 3.
;;;
;;; Helper prefix: rkn-.

(define (rkn-close-opened! thunk)
  (for-each (lambda (l)
              (dk-focus! l)
              (let ((g (dk-goal)))
                (if (and (rkn-head? g '=) (equal? (cadr g) (caddr g))) (rfl) (ass))))
            (dk-opened thunk)))


(define (rkn-check! name)
  (if (not (proof-done? *ps*))
      (begin (display ";; rkn: OPEN LEAVES before qed ") (display name) (newline)
             (for-each (lambda (l) (display ";;   ")
                         (display (expression->string (dk-goal-of l))) (newline))
                       (proof-leaves))
             (error "rkn: proof not complete" name))))
(define (rkn-head? f h) (and (pair? f) (eq? (car f) h)))
(define (rkn-body f)
  (cond ((rkn-head? f 'FORALL) (rkn-body (caddr f)))
        ((rkn-head? f 'IMPLIES) (rkn-body (caddr f)))
        (#t f)))
(define (rkn-nvars f)
  (cond ((rkn-head? f 'FORALL) (+ 1 (rkn-nvars (caddr f))))
        ((rkn-head? f 'IMPLIES) (rkn-nvars (caddr f)))
        (#t 0)))
(define (rkn-law-pick head nv what)
  (dk-pick (lambda (f) (and (rkn-head? f 'FORALL)
                            (rkn-head? (rkn-body f) head)
                            (= (rkn-nvars f) nv)))
           what))
;; A tolerant `dk-apply!': instantiate the in-context universal F at TERMS and
;; detach its guards, and do NOT fail when a step's result is ALREADY in the
;; context.  `dk-apply!'/`inst*!' go through `dk-deepest', which errors when the
;; landing is empty -- and two instantiations of the same universal that share a
;; PREFIX (asc at (a,b,c) and then at (a,c,b)) make the second prefix step land
;; nothing.  The formula at each step is computed with `subst-free', so the
;; lookup is exact rather than a guess.
(define (rkn-asm-find f) (find-first (lambda (a) (alpha-equiv? a f)) (dk-asms)))
(define (rkn-step! thunk target what)
  (if (not (rkn-asm-find target)) (dk-landed* thunk))
  (or (rkn-asm-find target)
      (error (string-append "rkn-apply!: " what " landed nothing for")
             (expression->string target))))
;; like rkn-apply!, but STOPS (returning the implication) at a guard the context
;; does not hold -- the caller then knows exactly which formula to establish.
(define (rkn-apply-soft! f . terms)
  (let loop ((f f) (ts terms))
    (cond ((rkn-head? f 'IMPLIES)
           (if (rkn-asm-find (cadr f))
               (loop (rkn-step! (lambda () (detach! f)) (caddr f) "detach!") ts)
               f))
          ((null? ts) f)
          ((rkn-head? f 'FORALL)
           (loop (rkn-step! (lambda () (inst+ f (car ts)))
                            (subst-free (cadr f) (car ts) (caddr f)) "inst+")
                 (cdr ts)))
          (#t f))))
(define (rkn-apply! f . terms)
  (let loop ((f f) (ts terms))
    (cond ((rkn-head? f 'IMPLIES)
           (loop (rkn-step! (lambda () (detach! f)) (caddr f) "detach!") ts))
          ((null? ts) f)
          ((rkn-head? f 'FORALL)
           (loop (rkn-step! (lambda () (inst+ f (car ts)))
                            (subst-free (cadr f) (car ts) (caddr f)) "inst+")
                 (cdr ts)))
          (#t (error "rkn-apply!: not a universal" (expression->string f))))))
(define (rkn-find-if expr pred)
  (cond ((not (pair? expr)) #f)
        ((and (eq? (car expr) 'IF) (= (length expr) 4) (pred (cadr expr))) expr)
        (#t (let loop ((es expr))
              (cond ((null? es) #f)
                    ((not (pair? es)) #f)
                    (#t (or (rkn-find-if (car es) pred) (loop (cdr es)))))))))
(define (rkn-if-land! which ift . opt)
  (let* ((closer (if (pair? opt) (car opt) ass))
         (p      (cadr ift))
         (want   (if (eq? which 'true) p (list 'NOT p)))
         (val    (if (eq? which 'true) (caddr ift) (cadddr ift)))
         (new    (dk-opened (lambda () (if (eq? which 'true) (if-true ift) (if-false ift)))))
         (side   (rkn-leaf new (lambda (g) (alpha-equiv? g want)) "if side condition"))
         (main   (rkn-leaf new (lambda (g) (not (alpha-equiv? g want))) "if main branch")))
    (dk-focus! side) (closer)
    (if (not (sequent-node-grounded? side)) (error "rkn-if-land!: side leaf left open"))
    (dk-focus! main)
    (list '= ift val)))
(define (rkn-reduce-if! which pred . opt)
  (let ((ift (or (rkn-find-if (dk-goal) pred)
                 (error "rkn-reduce-if!: no IF with the wanted condition in"
                        (expression->string (dk-goal))))))
    (subst (apply rkn-if-land! which ift opt))))
(define (rkn-open-bijection! f)
  (dk-split-all! (dk-landed* (lambda () (mac-h 'bijection-membership-iff f))))
  (list (dk-pick (lambda (a) (rkn-head? a 'IN)) "the FUN typing")
        (dk-pick (lambda (a) (and (rkn-head? a 'FORALL) (rkn-head? (rkn-body a) '=)
                                  (= (rkn-nvars a) 2))) "injectivity")
        (dk-pick (lambda (a) (and (rkn-head? a 'FORALL) (rkn-head? (rkn-body a) 'FORSOME)))
                 "surjectivity")))
(define (rkn-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "rkn-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "rkn-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

;;; ---- the four laws, CURRIED (an AND antecedent would block `fact') --------
(define (rkn-o sv x y) (list (list 'OPR sv) x y))
(define (rkn-in-carr sv t) (list 'IN t (list 'CARR sv)))
(define (rkn-all-carr sv vars body)
  (fold-right (lambda (v b) (list 'FORALL v (list 'IMPLIES (rkn-in-carr sv v) b))) body vars))
(define (rkn-laws sv body)
  (list 'IMPLIES (rkn-in-carr sv (list 'IDEN sv))
   (list 'IMPLIES (rkn-all-carr sv '(a_ b_) (rkn-in-carr sv (rkn-o sv 'a_ 'b_)))
    (list 'IMPLIES (rkn-all-carr sv '(a_ b_ c_)
                      (list '= (rkn-o sv (rkn-o sv 'a_ 'b_) 'c_) (rkn-o sv 'a_ (rkn-o sv 'b_ 'c_))))
     (list 'IMPLIES (rkn-all-carr sv '(a_ b_) (list '= (rkn-o sv 'a_ 'b_) (rkn-o sv 'b_ 'a_)))
      body)))))

;;; A.  opr-rearrange-laws:  (a*b)*c = (a*c)*b.
(sp (make-wff
     (list 'FORALL 's (rkn-laws 's
       (rkn-all-carr 's '(a b c)
         (list '= (rkn-o 's (rkn-o 's 'a 'b) 'c) (rkn-o 's (rkn-o 's 'a 'c) 'b)))))))
(dk-peel!)
(let* ((gl (dk-goal))
       (sv (cadr (car (cadr gl))))
       (ab (cadr (cadr gl))) (av (cadr ab)) (bv (caddr ab)) (cv (caddr (cadr gl)))
       (O (lambda (x y) (rkn-o sv x y)))
       (clo (rkn-law-pick 'IN 2 "closure"))
       (asc (rkn-law-pick '= 3 "associativity"))
       (cmm (rkn-law-pick '= 2 "commutativity")))
  (display ";; clo ") (display (expression->string clo)) (newline)
  (display ";; asc ") (display (expression->string asc)) (newline)
  (display ";; cmm ") (display (expression->string cmm)) (newline)
  (define (shw tag) (display ";; ") (display tag) (display ": ")
    (display (if (proof-done? *ps*) "DONE" (expression->string (dk-goal)))) (newline))
  (rkn-apply! clo bv cv) (rkn-apply! clo cv bv)
  (rkn-apply! asc av bv cv)
  (subst (list '= (O (O av bv) cv) (O av (O bv cv))))  (shw 1)
  (rkn-apply! cmm bv cv)
  (subst (list '= (O bv cv) (O cv bv)))                (shw 2)
  (rkn-apply! asc av cv bv)
  (subst (list '= (O (O av cv) bv) (O av (O cv bv))))  (shw 3)
  (rkn-apply! clo av (O cv bv))
  (rfl))
(rkn-check! 'opr-rearrange-laws)
(qed 'opr-rearrange-laws)


;;; B.  sum-ag-type-laws:  the fold stays in the carrier.
(sp (make-wff
     (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
       (list 'FORALL 's (rkn-laws 's
         (list 'FORALL 'g (list 'IMPLIES '(IN g (FUN NN (CARR s)))
           (rkn-in-carr 's '(SUM-AG s g n))))))))))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkn-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "base"))
       (step (rkn-leaf leaves (lambda (g) (dk-contains? g 'succ)) "step")))
  (dk-focus! base)
  (dk-peel!)
  (mac 'sum-ag-zero)
  (ass)
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f)) (eq? (caddr f) 'NN)))
                            "n in NN")))
         (gl (dk-goal))                       ; (IN (SUM-AG s g (succ n)) (CARR s))
         (sv (cadr (cadr gl))) (gv (caddr (cadr gl)))
         (clo (rkn-law-pick 'IN 2 "closure"))
         (ih  (dk-pick (lambda (f) (and (rkn-head? f 'FORALL)
                                        (rkn-head? (rkn-body f) 'IN)
                                        (dk-contains? f 'SUM-AG)))
                       "the IH")))
    (mac 'sum-ag-succ)
    (rkn-apply! ih sv gv)
    (dk-fact! 'fun-apply-type-c gv 'NN (list 'CARR sv) nv)
    (rkn-apply! clo (list 'SUM-AG sv gv nv) (list gv nv))
    (ass)))
(rkn-check! 'sum-ag-type-laws)
(qed 'sum-ag-type-laws)

;;; C.  sum-ag-segment-congruence: SUM-AG(ag,_,n) reads only the indices in OS(n).
;;; (Also proven in theorem-library/finsum-insert.scm -- which loads AFTER this file
;;; once finsum-insert is moved; that block is the one to delete.)
(define rkn-congruence-stmt
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (FORALL g (FORALL h
       (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT n)) (== (g i) (h i))))
                (== (SUM-AG ag g n) (SUM-AG ag h n)))))))))
(sp (make-wff rkn-congruence-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkn-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "base"))
       (step (rkn-leaf leaves (lambda (g) (dk-contains? g 'succ)) "step")))
  (dk-focus! base)
  (dk-peel!)
  (mac 'sum-ag-zero)
  (qrfl)
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f)) (eq? (caddr f) 'NN)))
                            "n in NN")))
         (agree? (lambda (f) (and (rkn-head? f 'FORALL) (rkn-head? (caddr f) 'IMPLIES)
                                  (rkn-head? (cadr (caddr f)) 'IN)
                                  (pair? (caddr (cadr (caddr f))))
                                  (eq? (car (caddr (cadr (caddr f)))) 'ORD-SEGMENT))))
         (hh (dk-pick agree? "the agreement on OS(succ n)"))
         (ih (dk-pick (lambda (f) (and (rkn-head? f 'FORALL) (not (agree? f)))) "the IH"))
         (gl (dk-goal))
         (agv (cadr (cadr gl))) (gv (caddr (cadr gl))) (hv (caddr (caddr gl))))
    (mac 'sum-ag-succ)
    (have! (list 'IN nv (list 'ORD-SEGMENT (list 'succ nv)))
           (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (rkn-apply! hh nv)
    (subst (list '== (list gv nv) (list hv nv)))
    (have! (list 'FORALL 'i (list 'IMPLIES (list 'IN 'i (list 'ORD-SEGMENT nv))
                                  (list '== (list gv 'i) (list hv 'i))))
           (lambda ()
             (let ((iv (dk-di-var!)))
               (have! (list 'IN iv (list 'ORD-SEGMENT (list 'succ nv)))
                      (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
               (rkn-apply! hh iv)
               (ass))))
    (rkn-apply! ih agv gv hv)
    (subst (list '== (list 'SUM-AG agv gv nv) (list 'SUM-AG agv hv nv)))
    (qrfl)))
(rkn-check! 'sum-ag-segment-congruence)
(qed 'sum-ag-segment-congruence)


;; mac-h that also closes the side-condition leaves a GUARDED macete spawns.
(define (rkn-mac-h! name hyp)
  (let* ((g0    (dk-goal))
         (new   (dk-opened (lambda () (mac-h name hyp))))
         (sides (filter (lambda (l) (not (alpha-equiv? (dk-goal-of l) g0))) new))
         (mains (filter (lambda (l) (alpha-equiv? (dk-goal-of l) g0)) new)))
    (for-each (lambda (s) (dk-focus! s) (ass)) sides)
    (if (null? mains) (error "rkn-mac-h!: no main branch after" name))
    (dk-focus! (car mains))))

;;; ord-segment-self MOVED 2026-09-17 to rake-inverse-bij.scm (part 1): finsum-single-support
;;; (position 202) cites it, and this file loads at ~230.

;; (IN i (ORD-SEGMENT n)), (IN n NN) in context  =>  land (NOT (= i n)).
(define (rkn-seg-neq! iv nv)
  (let ((claim (list 'NOT (list '= iv nv))))
    (if (not (rkn-asm-find claim))
        (have! claim
          (lambda ()
            (dk-fact! 'nn-subset-ord nv)
            (rkn-mac-h! 'ord-segment-membership (list 'IN iv (list 'ORD-SEGMENT nv)))
            (rkn-mac-h! 'ord-lt-iff (dk-pick (dk-head? 'ORD-LT) "ORD-LT i n"))
            (dk-split! (dk-pick (dk-head? 'AND) "ord-lt-iff conjunction"))
            (ass))))
    claim))


;;; D.  sum-ag-replace-entry-laws:  changing ONE entry of the family.
;;;
;;;   k in OS(n),  g = gp off k   =>   SUM(g,n) * gp(k)  =  SUM(gp,n) * g(k)
;;;
;;; This is the whole combinatorial content of permutation invariance, and it needs
;;; no index surgery: the induction peels the TOP index n, and the only moves are
;;; sum-ag-succ and (a*b)*c = (a*c)*b.
(define rkn-replace-stmt
  (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (list 'FORALL 's (rkn-laws 's
      (list 'FORALL 'g (list 'IMPLIES '(IN g (FUN NN (CARR s)))
      (list 'FORALL 'gp (list 'IMPLIES '(IN gp (FUN NN (CARR s)))
      (list 'FORALL 'k (list 'IMPLIES '(IN k (ORD-SEGMENT n))
        (list 'IMPLIES '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                                     (IMPLIES (NOT (= i_ k)) (== (g i_) (gp i_)))))
          (list '= (rkn-o 's '(SUM-AG s g n) '(gp k))
                   (rkn-o 's '(SUM-AG s gp n) '(g k)))))))))))))))

(sp (make-wff rkn-replace-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkn-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "base"))
       (step (rkn-leaf leaves (lambda (g) (dk-contains? g 'succ)) "step")))
  ;; ---- base n = 0: ORD-SEGMENT(0) has no members, so the hypothesis is absurd
  (dk-focus! base)
  (dk-peel!)
  (let* ((kh (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                       (equal? (caddr f) '(ORD-SEGMENT 0))))
                      "k in ORD-SEGMENT(0)"))
         (no (dk-fact! 'ord-segment-zero-no-members (cadr kh))))
    (dk-only! kh no)
    (prop))
  ;; ---- step
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv  (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f)) (eq? (caddr f) 'NN)))
                             "n in NN")))
         (gl  (dk-goal))
         (lhs (cadr gl))
         (sv  (cadr (car lhs)))
         (gv  (caddr (cadr lhs)))
         (gpk (caddr lhs)) (gpv (car gpk)) (kv (cadr gpk))
         (O   (lambda (x y) (rkn-o sv x y)))
         (SG  (lambda (f m) (list 'SUM-AG sv f m)))
         (CA  (list 'CARR sv))
         (clo (rkn-law-pick 'IN 2 "closure"))
         (ih  (dk-pick (lambda (f) (and (rkn-head? f 'FORALL) (dk-contains? f 'SUM-AG))) "the IH"))
         (agree (dk-pick (lambda (f) (and (rkn-head? f 'FORALL) (dk-contains? f 'ORD-SEGMENT)
                                          (not (dk-contains? f 'SUM-AG))))
                         "the agreement on OS(succ n)"))
         (segN (list 'ORD-SEGMENT nv))
         (segS (list 'ORD-SEGMENT (list 'succ nv))))
    (display ";; rkn D step vars ") (display (list nv sv gv gpv kv)) (newline)
    (dk-fact! 'nn-succ-closed nv)
    (dk-fact! 'ord-segment-nn-subset (list 'succ nv) kv)        ; (IN k NN)
    (dk-fact! 'fun-apply-type-c gv  'NN CA kv)
    (dk-fact! 'fun-apply-type-c gpv 'NN CA kv)
    (dk-fact! 'fun-apply-type-c gv  'NN CA nv)
    (dk-fact! 'fun-apply-type-c gpv 'NN CA nv)
    (dk-fact! 'sum-ag-type-laws nv sv gv)
    (dk-fact! 'sum-ag-type-laws nv sv gpv)
    (use-em (list 'IN kv segN)
      ;; ---- k below n: peel the top term and use the IH
      (lambda ()
        (mac 'sum-ag-succ)
        (have! (list 'IN nv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
        (rkn-seg-neq! kv nv)                                    ; (NOT (= k n))
        (dk-fact! 'neq-sym kv nv)                               ; (NOT (= n k))
        (rkn-apply! agree nv)                                   ; (== (g n) (gp n))
        (subst (list '== (list gv nv) (list gpv nv)))
        (rkn-apply! clo (SG gv nv) (list gpv kv))
        (subst (dk-fact! 'opr-rearrange-laws sv (SG gv nv) (list gpv nv) (list gpv kv)))
        (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ segN)
                        (list 'IMPLIES (list 'NOT (list '= 'i_ kv))
                              (list '== (list gv 'i_) (list gpv 'i_)))))
               (lambda ()
                 (dk-peel!)
                 (let ((iv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                                           (equal? (caddr f) segN)))
                                          "i in OS(n)"))))
                   (have! (list 'IN iv segS)
                          (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
                   (rkn-apply! agree iv)
                   (ass))))
        (subst (rkn-apply! ih sv gv gpv kv))
        (rkn-apply! clo (SG gpv nv) (list gv kv))
        (subst (dk-fact! 'opr-rearrange-laws sv (SG gpv nv) (list gpv nv) (list gv kv)))
        (rfl))
      ;; ---- k = n: the two families agree BELOW n, and the two top terms swap
      (lambda ()
        (rkn-mac-h! 'ord-segment-nn-succ (list 'IN kv segS))
        (have! (list '= kv nv) (lambda () (prop)))
        (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ segN)
                                       (list '== (list gv 'i_) (list gpv 'i_))))
               (lambda ()
                 (dk-peel!)
                 (let ((iv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                                           (equal? (caddr f) segN)))
                                          "i in OS(n)"))))
                   (rkn-seg-neq! iv nv)
                   (have! (list 'NOT (list '= iv kv))
                          (lambda () (subst (list '= kv nv)) (ass)))
                   (have! (list 'IN iv segS)
                          (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
                   (rkn-apply! agree iv)
                   (ass))))
        (subst (list '= kv nv))                                  ; the goal now speaks of n
        (mac 'sum-ag-succ)
        (subst (dk-fact! 'sum-ag-segment-congruence nv sv gv gpv))
        (rkn-apply! clo (SG gpv nv) (list gv nv))
        (subst (dk-fact! 'opr-rearrange-laws sv (SG gpv nv) (list gpv nv) (list gv nv)))
        (rfl)))))
(rkn-check! 'sum-ag-replace-entry-laws)
(qed 'sum-ag-replace-entry-laws)

;;; ---------------------------------------------------------------------------
;;; E.  seg-perm-restrict-is-bijection.
;;;
;;; A permutation phi of OS(succ n) restricts to a permutation of OS(n) once the
;;; one index it sends to n is re-routed to k = phi(n):
;;;
;;;     rho(i)  =  IF phi(i) = n THEN k ELSE phi(i)        (i in OS n)
;;;
;;; is a bijection OS(n) -> OS(n).  This is the index surgery the permutation
;;; induction needs, and it replaces the archived proof's DELETE-AT + INVERSE-BIJ
;;; pair: no deletion, no index shifting, no ordinal arithmetic beyond
;;; "n is not in OS(n)" and "OS(succ n) = OS(n) u {n}".
(define rkn-rho-stmt
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL phi (IMPLIES (IN phi (BIJECTION (ORD-SEGMENT (succ n)) (ORD-SEGMENT (succ n))))
     (FORALL k (IMPLIES (= (phi n) k)
       (IN (VNB-LAMBDA i_ (ORD-SEGMENT n) (IF (= (phi i_) n) k (phi i_)))
           (BIJECTION (ORD-SEGMENT n) (ORD-SEGMENT n))))))))))

(sp (make-wff rkn-rho-stmt))
(dk-peel!)
(define rkn-rho-n  (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f)) (eq? (caddr f) 'NN))) "n in NN")))
(define rkn-rho-segN (list 'ORD-SEGMENT rkn-rho-n))
(define rkn-rho-segS (list 'ORD-SEGMENT (list 'succ rkn-rho-n)))
(define rkn-rho-phi (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                                    (rkn-head? (caddr f) 'BIJECTION))) "phi")))
(define rkn-rho-k   (caddr (dk-pick (lambda (f) (and (rkn-head? f '=)
                                                     (equal? (cadr f) (list rkn-rho-phi rkn-rho-n))))
                                    "phi(n) = k")))
(define rkn-rho-lam (list 'VNB-LAMBDA 'i_ rkn-rho-segN
                          (list 'IF (list '= (list rkn-rho-phi 'i_) rkn-rho-n) rkn-rho-k
                                (list rkn-rho-phi 'i_))))
(display ";; rho vars ") (display (list rkn-rho-n rkn-rho-phi rkn-rho-k)) (newline)

(define rkn-rho-parts (rkn-open-bijection! (list 'IN rkn-rho-phi (list 'BIJECTION rkn-rho-segS rkn-rho-segS))))
(define rkn-rho-fun  (car rkn-rho-parts))
(define rkn-rho-inj  (cadr rkn-rho-parts))
(define rkn-rho-surj (caddr rkn-rho-parts))
(dk-fact! 'nn-succ-closed rkn-rho-n)
(dk-fact! 'ord-segment-self rkn-rho-n)                       ; (NOT (IN n (OS n)))
(have! (list 'IN rkn-rho-n rkn-rho-segS)
       (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
(dk-fact! 'fun-apply-type-c rkn-rho-phi rkn-rho-segS rkn-rho-segS rkn-rho-n)
(have! (list 'IN rkn-rho-k rkn-rho-segS)
       (lambda () (subst (list '= rkn-rho-k (list rkn-rho-phi rkn-rho-n))) (ass)))

;; (IN i (OS n)) in context, EQ is (= i n) in context  =>  FALSITY
(define (rkn-seg-absurd! iv eqin)
  (let ((neg (list 'NOT (list 'IN iv rkn-rho-segN))))
    (have! neg (lambda () (subst eqin) (ass)))
    (ai neg)))

;; i in OS n, (= (phi i) n) in context  =>  land (NOT (= k n))
(define (rkn-k-neq-n! iv)
  (let ((claim (list 'NOT (list '= rkn-rho-k rkn-rho-n))))
    (rkn-ensure! claim
          (lambda ()
            (di)                                             ; assume (= k n), goal FALSITY
            (dk-fact! 'eq-trans (list rkn-rho-phi rkn-rho-n) rkn-rho-k rkn-rho-n)
            (dk-fact! 'eq-sym (list rkn-rho-phi iv) rkn-rho-n)
            (dk-fact! 'eq-trans (list rkn-rho-phi rkn-rho-n) rkn-rho-n (list rkn-rho-phi iv))
            (rkn-apply! rkn-rho-inj rkn-rho-n iv)            ; (= n i)
            (dk-fact! 'eq-sym rkn-rho-n iv)                  ; (= i n)
            (rkn-seg-absurd! iv (list '= iv rkn-rho-n))))
    claim))

;; i in OS n  =>  land (IN i (OS (succ n)))  and  (NOT (= (phi i) k))
(define (rkn-lift! iv)
  (have! (list 'IN iv rkn-rho-segS) (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
  (dk-fact! 'fun-apply-type-c rkn-rho-phi rkn-rho-segS rkn-rho-segS iv))

;; prove CLAIM, or find it in the context, or -- when it IS the focus goal --
;; run BODY in place.  (`have!' of the focus goal is a silent self-loop.)
(define (rkn-ensure! claim body)
  (cond ((rkn-asm-find claim) 'in-context)
        ((alpha-equiv? claim (dk-goal)) (body) 'closed)
        (#t (have! claim body) 'in-context)))

;; a value v in OS(succ n) with (NOT (= v n)) in context  =>  (IN v (OS n))
(define (rkn-drop! v)
  (rkn-ensure! (list 'IN v rkn-rho-segN)
    (lambda ()
      (rkn-mac-h! 'ord-segment-nn-succ (list 'IN v rkn-rho-segS))
      (prop))))

(define (rkn-rho-fun!)
  (let ((iv (dk-di-var!)))
    (rkn-lift! iv)
    (use-em (list '= (list rkn-rho-phi iv) rkn-rho-n)
      (lambda ()                                             ; phi i = n:  rho i = k
        (rkn-reduce-if! 'true (lambda (c) #t))
        (rkn-k-neq-n! iv)
        (dk-fact! 'neq-sym rkn-rho-k rkn-rho-n)
        (if (eq? (rkn-drop! rkn-rho-k) 'in-context) (ass)))
      (lambda ()                                             ; phi i /= n: rho i = phi i
        (rkn-reduce-if! 'false (lambda (c) #t))
        (if (eq? (rkn-drop! (list rkn-rho-phi iv)) 'in-context) (ass))))))


;; land (= IFT val) by one IF reduction (WHICH is 'true or 'false)
(define (rkn-if-value! ift val which)
  (rkn-ensure! (list '= ift val)
    (lambda () (rkn-reduce-if! which (lambda (c) #t)) (rfl))))

;; the IF term the lambda body becomes at argument V
(define (rkn-rho-if v)
  (list 'IF (list '= (list rkn-rho-phi v) rkn-rho-n) rkn-rho-k (list rkn-rho-phi v)))

;; from (= IFa IFb) in context and the two branch values, land (= va vb)
(define (rkn-transport! av bv va vb)
  (dk-fact! 'eq-sym (rkn-rho-if av) va)                       ; (= va IFa)
  (dk-fact! 'eq-trans va (rkn-rho-if av) (rkn-rho-if bv))     ; (= va IFb)
  (dk-fact! 'eq-trans va (rkn-rho-if bv) vb))                 ; (= va vb)

(define (rkn-rho-inj!)
  (let* ((landed (dk-peel!))
         (gl (dk-goal))                                      ; (= a b)
         (av (cadr gl)) (bv (caddr gl))
         (pa (list rkn-rho-phi av)) (pb (list rkn-rho-phi bv)))
    (rkn-lift! av) (rkn-lift! bv)
    (lam-b-h (dk-pick (lambda (f) (and (rkn-head? f '=) (dk-contains? f 'VNB-LAMBDA)))
                      "rho a = rho b"))
    (define (close-from-phi-eq!)                             ; (= (phi a) (phi b)) in context
      (rkn-apply! rkn-rho-inj av bv)
      (ass))
    (use-em (list '= pa rkn-rho-n)
      (lambda ()
        (rkn-if-value! (rkn-rho-if av) rkn-rho-k 'true)
        (use-em (list '= pb rkn-rho-n)
          (lambda ()                                         ; both hit n
            (dk-fact! 'eq-sym pb rkn-rho-n)
            (dk-fact! 'eq-trans pa rkn-rho-n pb)
            (close-from-phi-eq!))
          (lambda ()                                         ; a hits n, b does not: absurd
            (rkn-if-value! (rkn-rho-if bv) pb 'false)
            (rkn-transport! av bv rkn-rho-k pb)              ; (= k (phi b))
            (dk-fact! 'eq-trans (list rkn-rho-phi rkn-rho-n) rkn-rho-k pb)
            (rkn-apply! rkn-rho-inj rkn-rho-n bv)            ; (= n b)
            (dk-fact! 'eq-sym rkn-rho-n bv)
            (rkn-seg-absurd! bv (list '= bv rkn-rho-n)))))
      (lambda ()
        (rkn-if-value! (rkn-rho-if av) pa 'false)
        (use-em (list '= pb rkn-rho-n)
          (lambda ()                                         ; b hits n, a does not: absurd
            (rkn-if-value! (rkn-rho-if bv) rkn-rho-k 'true)
            (rkn-transport! av bv pa rkn-rho-k)              ; (= (phi a) k)
            (dk-fact! 'eq-sym pa rkn-rho-k)
            (dk-fact! 'eq-trans (list rkn-rho-phi rkn-rho-n) rkn-rho-k pa)
            (rkn-apply! rkn-rho-inj rkn-rho-n av)            ; (= n a)
            (dk-fact! 'eq-sym rkn-rho-n av)
            (rkn-seg-absurd! av (list '= av rkn-rho-n)))
          (lambda ()                                         ; neither
            (rkn-if-value! (rkn-rho-if bv) pb 'false)
            (rkn-transport! av bv pa pb)
            (close-from-phi-eq!)))))))

(define (rkn-rho-pre! z eqz other)
  ;; z in OS(succ n) with (= (phi z) EQZ); show z /= n, the contradiction being
  ;; that phi(n) = k would then force OTHER (an equation the branch refutes).
  (have! (list 'NOT (list '= z rkn-rho-n))
    (lambda ()
      (di)
      (have! (list '= (list rkn-rho-phi z) (list rkn-rho-phi rkn-rho-n))
             (lambda () (subst (list '= z rkn-rho-n)) (rfl)))
      (dk-fact! 'eq-sym (list rkn-rho-phi z) eqz)
      (dk-fact! 'eq-trans eqz (list rkn-rho-phi z) (list rkn-rho-phi rkn-rho-n))
      (dk-fact! 'eq-trans eqz (list rkn-rho-phi rkn-rho-n) rkn-rho-k)
      (other))))

(define (rkn-rho-surj!)
  (let* ((mem (car (dk-peel!)))
         (w   (cadr mem)))
    (rkn-lift! w)
    (rkn-seg-neq! w rkn-rho-n)                                  ; (NOT (= w n))
    (use-em (list '= w rkn-rho-k)
      (lambda ()                                                ; w = k: take phi^-1(n)
        (let ((z (dk-skolem! (rkn-apply! rkn-rho-surj rkn-rho-n))))
          (rkn-rho-pre! z rkn-rho-n
            (lambda ()                                          ; (= n k) is now in context
              (dk-fact! 'eq-sym rkn-rho-n rkn-rho-k)
              (dk-fact! 'eq-trans w rkn-rho-k rkn-rho-n)
              (ai (list 'NOT (list '= w rkn-rho-n)))))
          (rkn-drop! z)
          (ew z)
          (dk-conj-close!
           (lambda ()
             (if (rkn-head? (dk-goal) 'IN)
                 (ass)
                 (begin (lam-b)
                        (rkn-reduce-if! 'true (lambda (c) #t))
                        (dk-fact! 'eq-sym w rkn-rho-k)
                        (ass)))))))
      (lambda ()                                                ; w /= k: take phi^-1(w)
        (let ((z (dk-skolem! (rkn-apply! rkn-rho-surj w))))
          (rkn-rho-pre! z w
            (lambda () (ai (list 'NOT (list '= w rkn-rho-k)))))  ; (= w k) is now in context
          (rkn-drop! z)
          (ew z)
          (dk-conj-close!
           (lambda ()
             (if (rkn-head? (dk-goal) 'IN)
                 (ass)
                 (begin (lam-b)
                        (have! (list 'NOT (list '= (list rkn-rho-phi z) rkn-rho-n))
                               (lambda () (subst (list '= (list rkn-rho-phi z) w)) (ass)))
                        (rkn-reduce-if! 'false (lambda (c) #t))
                        (ass))))))))))

(mac 'bijection-membership-iff)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((rkn-head? g 'IN)
            (let* ((ls (dk-opened (lambda () (lam-t))))
                   (st? (lambda (q) (and (rkn-head? q 'IN) (eq? (caddr q) 'SET))))
                   (setl (rkn-leaf ls (lambda (q) (st? q)) "sethood of OS(n)"))
                   (ptw  (rkn-leaf ls (lambda (q) (not (st? q))) "pointwise typing")))
              (dk-focus! setl)
              (dk-fact! 'nn-subset-ord rkn-rho-n)
              (dk-fact! 'ord-segment-is-set rkn-rho-n)
              (ass)
              (dk-focus! ptw)
              (rkn-rho-fun!)))
           ((rkn-head? (caddr (caddr g)) 'FORALL) (rkn-rho-inj!))
           (#t (rkn-rho-surj!))))))
(rkn-check! 'seg-perm-restrict-is-bijection)
(qed 'seg-perm-restrict-is-bijection)

;;; ---------------------------------------------------------------------------
;;; F.  sum-ag-permutation-invariance-laws.
(define rkn-pi-stmt
  (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (list 'FORALL 's (rkn-laws 's
      (list 'FORALL 'g (list 'IMPLIES '(IN g (FUN NN (CARR s)))
      (list 'FORALL 'h (list 'IMPLIES '(IN h (FUN NN (CARR s)))
      (list 'FORALL 'phi (list 'IMPLIES '(IN phi (BIJECTION (ORD-SEGMENT n) (ORD-SEGMENT n)))
        (list 'IMPLIES '(FORALL i (IMPLIES (IN i (ORD-SEGMENT n)) (= (h i) (g (phi i)))))
          '(= (SUM-AG s g n) (SUM-AG s h n))))))))))))))

;; generic versions of the E-helpers (E's are closed over its own eigenvariables)
;; the three projections of a BIJECTION membership, each landed in a HAVE! lane
;; so the membership itself SURVIVES (mac-h replaces what it unfolds).
(define (rkn-bij-inj-stmt bij)
  (let ((ph (cadr bij)) (X (cadr (caddr bij))))
    (list 'FORALL 'a (list 'IMPLIES (list 'IN 'a X)
      (list 'FORALL 'b (list 'IMPLIES (list 'IN 'b X)
        (list 'IMPLIES (list '= (list ph 'a) (list ph 'b)) (list '= 'a 'b))))))))
(define (rkn-bij-surj-stmt bij)
  (let ((ph (cadr bij)) (X (cadr (caddr bij))) (Y (caddr (caddr bij))))
    (list 'FORALL 'w (list 'IMPLIES (list 'IN 'w Y)
      (list 'FORSOME 'z (list 'AND (list 'IN 'z X) (list '= (list ph 'z) 'w)))))))
(define (rkn-bij-proj! bij claim)
  (have! claim (lambda () (rkn-open-bijection! bij) (ass)))
  claim)

(define (rkn-absurd*! iv nv eqin)
  (let ((neg (list 'NOT (list 'IN iv (list 'ORD-SEGMENT nv)))))
    (have! neg (lambda () (subst eqin) (ass)))
    (ai neg)))

(sp (make-wff rkn-pi-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkn-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "base"))
       (step (rkn-leaf leaves (lambda (g) (dk-contains? g 'succ)) "step")))
  ;; ---- base n = 0:  both folds are IDEN(s)
  (dk-focus! base)
  (dk-peel!)
  (mac 'sum-ag-zero)
  (rfl)
  ;; ---- step
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv   (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f)) (eq? (caddr f) 'NN)))
                              "n in NN")))
         (segN (list 'ORD-SEGMENT nv))
         (segS (list 'ORD-SEGMENT (list 'succ nv)))
         (gl   (dk-goal))                       ; (= (SUM-AG s g (succ n)) (SUM-AG s h (succ n)))
         (sv   (cadr (cadr gl))) (gv (caddr (cadr gl))) (hv (caddr (caddr gl)))
         (CA   (list 'CARR sv))
         (phiv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                               (rkn-head? (caddr f) 'BIJECTION))) "phi")))
         (kt   (list phiv nv))                  ; k := phi(n)
         (O    (lambda (x y) (rkn-o sv x y)))
         (SG   (lambda (f m) (list 'SUM-AG sv f m)))
         (gp   (list 'VNB-LAMBDA 'x_ 'NN
                 (list 'IF (list '= 'x_ nv) (list gv kt)
                       (list 'IF (list '= 'x_ kt) (list gv nv) (list gv 'x_)))))
         (rho  (list 'VNB-LAMBDA 'i_ segN
                 (list 'IF (list '= (list phiv 'i_) nv) kt (list phiv 'i_))))
         (ih   (dk-pick (lambda (f) (and (rkn-head? f 'FORALL) (dk-contains? f 'SUM-AG))) "the IH"))
         (agree (dk-pick (lambda (f) (and (rkn-head? f 'FORALL) (dk-contains? f 'ORD-SEGMENT)
                                          (not (dk-contains? f 'SUM-AG)))) "the agreement"))
         (clo  (rkn-law-pick 'IN 2 "closure")))
    (display ";; rkn F step ") (display (list nv sv gv hv phiv)) (newline)
    (define bij (list 'IN phiv (list 'BIJECTION segS segS)))
    (rkn-bij-proj! bij (list 'IN phiv (list 'FUN segS segS)))
    (define inj (rkn-bij-proj! bij (rkn-bij-inj-stmt bij)))
    (dk-fact! 'nn-succ-closed nv)
    (dk-fact! 'ord-segment-self nv)
    (have! (list 'IN nv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (dk-fact! 'fun-apply-type-c phiv segS segS nv)            ; (IN (phi n) (OS succ n))
    (dk-fact! 'ord-segment-nn-subset (list 'succ nv) kt)      ; (IN (phi n) NN)
    (dk-fact! 'fun-apply-type-c gv 'NN CA nv)
    (dk-fact! 'fun-apply-type-c gv 'NN CA kt)
    (dk-fact! 'fun-apply-type-c hv 'NN CA nv)
    ;; gp in FUN(NN, CARR s)
    (have! (list 'IN gp (list 'FUN 'NN CA))
      (lambda ()
        (let* ((ls (dk-opened (lambda () (lam-t))))
               (st? (lambda (q) (and (rkn-head? q 'IN) (eq? (caddr q) 'SET))))
               (setl (rkn-leaf ls st? "NN in SET"))
               (ptw  (rkn-leaf ls (lambda (q) (not (st? q))) "pointwise")))
          (dk-focus! setl) (fact 'nn-is-set) (ass)
          (dk-focus! ptw)
          (let ((xv (dk-di-var!)))
            (dk-fact! 'fun-apply-type-c gv 'NN CA xv)
            (use-em (list '= xv nv)
              (lambda () (rkn-reduce-if! 'true (lambda (c) #t)) (ass))
              (lambda ()
                (rkn-reduce-if! 'false (lambda (c) (equal? c (list '= xv nv))))
                (use-em (list '= xv kt)
                  (lambda () (rkn-reduce-if! 'true (lambda (c) #t)) (ass))
                  (lambda () (rkn-reduce-if! 'false (lambda (c) #t)) (ass)))))))))
    (dk-fact! 'fun-apply-type-c gp 'NN CA nv)
    (dk-fact! 'fun-apply-type-c gp 'NN CA kt)
    (dk-fact! 'sum-ag-type-laws nv sv gv)
    (dk-fact! 'sum-ag-type-laws nv sv gp)
    (dk-fact! 'sum-ag-type-laws nv sv hv)
    ;; rho in BIJECTION(OS n, OS n)
    (have! (list '= kt kt) (lambda () (rfl)))
    (dk-fact! 'seg-perm-restrict-is-bijection nv phiv kt)

    ;; ---------------------------------------------------------------- pieces
    (define (val-of! term val which . opt)          ; (= term val) by beta + one IF
      (rkn-ensure! (list '= term val)
        (lambda () (lam-b) (apply rkn-reduce-if! which (lambda (c) #t) opt) (rfl))))
    (define (gp-at-n!)                              ; gp(n) = g(phi n)
      (val-of! (list gp nv) (list gv kt) 'true (lambda () (rfl))))
    ;; for i in OS n with (NOT (= i n)) and (NOT (= i (phi n))): gp(i) == g(i)
    (define (gp-off! iv)
      (rkn-reduce-if! 'false (lambda (c) (equal? c (list '= iv nv))))
      (rkn-reduce-if! 'false (lambda (c) (equal? c (list '= iv kt))))
      (qrfl))
    ;; i in OS n, (= (phi i) n) in context  =>  (NOT (= (phi n) n))
    (define (kt-neq-n! iv)
      (rkn-ensure! (list 'NOT (list '= kt nv))
        (lambda ()
          (di)
          (dk-fact! 'eq-sym kt nv)
          (dk-fact! 'eq-trans (list phiv iv) nv kt)
          (rkn-apply! inj iv nv)
          (rkn-absurd*! iv nv (list '= iv nv)))))
    ;; i in OS n  =>  (NOT (= (phi i) (phi n)))
    (define (phi-neq! iv)
      (rkn-ensure! (list 'NOT (list '= (list phiv iv) kt))
        (lambda ()
          (di)
          (rkn-apply! inj iv nv)
          (rkn-absurd*! iv nv (list '= iv nv)))))

    (gp-at-n!)
    ;; ------------------------------------------------- the IH along rho
    (let* ((partial (rkn-apply-soft! ih sv gp hv rho))
           (need    (cadr partial)))
      (display ";; IH wants: ") (display (expression->string need)) (newline)
      (have! need
        (lambda ()
          (dk-peel!)
          (let ((iv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                                    (equal? (caddr f) segN))) "i in OS n"))))
            (have! (list 'IN iv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
            (dk-fact! 'fun-apply-type-c phiv segS segS iv)
            (dk-fact! 'ord-segment-nn-subset (list 'succ nv) (list phiv iv))
            (rkn-apply! agree iv)                          ; (= (h i) (g (phi i)))
            (rkn-seg-neq! iv nv)
            (use-em (list '= (list phiv iv) nv)
              (lambda ()                                   ; phi i = n:  rho i = phi n
                (val-of! (list rho iv) kt 'true)
                (subst (list '= (list rho iv) kt))
                (kt-neq-n! iv)
                (rkn-ensure! (list '= (list gp kt) (list gv nv))
                  (lambda () (lam-b)
                     (rkn-reduce-if! 'false (lambda (c) (equal? c (list '= kt nv))))
                     (rkn-reduce-if! 'true  (lambda (c) (equal? c (list '= kt kt))) (lambda () (rfl)))
                     (rfl)))
                (subst (list '= (list gp kt) (list gv nv)))
                (have! (list '= (list gv (list phiv iv)) (list gv nv))
                       (lambda () (subst (list '= (list phiv iv) nv)) (rfl)))
                (dk-fact! 'eq-trans (list hv iv) (list gv (list phiv iv)) (list gv nv))
                (ass))
              (lambda ()                                   ; phi i /= n: rho i = phi i
                (val-of! (list rho iv) (list phiv iv) 'false)
                (subst (list '= (list rho iv) (list phiv iv)))
                (phi-neq! iv)
                (rkn-ensure! (list '= (list gp (list phiv iv)) (list gv (list phiv iv)))
                  (lambda () (lam-b)
                     (rkn-reduce-if! 'false (lambda (c) (equal? c (list '= (list phiv iv) nv))))
                     (rkn-reduce-if! 'false (lambda (c) (equal? c (list '= (list phiv iv) kt))))
                     (rfl)))
                (subst (list '= (list gp (list phiv iv)) (list gv (list phiv iv))))
                (ass))))))
      (rkn-apply! partial))                                ; (= (SUM s gp n) (SUM s h n))
    ;; ------------------------------------------------- h(n) = gp(n)
    (rkn-apply! agree nv)                                  ; (= (h n) (g (phi n)))
    (dk-fact! 'eq-sym (list gp nv) (list gv kt))            ; (= (g (phi n)) (gp n))
    (dk-fact! 'eq-trans (list hv nv) (list gv kt) (list gp nv))
    (dk-fact! 'eq-sym (SG gp nv) (SG hv nv))
    ;; ------------------------------------------------- the swap
    (have! (list '= (O (SG gv nv) (list gv nv)) (O (SG gp nv) (list gp nv)))
      (lambda ()
        (use-em (list '= kt nv)
          (lambda ()                                       ; phi n = n: gp agrees with g
            (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ segN)
                          (list '== (list gp 'i_) (list gv 'i_))))
              (lambda ()
                (dk-peel!)
                (let ((iv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                                          (equal? (caddr f) segN))) "i"))))
                  (dk-fact! 'ord-segment-nn-subset nv iv)
                  (rkn-seg-neq! iv nv)
                  (have! (list 'NOT (list '= iv kt))
                         (lambda () (subst (list '= kt nv)) (ass)))
                  (lam-b)
                  (gp-off! iv))))
            (subst (dk-fact! 'sum-ag-segment-congruence nv sv gp gv))
            (have! (list '= (list gv kt) (list gv nv))
                   (lambda () (subst (list '= kt nv)) (rfl)))
            (dk-fact! 'eq-trans (list gp nv) (list gv kt) (list gv nv))
            (subst (list '= (list gp nv) (list gv nv)))
            (rkn-apply! clo (SG gv nv) (list gv nv))
            (rfl))
          (lambda ()                                       ; phi n /= n: one entry replaced
            (rkn-ensure! (list 'IN kt segN)
              (lambda () (rkn-mac-h! 'ord-segment-nn-succ (list 'IN kt segS)) (prop)))
            (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ segN)
                          (list 'IMPLIES (list 'NOT (list '= 'i_ kt))
                                (list '== (list gv 'i_) (list gp 'i_)))))
              (lambda ()
                (dk-peel!)
                (let ((iv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                                          (equal? (caddr f) segN))) "i"))))
                  (dk-fact! 'ord-segment-nn-subset nv iv)
                  (rkn-seg-neq! iv nv)
                  (lam-b)
                  (gp-off! iv))))
            (rkn-ensure! (list '= (list gp kt) (list gv nv))
              (lambda () (lam-b)
                 (rkn-reduce-if! 'false (lambda (c) (equal? c (list '= kt nv))))
                 (rkn-reduce-if! 'true  (lambda (c) (equal? c (list '= kt kt))) (lambda () (rfl)))
                 (rfl)))
            ;; the two congruences are built by REWRITING THE OTHER SIDE: a `subst'
            ;; of (g n) into the goal would also fire inside gp's own lambda body,
            ;; which contains (g n) by construction.
            (rkn-apply! clo (SG gv nv) (list gv nv))
            (rkn-apply! clo (SG gv nv) (list gp kt))
            (rkn-apply! clo (SG gp nv) (list gv kt))
            (have! (list '= (O (SG gv nv) (list gv nv)) (O (SG gv nv) (list gp kt)))
                   (lambda () (subst (list '= (list gp kt) (list gv nv))) (rfl)))
            (have! (list '= (O (SG gp nv) (list gv kt)) (O (SG gp nv) (list gp nv)))
                   (lambda () (subst (list '= (list gp nv) (list gv kt))) (rfl)))
            (dk-fact! 'sum-ag-replace-entry-laws nv sv gv gp kt)
            (dk-fact! 'eq-trans (O (SG gv nv) (list gv nv)) (O (SG gv nv) (list gp kt))
                                (O (SG gp nv) (list gv kt)))
            (dk-fact! 'eq-trans (O (SG gv nv) (list gv nv)) (O (SG gp nv) (list gv kt))
                                (O (SG gp nv) (list gp nv)))
            (ass)))))
    ;; ------------------------------------------------- assemble
    (mac 'sum-ag-succ)
    (subst (list '= (SG hv nv) (SG gp nv)))
    (subst (list '= (list hv nv) (list gp nv)))
    (ass)))


(rkn-check! 'sum-ag-permutation-invariance-laws)
(qed 'sum-ag-permutation-invariance-laws)

;;; ---------------------------------------------------------------------------
;;; G.  the two instantiations.
(define (rkn-land-laws! sv iden! clo! asc! cmm!)
  (have! (rkn-in-carr sv (list 'IDEN sv)) iden!)
  (have! (rkn-all-carr sv '(a_ b_) (rkn-in-carr sv (rkn-o sv 'a_ 'b_))) clo!)
  (have! (rkn-all-carr sv '(a_ b_ c_)
           (list '= (rkn-o sv (rkn-o sv 'a_ 'b_) 'c_) (rkn-o sv 'a_ (rkn-o sv 'b_ 'c_)))) asc!)
  (have! (rkn-all-carr sv '(a_ b_) (list '= (rkn-o sv 'a_ 'b_) (rkn-o sv 'b_ 'a_))) cmm!))
;; peel the law's binders and hand the citation its eigenvariables
(define (rkn-law-by-cite! nargs cite!)
  (lambda ()
    (dk-peel!)
    (let* ((g (dk-goal))
           (t (if (rkn-head? g 'IN) (cadr g) (cadr g))))
      (if (= nargs 2)
          (cite! (cadr t) (caddr t))
          (let ((ab (cadr t))) (cite! (cadr ab) (caddr ab) (caddr t)))))
    (ass)))

(define rkn-pi-ag-stmt
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL g (IMPLIES (IN g (FUN NN (CARR ag)))
     (FORALL h (IMPLIES (IN h (FUN NN (CARR ag)))
     (FORALL phi (IMPLIES (IN phi (BIJECTION (ORD-SEGMENT n) (ORD-SEGMENT n)))
       (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT n)) (= (h i) (g (phi i)))))
         (= (SUM-AG ag g n) (SUM-AG ag h n))))))))))))))
(sp (make-wff rkn-pi-ag-stmt))
(dk-peel!)
(let* ((gl (dk-goal))
       (agv (cadr (cadr gl))) (gv (caddr (cadr gl))) (nv (cadddr (cadr gl)))
       (hv  (caddr (caddr gl)))
       (phiv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                             (rkn-head? (caddr f) 'BIJECTION))) "phi"))))
  (dk-fact! 'abelian-group-is-group agv)
  (rkn-land-laws! agv
    (lambda () (dk-fact! 'group-identity-in agv) (ass))
    (rkn-law-by-cite! 2 (lambda (a b) (dk-fact! 'group-carrier-closed-opr agv a b)))
    (rkn-law-by-cite! 3 (lambda (a b c) (dk-fact! 'group-assoc agv a b c)))
    (rkn-law-by-cite! 2 (lambda (a b) (dk-fact! 'abelian-group-opr-comm agv a b))))
  (dk-fact! 'sum-ag-permutation-invariance-laws nv agv gv hv phiv)
  (ass))
(rkn-check! 'sum-ag-permutation-invariance)
(qed 'sum-ag-permutation-invariance)

(define rkn-pi-cm-stmt
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL m (IMPLIES (IS-COMM-MONOID m)
     (FORALL g (IMPLIES (IN g (FUN NN (CARR m)))
     (FORALL h (IMPLIES (IN h (FUN NN (CARR m)))
     (FORALL phi (IMPLIES (IN phi (BIJECTION (ORD-SEGMENT n) (ORD-SEGMENT n)))
       (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT n)) (= (h i) (g (phi i)))))
         (= (SUM-AG m g n) (SUM-AG m h n))))))))))))))
(sp (make-wff rkn-pi-cm-stmt))
(dk-peel!)
(let* ((gl (dk-goal))
       (mv (cadr (cadr gl))) (gv (caddr (cadr gl))) (nv (cadddr (cadr gl)))
       (hv (caddr (caddr gl)))
       (phiv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                             (rkn-head? (caddr f) 'BIJECTION))) "phi"))))
  (rkn-land-laws! mv
    (lambda () (dk-fact! 'comm-monoid-identity-in-carr mv) (ass))
    (rkn-law-by-cite! 2 (lambda (a b) (dk-fact! 'comm-monoid-carrier-closed-opr mv a b)))
    (lambda ()
      (mac-h 'is-comm-monoid (list 'IS-COMM-MONOID mv))
      (dk-split-all!)
      (mac-h 'is-associative (dk-pick (lambda (f) (rkn-head? f 'IS-ASSOCIATIVE)) "is-associative"))
      (ass))
    (lambda ()
      (mac-h 'is-comm-monoid (list 'IS-COMM-MONOID mv))
      (dk-split-all!)
      (mac-h 'is-commutative (dk-pick (lambda (f) (rkn-head? f 'IS-COMMUTATIVE)) "is-commutative"))
      (ass)))
  (dk-fact! 'sum-ag-permutation-invariance-laws nv mv gv hv phiv)
  (ass))
(rkn-check! 'finsum-comm-monoid-permutation-invariance)
(qed 'finsum-comm-monoid-permutation-invariance)

;; enum-fam-value, as a lane:  (ENUM-FAM ag u phi n)(i) == u(phi i)  for i in the
;; segment.  Needs (IN i NN) and (IN i (ORD-SEGMENT n)) in context.  Returns the
;; equation, which is then in the context.
(define (rkn-efv! agv fv phiv nv iv)
  (let ((eq (list '== (list (list 'ENUM-FAM agv fv phiv nv) iv) (list fv (list phiv iv)))))
    (have! eq (lambda ()
                (mac 'ENUM-FAM)
                (lam-b)
                (rkn-reduce-if! 'true (lambda (c) (equal? c (list 'IN iv (list 'ORD-SEGMENT nv)))))
                (qrfl)))
    eq))

;; the ENUM-FAM totality lane:  (IN (ENUM-FAM ag f phi n) (FUN NN (CARR ag))).
;; Needs (IN phi (FUN (ORD-SEGMENT n) S)), (IN f (FUN S (CARR ag))) and
;; (IN (IDEN ag) (CARR ag)) in the context -- the last is what the else-branch of
;; ENUM-FAM's guard produces, and it is the ONLY structure fact the totality uses.
(define (rkn-enum-fam-fun! agv fv phiv nv sv)
  (let ((claim (list 'IN (list 'ENUM-FAM agv fv phiv nv) (list 'FUN 'NN (list 'CARR agv)))))
    (have! claim
      (lambda ()
        (mac 'ENUM-FAM)
        (let* ((ls   (dk-opened (lambda () (lam-t))))
               (setl (rkn-leaf ls (lambda (g) (equal? g '(IN NN SET))) "NN in SET"))
               (ptw  (rkn-leaf ls (lambda (g) (rkn-head? g 'FORALL)) "pointwise typing")))
          (dk-focus! setl) (fact 'nn-is-set) (ass)
          (dk-focus! ptw)
          (let* ((iv  (dk-di-var!))
                 (pp  (list 'IN iv (list 'ORD-SEGMENT nv)))
                 (ift (list 'IF pp (list fv (list phiv iv)) (list 'IDEN agv))))
            (use-em pp
              (lambda ()
                (let* ((l (dk-opened (lambda () (if-true ift))))
                       (c (rkn-leaf l (lambda (g) (equal? g pp)) "if-true condition"))
                       (m (rkn-leaf l (lambda (g) (not (equal? g pp))) "if-true main")))
                  (dk-focus! c) (ass)
                  (dk-focus! m)
                  (subst (list '= ift (list fv (list phiv iv))))
                  (dk-fact! 'fun-apply-type-c phiv (list 'ORD-SEGMENT nv) sv iv)
                  (dk-fact! 'fun-apply-type-c fv sv (list 'CARR agv) (list phiv iv))
                  (ass)))
              (lambda ()
                (let* ((l (dk-opened (lambda () (if-false ift))))
                       (c (rkn-leaf l (dk-head? 'NOT) "if-false condition"))
                       (m (rkn-leaf l (lambda (g) (not ((dk-head? 'NOT) g))) "if-false main")))
                  (dk-focus! c) (ass)
                  (dk-focus! m)
                  (subst (list '= ift (list 'IDEN agv)))
                  (ass))))))) )
    claim))

;; the FUN projection of a BIJECTION membership, in a HAVE! lane -- `mac-h' is
;; destructive and the BIJECTION hypothesis is what the inverse facts detach against.
(define (rkn-bij-fun! bij)
  (let ((claim (list 'IN (cadr bij) (cons 'FUN (cdr (caddr bij))))))
    (have! claim (lambda () (rkn-open-bijection! bij) (ass)))
    claim))


;;; ===========================================================================
;;; 3.  finsum-well-defined -- FINSUM does not depend on the enumeration.
;;;
;;;   FINSUM(ag,f,S) = SUM-AG(ag, ENUM-FAM(ag,f,FIN-ENUM S,|S|), |S|)   (definition)
;;;
;;; and for ANY other enumeration enm the two folds differ by the permutation
;;;   psi = INVERSE-BIJ(enm) o FIN-ENUM S : OS(|S|) -> OS(|S|),
;;; which is exactly what sum-ag-permutation-invariance consumes: enm(psi i) =
;;; FIN-ENUM(S)(i) by inverse-bij-right, so the two enumerated families agree
;;; pointwise along psi.  CHAINS TO sum-ag-permutation-invariance (asserted).
;;; ===========================================================================

(define rkn-wd-stmt
  '(FORALL S
     (IMPLIES (IN S SET)
     (IMPLIES (IN (CARD S) NN)
     (FORALL ag
     (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL f
     (IMPLIES (IN f (FUN S (CARR ag)))
     (FORALL enm
     (IMPLIES (IN enm (BIJECTION (ORD-SEGMENT (CARD S)) S))
       (= (FINSUM ag f S)
          (SUM-AG ag (ENUM-FAM ag f enm (CARD S)) (CARD S)))))))))))))

(sp (make-wff rkn-wd-stmt))
(dk-peel!)
(let* ((gl   (dk-goal))
       (lhs  (cadr gl))                                  ; (FINSUM ag f S)
       (agv  (cadr lhs)) (fv (caddr lhs)) (sv (cadddr lhs))
       (nv   (list 'CARD sv))
       (seg  (list 'ORD-SEGMENT nv))
       (enmv (list-ref (caddr (caddr gl)) 3))            ; ENUM-FAM's phi slot
       (fe   (list 'FIN-ENUM sv))
       (inv  (list 'INVERSE-BIJ enmv seg sv))
       (psi  (list 'VNB-LAMBDA 'x_ seg (list inv (list fe 'x_))))
       (famE (list 'ENUM-FAM agv fv enmv nv))
       (famF (list 'ENUM-FAM agv fv fe nv)))
  (display ";; rkn wd: ") (display (list agv fv sv enmv)) (newline)
  (dk-fact! 'fin-enum-is-bijection sv)                   ; FE in BIJECTION(seg,S)
  (rkn-bij-fun! (list 'IN fe (list 'BIJECTION seg sv)))
  (rkn-bij-fun! (list 'IN enmv (list 'BIJECTION seg sv)))
  (dk-fact! 'inverse-bij-in-fun seg sv enmv)             ; inv in FUN(S, seg)
  (dk-fact! 'inverse-bij-is-bijection seg sv enmv)       ; inv in BIJECTION(S, seg)
  (have! (list 'AND (list 'IN fe (list 'BIJECTION seg sv))
                    (list 'IN inv (list 'BIJECTION sv seg)))
         (lambda () (dk-conj-close! (lambda () (ass)))))
  (dk-fact! 'bijection-compose seg sv seg fe inv)        ; psi in BIJECTION(seg,seg)
  (dk-fact! 'abelian-group-is-group agv)
  (dk-fact! 'group-identity-in agv)
  (rkn-enum-fam-fun! agv fv enmv nv sv)
  (rkn-enum-fam-fun! agv fv fe nv sv)
  (mac 'FINSUM)
  (display ";; goal now: ") (display (expression->string (dk-goal))) (newline)
  ;; the pointwise agreement famF(i) = famE(psi i) on the segment
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
                                 (list '= (list famF 'i_) (list famE (list psi 'i_)))))
    (lambda ()
      (let* ((landed (dk-peel!))
             (iv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                                 (equal? (caddr f) seg)))
                                "i in the segment"))))
        (dk-fact! 'ord-segment-nn-subset nv iv)                       ; (IN i NN)
        (dk-fact! 'fun-apply-type-c fe seg sv iv)                     ; (IN (FE i) S)
        (dk-fact! 'fun-apply-type-c fv sv (list 'CARR agv) (list fe iv))
        (lam-b)                                                       ; psi i -> inv(FE i)
        (dk-fact! 'fun-apply-type-c inv sv seg (list fe iv))          ; (IN (inv (FE i)) seg)
        (dk-fact! 'ord-segment-nn-subset nv (list inv (list fe iv)))
        (subst (rkn-efv! agv fv fe nv iv))
        (subst (rkn-efv! agv fv enmv nv (list inv (list fe iv))))
        (subst (dk-fact! 'inverse-bij-right seg sv enmv (list fe iv)))
        (rfl))))
  (dk-fact! 'sum-ag-permutation-invariance nv agv famE famF psi)
  (dk-fact! 'eq-sym (list 'SUM-AG agv famE nv) (list 'SUM-AG agv famF nv))
  (ass))
(rkn-check! 'finsum-well-defined)
(qed 'finsum-well-defined)

;;; ===========================================================================
;;; 4.  finsum-comm-monoid-well-defined -- the same argument over a COMMUTATIVE
;;; MONOID.  IS-COMM-MONOID pins a 3-slot tuple and IS-ABELIAN-GROUP a 4-slot one,
;;; so neither statement is an instance of the other and there is no view between
;;; them; but SUM-AG and ENUM-FAM read only CARR / OPR / IDEN, so the driver is
;;; the same one, with the identity-in-carrier fact taken from IS-COMM-MONOID's
;;; own unfold instead of from group-identity-in.
;;; CHAINS TO finsum-comm-monoid-permutation-invariance (asserted).
;;; ===========================================================================

;; The body of both well-definedness proofs.  IDEN-LANE! lands (IN (IDEN m) (CARR m));
;; PERM is the permutation-invariance theorem to cite.
(define (rkn-well-defined! iden-lane! perm)
  (dk-peel!)
  (let* ((gl   (dk-goal))
         (lhs  (cadr gl))
         (agv  (cadr lhs)) (fv (caddr lhs)) (sv (cadddr lhs))
         (nv   (list 'CARD sv))
         (seg  (list 'ORD-SEGMENT nv))
         (enmv (list-ref (caddr (caddr gl)) 3))
         (fe   (list 'FIN-ENUM sv))
         (inv  (list 'INVERSE-BIJ enmv seg sv))
         (psi  (list 'VNB-LAMBDA 'x_ seg (list inv (list fe 'x_))))
         (famE (list 'ENUM-FAM agv fv enmv nv))
         (famF (list 'ENUM-FAM agv fv fe nv)))
    (dk-fact! 'fin-enum-is-bijection sv)
    (rkn-bij-fun! (list 'IN fe (list 'BIJECTION seg sv)))
    (rkn-bij-fun! (list 'IN enmv (list 'BIJECTION seg sv)))
    (dk-fact! 'inverse-bij-in-fun seg sv enmv)
    (dk-fact! 'inverse-bij-is-bijection seg sv enmv)
    (have! (list 'AND (list 'IN fe (list 'BIJECTION seg sv))
                      (list 'IN inv (list 'BIJECTION sv seg)))
           (lambda () (dk-conj-close! (lambda () (ass)))))
    (dk-fact! 'bijection-compose seg sv seg fe inv)
    (iden-lane! agv)
    (rkn-enum-fam-fun! agv fv enmv nv sv)
    (rkn-enum-fam-fun! agv fv fe nv sv)
    (mac 'FINSUM)
    (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
                                   (list '= (list famF 'i_) (list famE (list psi 'i_)))))
      (lambda ()
        (dk-peel!)
        (let ((iv (cadr (dk-pick (lambda (f) (and (rkn-head? f 'IN) (symbol? (cadr f))
                                                  (equal? (caddr f) seg)))
                                 "i in the segment"))))
          (dk-fact! 'ord-segment-nn-subset nv iv)
          (dk-fact! 'fun-apply-type-c fe seg sv iv)
          (dk-fact! 'fun-apply-type-c fv sv (list 'CARR agv) (list fe iv))
          (lam-b)
          (dk-fact! 'fun-apply-type-c inv sv seg (list fe iv))
          (dk-fact! 'ord-segment-nn-subset nv (list inv (list fe iv)))
          (subst (rkn-efv! agv fv fe nv iv))
          (subst (rkn-efv! agv fv enmv nv (list inv (list fe iv))))
          (subst (dk-fact! 'inverse-bij-right seg sv enmv (list fe iv)))
          (rfl))))
    (dk-fact! perm nv agv famE famF psi)
    (dk-fact! 'eq-sym (list 'SUM-AG agv famE nv) (list 'SUM-AG agv famF nv))
    (ass)))

(define rkn-cm-wd-stmt
  '(FORALL S
     (IMPLIES (IN S SET)
     (IMPLIES (IN (CARD S) NN)
     (FORALL m
     (IMPLIES (IS-COMM-MONOID m)
     (FORALL f
     (IMPLIES (IN f (FUN S (CARR m)))
     (FORALL enm
     (IMPLIES (IN enm (BIJECTION (ORD-SEGMENT (CARD S)) S))
       (= (FINSUM m f S)
          (SUM-AG m (ENUM-FAM m f enm (CARD S)) (CARD S)))))))))))))

(sp (make-wff rkn-cm-wd-stmt))
(rkn-well-defined!
 (lambda (mv)
   (have! (list 'IN (list 'IDEN mv) (list 'CARR mv))
          (lambda () (mac-h 'is-comm-monoid (list 'IS-COMM-MONOID mv))
                     (dk-split-all!) (ass))))
 'finsum-comm-monoid-permutation-invariance)
(rkn-check! 'finsum-comm-monoid-well-defined)
(qed 'finsum-comm-monoid-well-defined)
