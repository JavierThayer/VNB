;;; zz-ring-is-ring.scm -- IS-RING(ZZ-RING), PROVED.
;;;
;;; It was an asserted axiom (numeric-instances.scm, `zz-is-ring'), and it showed
;;; up in the bill of every theorem that reached the integers through their ring
;;; structure -- including every transported one.  It should never have been an
;;; assertion: everything it needs is already written down as basic arithmetic.
;;;
;;;   the shape   ZZ-RING = LIST(ZZ, binplus, bintimes, binneg, 0, 1)  (definitional)
;;;   the typings binplus-in-fun-zz : binplus in FUN(ZZ x ZZ, ZZ), and siblings
;;;   the laws    zz-add-assoc, zz-add-comm, zz-mul-comm, zz-distributive, ...
;;;
;;; IS-RING is an IFF (declare-structure builds it), so the proof is: unfold it,
;;; push the accessors down to the surface language -- (ADD ZZ-RING) == binplus,
;;; binplus(x,y) == x + y, both now THEOREMS (see transport.scm) -- and the
;;; fourteen conjuncts become the ordinary arithmetic of the integers.  The seven
;;; law conjuncts are ring identities over typed generators, which is exactly
;;; what `crs' decides.
;;;
;;; This is the payoff of the transport work turned around: transport! rewrites a
;;; landed FACT into the surface language; here surface-goal! rewrites the GOAL.
;;;
;;; 2026-08-10: the file proves the SAME theorem for QQ-RING as well, so its name
;;; is now historical.  QQ-RING is (QQ binplus bintimes binneg 0 1) -- the same
;;; tuple over a different carrier -- and `qq-is-ring' was the other asserted
;;; instance, one of the last unwarranted leaves in the ledger.  The driver
;;; below is therefore PARAMETERISED over the instance rather than copied: the
;;; ring name, its carrier, its defining equation and its three typing axioms
;;; are arguments, and everything else is shared.  A third numeric ring would be
;;; one more call.

(define (zr-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (zr-leaves) (proof-open-goals *ps*))
(define (zr-head g) (and (pair? g) (car g)))

;;; Per-instance data: carrier, defining equation, the set-hood fact, and the
;;; three membership conjuncts (each an axiom of number-systems /
;;; numeric-instances).
;;; 2026-08-29: the last field was a map from the shared bridge CONSTANT to its
;;; FUN-membership axiom (binplus -> binplus-in-fun-zz, ...).  Those axioms are
;;; GONE: one object cannot be a set function with five different domains, and
;;; asserting so proved ZZ = QQ = RR = CC and thence FALSITY.  The slots now hold
;;; a tupled VNB-LAMBDA per instance (numeric-instances.scm), so the op-slot
;;; typing is PROVED by lam-t, and the field below maps the lambda body's
;;; OPERATION HEAD to the carrier's closure axiom -- which is what those typings
;;; were always a mis-encoding of (numeric-instances.scm said so in prose).
(define zr-instances
  '((ZZ-RING ZZ zz-ring-def zz-is-set zz-is-ring
     ((+ . zz-add-closed) (* . zz-mul-closed) (- . zz-neg-closed)))
    (QQ-RING QQ qq-ring-def qq-is-set qq-is-ring
     ((+ . qq-add-closed) (* . qq-mul-closed) (- . qq-neg-closed)))))

;;; The op-slot typing  IN (VNB-LAMBDA ...) (FUN dom rng),  proved not cited.
;;; `lam-t' opens exactly two leaves: the pointwise typing of the body -- the
;;; carrier's closure axiom, verbatim -- and SETHOOD of the domain.  Both are
;;; already in the tree; nothing new is asserted.
;;;
;;; TAKE THE LEAVES `lam-t' OPENED, never search the open leaves by SHAPE.  The
;;; other thirteen conjuncts of IS-RING are still open at this point and three of
;;; them are `IN' goals -- a shape search picked up MUL's typing while closing
;;; ADD's, and the driver then rewrote the wrong branch and failed several steps
;;; later, blaming the conjunct it had started on.  `dk-opened' is what the rest
;;; of this file already uses for exactly this reason.
(define (zr-close-lambda-typing! ring g)
  (let* ((carrier (cadr ring))
         (setfact (cadddr ring))
         (closure (list-ref ring 5))
         (lam     (cadr g))
         (binder  (cadr lam))
         (body    (cadddr lam))
         (thm     (cdr (assq (car body) closure)))
         (tupled? (and (pair? binder) (eq? (car binder) 'LIST)))
         (opened  (dk-opened (lambda () (lam-t)))))
    (define (pick head)
      (let ((hit (filter (lambda (n)
                           (let ((gg (wff-formula (sequent-node-assertion n))))
                             (and (pair? gg) (eq? (car gg) head))))
                         opened)))
        (and (pair? hit) (dk-focus! (car hit)))))
    (if (null? opened)
        (error "zz-ring-is-ring: lam-t opened nothing on" g))
    ;; leaf 1 -- pointwise: forall <args> in carrier. op(<args>) in carrier
    (when (pick 'FORALL)
      (di)
      (let* ((g2 (zr-goal)) (term (cadr g2)) (args (cdr term)))
        (if (pair? (cdr args))
            (begin (dk-have! (list 'AND (list 'IN (car args)  carrier)
                                     (list 'IN (cadr args) carrier)))
                   (fact thm (car args) (cadr args)))
            (fact thm (car args))))
      (ass))
    ;; leaf 2 -- SETHOOD of the domain, and it is not always opened: sequent
    ;; nodes are hash-consed, so when a sibling conjunct has already posted the
    ;; identical `CARTESIAN(c,c) in SET' under the identical context, lam-t
    ;; posts no new node and dk-opened correctly reports one leaf, not two.
    ;; Closing it is therefore conditional -- never assume an arity of leaves.
    (when (pick 'IN)
      (fact setfact)
      (when tupled?
        (dk-have! (list 'AND (list 'IN carrier 'SET) (list 'IN carrier 'SET)))
        (mac 'cartesian-set-iff))
      (ass))))


;;; The slot-application saturation lives in driver-kit.scm (dk-saturate-slot-ops!)
;;; since nn-add-monoid.scm needs it too -- CLAUDE.md's rule: one file, keep it
;;; local; two files, it belongs in the kit.

;;; Discharge the FOCUSED conjunct of instance RING (the zr-instances entry).
;;; Every branch is decided by the goal's own shape -- there is no search here,
;;; and no leaf is left to luck.
(define (zr-close-leaf! ring)
  (let ((name   (car ring))    (carrier (cadr ring))
        (defn   (caddr ring))  (setfact (cadddr ring))
        (g      (zr-goal)))
    (cond
      ;; length(<ring>) = 6 : unfold the tuple, reduce LENGTH, compute.
      ((and (eq? (zr-head g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
       (mac defn) (len-r) (arith))
      ;; (IN 0 <carrier>) / (IN 1 <carrier>) : ground, so `arith' decides them.
      ((and (eq? (zr-head g) 'IN) (number? (cadr g)))
       (arith))
      ;; (IN <carrier> SET)
      ((equal? g (list 'IN carrier 'SET))
       (fact setfact) (ass))
      ;; (IN (VNB-LAMBDA ...) (FUN ...)) -- the op-slot typing, PROVED by lam-t.
      ((and (eq? (zr-head g) 'IN)
            (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
       (zr-close-lambda-typing! ring g))
      ;; a law: is-associative / is-commutative / is-identity / has-inverses /
      ;; is-distributive.  Unfold it, drop to the surface, peel, and let `crs'
      ;; decide the ring identity.  (di splits the AND goals of is-identity /
      ;; has-inverses / is-distributive; each half is again a ring identity.)
      ((memq (zr-head g) '(is-associative is-commutative is-identity
                           has-inverses is-distributive))
       (mac (zr-head g))
       ;; `quietly' here silences the STATE DUMP only: surface-goal! prints the
       ;; whole fourteen-conjunct goal after every rewrite otherwise, and the
       ;; run drowns in it.  It is safe because surface-goal! does not rely on a
       ;; tactic silently succeeding -- it computes each rewrite itself first and
       ;; errors if the rules do not reach a fixpoint -- and because the proof
       ;; below refuses to qed unless every leaf actually closed.
       (quietly (lambda () (surface-goal! name)))
       ;; Peel the typed binders.  GUARD ON PROGRESS: `di' only WARNS when it
       ;; cannot decompose, so "loop while the head is FORALL/IMPLIES" spins
       ;; forever the moment it no-ops.  Loop while the goal CHANGES.
       (let peel ((fuel 20))
         (let ((before (zr-goal)))
           (when (and (> fuel 0) (memq (zr-head before) '(FORALL IMPLIES)))
             (di)
             (if (equal? (zr-goal) before)
                 (error "zz-ring-is-ring: di made no progress on" before)
                 (peel (- fuel 1))))))
       (let close ((fuel 20))
         (let ((g2 (zr-goal)))
           (cond
             ((<= fuel 0) (error "zz-ring-is-ring: AND split did not terminate"))
             ((eq? (zr-head g2) 'AND)
              (for-each (lambda (k) (dk-focus! k) (close (- fuel 1)))
                        (dk-opened (lambda () (di)))))
             (else (dk-saturate-slot-ops! carrier (list-ref ring 5)) (crs))))))
      (else (error "zz-ring-is-ring: unexpected conjunct" g)))))

;;; A genuine open LEAF: ungrounded AND no rule has fired on it.  proof-open-goals
;;; also lists ANCESTORS (a node stays ungrounded while any descendant is open),
;;; so searching it for an AND goal keeps finding the already-split conjunction
;;; and re-splitting it, forever.  That is what hung this proof twice.
(define (zr-open) (filter (lambda (s) (null? (sequent-node-in-arrows s))) (zr-leaves)))

;;; The whole proof, for one instance.
(define (zr-prove! ring)
  (let ((name (car ring)) (result (list-ref ring 4)))
    (sp (make-wff (list 'IS-RING name)))
    (mac 'IS-RING)                                    ; the definitional IFF
    (quietly (lambda () (surface-goal! name)))        ; carr(r) -> ZZ, add(r) -> binplus, ...
    ;; Split the conjunction to leaves, then close each by its shape.
    (let split ((fuel 40))
      (let ((andl (find-first (lambda (s)
                                (eq? (zr-head (wff-formula (sequent-node-assertion s))) 'AND))
                              (zr-open))))
        (when andl
          (if (= fuel 0) (error "zz-ring-is-ring: AND split did not terminate"))
          (dk-focus! andl) (di) (split (- fuel 1)))))
    ;; Close each conjunct.  The sweep insists on PROGRESS: if a pass leaves the
    ;; open-leaf count unchanged, the leaf did not close and we say which one,
    ;; rather than re-focusing it forever.
    (let sweep ((fuel 40))
      (let* ((open (zr-open))
             (n    (length open)))
        (when (pair? open)
          (if (= fuel 0) (error "zz-ring-is-ring: sweep out of fuel"))
          (dk-focus! (car open))
          (let ((g (zr-goal)))
            (zr-close-leaf! ring)
            (let ((n* (length (zr-open))))
              (if (>= n* n)
                  (error "zz-ring-is-ring: this conjunct did not close" g))))
          (sweep (- fuel 1)))))
    (if (proof-done? *ps*)
        (qed result)      ; the name the AXIOM had: every citation keeps working
        (begin
          (display "\n*** zz-ring-is-ring did NOT close for ")
          (display name) (display ".  Open goals:\n")
          (for-each (lambda (l)
                      (display "   GOAL: ")
                      (display (expression->string (wff-formula (sequent-node-assertion l))))
                      (newline))
                    (zr-leaves))
          (error "zz-ring-is-ring: unfinished" name)))))

(for-each zr-prove! zr-instances)
