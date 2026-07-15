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

(define (zr-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (zr-leaves) (proof-open-goals *ps*))
(define (zr-head g) (and (pair? g) (car g)))

;;; The membership conjuncts, each an axiom of number-systems / numeric-instances.
(define zr-typing-axioms
  '((binplus  . binplus-in-fun-zz)
    (bintimes . bintimes-in-fun-zz)
    (binneg   . binneg-in-fun-zz)))

;;; Discharge the FOCUSED conjunct.  Every branch is decided by the goal's own
;;; shape -- there is no search here, and no leaf is left to luck.
(define (zr-close-leaf!)
  (let ((g (zr-goal)))
    (cond
      ;; length(zz-ring) = 6 : unfold the tuple, reduce LENGTH, compute.
      ((and (eq? (zr-head g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
       (mac 'zz-ring-def) (len-r) (arith))
      ;; (IN 0 ZZ) / (IN 1 ZZ) : ground, so `arith' decides them.
      ((and (eq? (zr-head g) 'IN) (number? (cadr g)))
       (arith))
      ;; (IN ZZ SET)
      ((equal? g '(IN ZZ SET))
       (fact 'zz-is-set) (ass))
      ;; (IN binplus (FUN ...)) and siblings
      ((and (eq? (zr-head g) 'IN) (assq (cadr g) zr-typing-axioms))
       => (lambda (hit) (fact (cdr hit)) (ass)))
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
       (quietly (lambda () (surface-goal! 'ZZ-RING)))
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
             (else (crs))))))
      (else (error "zz-ring-is-ring: unexpected conjunct" g)))))

(sp (make-wff '(IS-RING ZZ-RING)))
(mac 'IS-RING)                       ; the definitional IFF
(quietly (lambda () (surface-goal! 'ZZ-RING)))   ; carr(zz-ring) -> zz, add(zz-ring) -> binplus, ...

;;; A genuine open LEAF: ungrounded AND no rule has fired on it.  proof-open-goals
;;; also lists ANCESTORS (a node stays ungrounded while any descendant is open),
;;; so searching it for an AND goal keeps finding the already-split conjunction
;;; and re-splitting it, forever.  That is what hung this proof twice.
(define (zr-open) (filter (lambda (s) (null? (sequent-node-in-arrows s))) (zr-leaves)))

;;; Split the conjunction to leaves, then close each by its shape.
(let split ((fuel 40))
  (let ((andl (find-first (lambda (s)
                            (eq? (zr-head (wff-formula (sequent-node-assertion s))) 'AND))
                          (zr-open))))
    (when andl
      (if (= fuel 0) (error "zz-ring-is-ring: AND split did not terminate"))
      (dk-focus! andl) (di) (split (- fuel 1)))))

;;; Close each conjunct.  The sweep insists on PROGRESS: if a pass leaves the
;;; open-leaf count unchanged, the leaf did not close and we say which one,
;;; rather than re-focusing it forever.
(let sweep ((fuel 40))
  (let* ((open (zr-open))
         (n    (length open)))
    (when (pair? open)
      (if (= fuel 0) (error "zz-ring-is-ring: sweep out of fuel"))
      (dk-focus! (car open))
      (let ((g (zr-goal)))
        (zr-close-leaf!)
        (let ((n* (length (zr-open))))
          (if (>= n* n)
              (error "zz-ring-is-ring: this conjunct did not close" g))))
      (sweep (- fuel 1)))))

(if (proof-done? *ps*)
    (qed 'zz-is-ring)        ; the name the AXIOM had: every citation keeps working
    (begin
      (display "\n*** zz-ring-is-ring did NOT close.  Open goals:\n")
      (for-each (lambda (l)
                  (display "   GOAL: ")
                  (display (expression->string (wff-formula (sequent-node-assertion l))))
                  (newline))
                (zr-leaves))
      (error "zz-ring-is-ring: unfinished")))
