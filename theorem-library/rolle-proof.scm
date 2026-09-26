;;; theorem-library/rolle-proof.scm -- Rolle's theorem, MACHINE-PROVEN.
;;; EVT gives argmax c / argmin d on [a,b]; if either is interior, the
;;; proven Fermat theorem (interior-max/min-deriv-zero) gives h'=0; else h is
;;; constant and a midpoint (rr-midpoint-between) is an interior max.
;;; Loads after interior-extremum-proof.scm.  Uses bc* -> compile auto-skips.
;;; ====================================================================
;;; RETIRED 2026-09-14 (proven): rr-midpoint-between -- theorem-library/rr-order-bundle.scm
;;; RETIRED 2026-09-14 (proven): max-val-strict-interior -- theorem-library/mvt-cluster-readoffs.scm
;;; RETIRED 2026-09-14 (proven): min-val-strict-interior -- theorem-library/mvt-cluster-readoffs.scm

(define (rl-gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (rl-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (rl-find pred) (let loop ((as (rl-asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (rl-head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (rl-ment? sym form) (cond ((eq? form sym) #t)
  ((pair? form) (or (rl-ment? sym (car form)) (rl-ment? sym (cdr form)))) (else #f)))
(define (rl-split) (let loop ((n 0)) (let ((a (rl-find (rl-head? 'AND))))
  (cond ((and a (< n 12)) (ai a) (loop (+ n 1))) (else n)))))
(define (rl-focus! raw) (let ((s (any-pred (lambda (s) (equal? (wff-formula (sequent-node-assertion s)) raw)) (proof-leaves))))
  (if s (begin (dk-focus! s) s) (error "rl-focus!: none equal" (expression->string raw)))))
(define (rl-grind!) (let loop ((g 0)) (quietly (lambda () (ass-all)))
  (let ((al (any-pred (lambda (s) (let ((gg (wff-formula (sequent-node-assertion s))))
              (and (not (sequent-node-grounded? s)) (pair? gg) (eq? (car gg) 'AND)))) (proof-leaves))))
    (when (and al (< g 40)) (dk-focus! al) (di) (loop (+ g 1))))))
(define (rl-dump tag) (display ";;; [")(display tag)(display "] done?=")(display (proof-done? *ps*))
  (display " leaves=")(display (length (proof-leaves)))(newline)
  (display ";;;   goal=")(write (rl-gf))(newline)
  (for-each (lambda (a) (display ";;;     - ")(write a)(newline)) (rl-asms)))

;;; --- order helpers (well-known) ---

;;; --- pose Rolle ---
(sp '(FORALL h (FORALL a (FORALL b
     (IMPLIES (AND (IN h (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b))
                 (IS-CONTINUOUS-AT RR-MS RR-MS h x)))
     (IMPLIES (FORALL x (IMPLIES (AND (IN x RR) (AND (< a x) (< x b)))
                 (FORSOME L (IS-DIFF-AT h x L))))
     (IMPLIES (= (h a) (h b))
       (FORSOME theta (AND (IN theta RR) (AND (< a theta) (AND (< theta b)
                      (IS-DIFF-AT h theta 0)))))))))))))
(quietly (lambda () (di)(di)(di)))         ; h,a,b
(rl-split)                                 ; break typing AND -> h in FUN, a,b in RR, a<b
(quietly (lambda () (di)(di)(di)))         ; continuity hyp, diff hyp, h(a)=h(b)
(quietly (lambda () (fact 'rr-lt-implies-le 'a 'b)))   ; a <= b for EVT
(define GOAL '(FORSOME theta (AND (IN theta RR) (AND (< a theta) (AND (< theta b) (IS-DIFF-AT h theta 0))))))

;;; EVT-max -> argmax c
(define EVTMAX (list 'FORSOME 'c (list 'AND '(IN c (CCINT a b))
                  (list 'FORALL 'x (list 'IMPLIES '(IN x (CCINT a b))
                    (list '<= '(h x) '(h c)))))))
(cut EVTMAX)
(rl-focus! EVTMAX)
(bc* 'extreme-value-max)
(rl-grind!)
(rl-focus! GOAL)
(ai EVTMAX)                                ; skolemize c
(rl-split)                                 ; (IN c (CCINT a b)), max-forall
;;; EVT-min -> argmin d
(define EVTMIN (list 'FORSOME 'd (list 'AND '(IN d (CCINT a b))
                  (list 'FORALL 'x (list 'IMPLIES '(IN x (CCINT a b))
                    (list '<= '(h d) '(h x)))))))
(cut EVTMIN)
(rl-focus! EVTMIN)
(bc* 'extreme-value-min)
(rl-grind!)
(rl-focus! GOAL)
(ai EVTMIN)                                ; skolemize d
(rl-split)

;;; capture skolems + key asms
(define (rl-deep pred form) (cond ((pred form) form)
  ((pair? form) (or (rl-deep pred (car form)) (rl-deep pred (cdr form)))) (else #f)))
(define MAXF (rl-find (lambda (a) (and ((rl-head? 'FORALL) a)
              (rl-deep (lambda (z) (and (pair? z) (eq? (car z) '<=) (equal? (cadr z) '(h x)))) a)))))
(define MINF (rl-find (lambda (a) (and ((rl-head? 'FORALL) a)
              (rl-deep (lambda (z) (and (pair? z) (eq? (car z) '<=) (equal? (caddr z) '(h x)))) a)))))
(define CMAX (cadr (caddr (caddr (caddr MAXF)))))   ; the c in (<= (h x) (h c))
(define CMIN (cadr (cadr  (caddr (caddr MINF)))))   ; the d in (<= (h d) (h x))
(define DIFFHYP (rl-find (lambda (a) (and ((rl-head? 'FORALL) a) (rl-ment? 'is-diff-at a)))))
(display ";;; CMAX=")(write CMAX)(display " CMIN=")(write CMIN)(newline)

;;; rr-midpoint-between: open interval nonempty (for the constant case)

;;; establish (IN a (CCINT a b)) and h(a)<=h(c), h(d)<=h(a)
(define (rl-have! mem main) (cut mem) (rl-focus! mem) (in-rr) (rl-focus! main))
(define (rl-focus-asm! form)
  (let ((s (any-pred (lambda (s) (any-pred (lambda (w) (equal? (wff-formula w) form))
                                           (sequent-node-assumptions s))) (proof-leaves))))
    (if s (begin (dk-focus! s) s) (error "rl-focus-asm!: none" form))))
;; (IN p RR) from (IN p (CCINT a b)), without destroying the membership (mac-h
;; runs only on the cut subgoal's branch); also leaves a<=p, p<=b there but the
;; main branch keeps the original membership.
(define (rl-type-ccint p main)
  (cut (list 'IN p 'RR))
  (rl-focus! (list 'IN p 'RR))
  (mac-h 'ccint-membership (list 'IN p '(CCINT a b)))
  (rl-split)
  (quietly (lambda () (ass-all)))
  (rl-focus! main))
(cut '(IN a (CCINT a b)))
(rl-focus! '(IN a (CCINT a b)))
(mac 'ccint-membership) (quietly (lambda () (fact 'rr-leq-reflexive 'a))) (rl-grind!)
(rl-focus! GOAL)
(quietly (lambda () (inst+ MAXF 'a) (inst+ MINF 'a)))   ; h(a)<=h(c) ; h(d)<=h(a)
;; type c, d in RR (from membership), then the function values
(rl-type-ccint CMAX GOAL)
(rl-type-ccint CMIN GOAL)
(rl-have! '(IN (h a) RR) GOAL)
(rl-have! (list 'IN (list 'h CMAX) 'RR) GOAL)
(rl-have! (list 'IN (list 'h CMIN) 'RR) GOAL)

;;; interior-position helpers (well-known; curried so `fact` detaches)

;;; ====== witness sub-routines (marker = the case-distinguishing asm) ======
;; focus the leaf whose GOAL is the Rolle goal AND which carries `marker`
(define (rl-focus-case! marker)
  (let ((s (any-pred (lambda (s)
                       (and (equal? (wff-formula (sequent-node-assertion s)) GOAL)
                            (any-pred (lambda (w) (equal? (wff-formula w) marker))
                                      (sequent-node-assumptions s))))
                     (proof-leaves))))
    (if s (begin (dk-focus! s) s) (error "rl-focus-case!: none" marker))))
;; The differentiability hypothesis is TYPED (its antecedent carries (IN x RR)),
;; so the interior-position AND we detach it against carries the typing too.
(define (rl-interior p) (list 'AND (list 'IN p 'RR) (list 'AND (list '< 'a p) (list '< p 'b))))
(define (rl-deriv-from p marker)
  (cut (rl-interior p))
  (rl-focus! (rl-interior p))
  (quietly (lambda () (rl-grind!)))       ; split the AND; every conjunct is in ctx
  (rl-focus-case! marker)
  (inst+ DIFFHYP p)
  (let ((fs (rl-find (lambda (z) (and ((rl-head? 'FORSOME) z) (rl-ment? 'is-diff-at z) (rl-ment? p z))))))
    (ai fs))
  (cadddr (rl-find (lambda (z) (and ((rl-head? 'IS-DIFF-AT) z) (equal? (caddr z) p))))))
(define (rl-finish-zero p Lp marker)
  (rl-focus-case! marker)
  (cut (list 'IS-DIFF-AT 'h p 0))
  (rl-focus! (list 'IS-DIFF-AT 'h p 0))
  (quietly (lambda () (fact 'eq-symm Lp 0)))
  (subst (list '= 0 Lp))
  (quietly (lambda () (ass-all)))
  (rl-focus-case! marker)
  (ew p)
  (rl-grind!))
(define (rl-wit p marker thm)
  (let ((Lp (rl-deriv-from p marker)))
    (cut (list '= Lp 0))
    (rl-focus! (list '= Lp 0))
    (if (eq? thm 'max)
        (bc* 'interior-max-deriv-zero ((f 'h) (a 'a) (b 'b) (theta p)))
        (bc* 'interior-min-deriv-zero ((f 'h) (a 'a) (b 'b) (theta p))))
    (rl-grind!)
    (rl-finish-zero p Lp marker)))

(define MI   (list '< (list 'h 'a) (list 'h CMAX)))   ; case I marker
(define MII  (list '= (list 'h 'a) (list 'h CMAX)))   ; case II marker
(define MIIA (list '< (list 'h CMIN) (list 'h 'a)))   ; case II.A marker
(define MIIB (list '= (list 'h CMIN) (list 'h 'a)))   ; case II.B marker

;;; ====== split 1: h(a) vs h(c) ======
(quietly (lambda () (fact 'rr-le-cases (list 'h 'a) (list 'h CMAX))))
(ai (rl-find (lambda (z) (and ((rl-head? 'OR) z) (rl-ment? CMAX z)))))

;;; --- CASE I: h(a) < h(c) -> c interior, max ---
(rl-focus-case! MI)
(quietly (lambda () (fact 'max-val-strict-interior 'h 'a 'b CMAX)))
(rl-split)
(rl-wit CMAX MI 'max)

;;; ====== split 2 (inside case II): h(d) vs h(a) ======
(rl-focus-case! MII)
(quietly (lambda () (fact 'rr-le-cases (list 'h CMIN) (list 'h 'a))))
(ai (rl-find (lambda (z) (and ((rl-head? 'OR) z) (rl-ment? CMIN z)))))

;;; --- CASE II.A: h(d) < h(a) -> d interior, min ---
(rl-focus-case! MIIA)
(quietly (lambda () (fact 'min-val-strict-interior 'h 'a 'b CMIN)))
(rl-split)
(rl-wit CMIN MIIA 'min)

;;; --- CASE II.B: h(d) = h(a) = h(c): h constant; midpoint is an interior max ---
(rl-focus-case! MIIB)
(quietly (lambda () (fact 'rr-midpoint-between 'a 'b)))
(let ((fs (rl-find (lambda (z) (and ((rl-head? 'FORSOME) z)
              (rl-deep (lambda (y) (and (pair? y)(eq?(car y) '<)(eq?(cadr y) 'a))) z)))))) (ai fs))
(rl-split)
(define MM (caddr (rl-find (lambda (z) (and (pair? z) (eq? (car z) '<) (eq? (cadr z) 'a) (symbol? (caddr z))
              (rl-find (lambda (y) (and (pair? y)(eq?(car y) '<)(equal?(cadr y)(caddr z))(eq?(caddr y) 'b)))))))))
(display ";;; MM=")(write MM)(newline)
;; m in [a,b]
(cut (list 'IN MM '(CCINT a b)))
(rl-focus! (list 'IN MM '(CCINT a b)))
(mac 'ccint-membership)
(quietly (lambda () (fact 'rr-lt-implies-le 'a MM) (fact 'rr-lt-implies-le MM 'b)))
(rl-grind!)
(rl-focus-case! MIIB)
;; type h(m); inst the EVT conditions at m
(define (rl-have-case! mem marker) (cut mem) (rl-focus! mem) (in-rr) (rl-focus-case! marker))
(rl-have-case! (list 'IN (list 'h MM) 'RR) MIIB)
(quietly (lambda () (inst+ MAXF MM) (inst+ MINF MM)))   ; h(m)<=h(c) ; h(d)<=h(m)
;; h(c)=h(d):  from h(a)=h(c) [MII] and h(d)=h(a) [MIIB]
(cut (list '= (list 'h CMIN) (list 'h CMAX)))
(rl-focus! (list '= (list 'h CMIN) (list 'h CMAX)))
(subst (list '= (list 'h CMIN) (list 'h 'a)))   ; goal -> (= (h a)(h c)) = MII
(quietly (lambda () (ass-all)))
(rl-focus-case! MIIB)
;; h(c)<=h(m):  rewrite to h(d)<=h(m)
(cut (list '<= (list 'h CMAX) (list 'h MM)))
(rl-focus! (list '<= (list 'h CMAX) (list 'h MM)))
(quietly (lambda () (fact 'eq-symm (list 'h CMIN) (list 'h CMAX))))   ; (= (h c)(h d))
(subst (list '= (list 'h CMAX) (list 'h CMIN)))   ; goal -> (<= (h d)(h m))
(quietly (lambda () (ass-all)))
(rl-focus-case! MIIB)
;; h(m)=h(c) by antisymmetry (h(m)<=h(c) and h(c)<=h(m))
(cut (list '= (list 'h MM) (list 'h CMAX)))
(rl-focus! (list '= (list 'h MM) (list 'h CMAX)))
(bc* 'rr-leq-antisymmetric)
(rl-grind!)
(rl-focus-case! MIIB)
;; maxcond for m:  forall x in [a,b], h(x) <= h(m)
(define MAXCONDM (list 'FORALL 'x (list 'IMPLIES '(IN x (CCINT a b))
                  (list '<= '(h x) (list 'h MM)))))
(cut MAXCONDM)
(rl-focus! MAXCONDM)
(di) (di)
(quietly (lambda () (inst+ MAXF 'x)))       ; h(x)<=h(c)
(subst (list '= (list 'h MM) (list 'h CMAX)))   ; goal (<= (h x)(h m)) -> (<= (h x)(h c))
(quietly (lambda () (ass-all)))
(rl-focus-case! MIIB)
(rl-wit MM MIIB 'max)

(qed 'rolle)
(topic! 'rolle 'analysis)
