;;; ringoid-setoid-proof.scm
;;;
;;; The congruence of a ringoid is an equivalence relation.
;;;
;;; A RINGOID is a ring (its own slots CARR/ADD/MUL/NEG/ZERO/ONE) with a distinguished
;;; two-sided ideal IDL.  Its congruence RINGOID-REL(r) relates a,b iff  a - b in IDL --
;;; concretely the SEP of pairs { p in CARR x CARR : (a - b) in IDL }, a = NTH 1 p,
;;; b = NTH 2 p.  We prove it is an equivalence relation on CARR(r):
;;;
;;;   reflexivity   a - a = 0 in I            (ringoid-add-right-inv, ringoid-ideal-zero)
;;;   symmetry      a-b in I => -(a-b)=b-a in I   (ringoid-ideal-neg, ringoid-neg-diff)
;;;   transitivity  (a-b)+(b-c)=a-c in I       (ringoid-ideal-add, ringoid-diff-telescope)
;;;   typing        the SEP is a subset of CARR x CARR, hence in its powerset.
;;;
;;; ringoid-neg-diff / ringoid-diff-telescope are asserted `well-known' in ringoid.scm:
;;; crs normalizes surface +/* but does NOT reach a structure's abstract (ADD s)/(NEG s)
;;; (the abstract-ring additive-normalizer gap).  Everything else is derived; membership
;;; in the congruence is unfolded through the definitional IFF ringoid-rel-mem (mac-h
;;; cannot unfold the RINGOID-REL functoid in an assumption).

;;; ---- file-local driver helpers ----
(define (rg-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (rg-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (rg-gof l) (wff-formula (sequent-node-assertion l)))
(define (rg-foc! pred)
  (dk-focus! (or (any-pred (lambda (l) (pred (rg-gof l))) (proof-leaves))
                 (error "ringoid-setoid: no leaf matching predicate"))))
(define (rg-split-goal!)                      ; recursively di every AND-goal leaf
  (let loop ((n 0))
    (let ((al (any-pred (lambda (l) (let ((g (rg-gof l))) (and (pair? g) (eq? (car g) 'AND))))
                        (proof-leaves))))
      (when (and al (< n 8)) (dk-focus! al) (vnb-guard (lambda () (di))) (loop (+ n 1))))))
(define (rg-refl-leaf? g)                     ; forall u. ... => [u,u] in rel
  (and (pair? g) (eq? (car g) 'FORALL)
       (let ((m (caddr g)))
         (and (pair? m) (eq? (car m) 'IMPLIES)
              (let ((c (caddr m))) (and (pair? c) (eq? (car c) 'IN) (pair? (cadr c)) (eq? (car (cadr c)) 'LIST)))))))
(define (rg-sym-leaf? g)                       ; forall u,v. ... => ([u,v] in rel => [v,u] in rel)
  (and (pair? g) (eq? (car g) 'FORALL)
       (let ((m (caddr g))) (and (pair? m) (eq? (car m) 'IMPLIES)
         (let ((c (caddr m))) (and (pair? c) (eq? (car c) 'FORALL)
           (let ((m2 (caddr c))) (and (pair? m2) (eq? (car m2) 'IMPLIES)
             (let ((c2 (caddr m2))) (and (pair? c2) (eq? (car c2) 'IMPLIES)))))))))))
(define (rg-typingB-leaf? g)                   ; forall z. z in {SEP} => z in cart
  (and (pair? g) (eq? (car g) 'FORALL)
       (let ((m (caddr g))) (and (pair? m) (eq? (car m) 'IMPLIES)
         (let ((a (cadr m))) (and (pair? a) (eq? (car a) 'IN) (pair? (caddr a)) (eq? (car (caddr a)) 'SEP)))))))
(define rg-ADDu-u (list '= (list (list 'ADD 'r) 'u (list (list 'NEG 'r) 'u)) (list 'ZERO 'r)))
(define rg-Xsym (list (list 'ADD 'r) 'u (list (list 'NEG 'r) 'v)))          ; u-v
(define rg-Xuv  (list (list 'ADD 'r) 'u (list (list 'NEG 'r) 'v)))          ; u-v
(define rg-Xvw  (list (list 'ADD 'r) 'v (list (list 'NEG 'r) 'w)))          ; v-w
(define rg-Xuw  (list (list 'ADD 'r) 'u (list (list 'NEG 'r) 'w)))          ; u-w

;;; ================= ringoid-rel-is-equivalence =================
(sp (make-wff '(FORALL r (IMPLIES (IS-RINGOID r) (is-equivalence (RINGOID-REL r) (CARR r))))))
(di)(di)
(fact 'ringoid-carr-in-set 'r)                ; carr(r) in set
(mac 'is-equivalence)
(rg-split-goal!)

;;; ---- reflexivity: [u,u] in rel, since u-u = 0 in I ----
(rg-foc! rg-refl-leaf?)
(di)(di)
(mac 'RINGOID-REL)
(define rg-refl-kids (dk-opened (lambda () (sep-mi))))
(for-each
  (lambda (l)
    (dk-focus! l)
    (let ((g (rg-goal)))
      (if (and (pair? g) (eq? (car g) 'IN) (equal? (caddr g) '(IDL r)))
          (begin (nth-r)
                 (have! rg-ADDu-u (lambda ()
                          (fact 'ringoid-add-right-inv 'r 'u)
                          (detach! (list 'IMPLIES (list 'IN 'u '(CARR r)) rg-ADDu-u))
                          (ass)))
                 (subst rg-ADDu-u)
                 (fact 'ringoid-ideal-zero 'r)
                 (detach! (list 'IMPLIES '(IS-RINGOID r) (list 'IN (list 'ZERO 'r) (list 'IDL 'r))))
                 (ass))
          (for-each (lambda (k) (dk-focus! k) (vnb-guard (lambda () (ass))))
                    (dk-opened (lambda () (ci)))))))
  rg-refl-kids)

;;; ---- symmetry: a-b in I => -(a-b) = b-a in I ----
(rg-foc! rg-sym-leaf?)
(di)(di)(di)(di)                              ; u ; u in carr ; v ; v in carr
(di)                                          ; assume [u,v] in rel ; goal [v,u] in rel
(mac-h 'ringoid-rel-mem (list 'IN (list 'LIST 'u 'v) '(RINGOID-REL r)))
(ai (list 'AND
   (list 'IN (list 'LIST 'u 'v) (list 'CARTESIAN '(CARR r) '(CARR r)))
   (list 'IN rg-Xsym '(IDL r))))              ; -> u-v in idl in context
(fact 'ringoid-ideal-neg 'r rg-Xsym)          ; -(u-v) in idl
(fact 'ringoid-neg-diff 'r 'u 'v)             ; -(u-v) = v-u
(mac 'ringoid-rel-mem)                         ; goal [v,u]in rel -> AND(cart, v-u in idl)
(for-each (lambda (leaf) (dk-focus! leaf)
   (let ((g (rg-goal)))
     (if (and (pair? g) (eq? (car g) 'IN) (pair? (caddr g)) (eq? (car (caddr g)) 'CARTESIAN))
         (for-each (lambda (k) (dk-focus! k) (vnb-guard (lambda () (ass)))) (dk-opened (lambda () (ci))))
         (begin
           (subst (list '= (list (list 'ADD 'r) 'v (list (list 'NEG 'r) 'u))
                        (list (list 'NEG 'r) rg-Xsym)))
           (vnb-guard (lambda () (ass)))))))
  (dk-opened (lambda () (di))))

;;; ---- typing: RINGOID-REL(r) in POWER(cartesian(carr,carr)) ----
(rg-foc! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (pair? (caddr g)) (eq? (car (caddr g)) 'POWER))))
(define rel-sep '(SEP p (CARTESIAN (CARR r) (CARR r))
                      (IN ((ADD r) (NTH 1 p) ((NEG r) (NTH 2 p))) (IDL r))))
(mac 'RINGOID-REL)                            ; {SEP} in power(cart)
(mac 'power-set-membership)                   ; AND(SEP in SET, forall z. z in SEP => z in cart)
(di)
;; A: SEP in SET  (sep-set spawns cartesian in SET; cartesian-set-iff reduces to carr in SET)
(rg-foc! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET)
                          (pair? (cadr g)) (eq? (car (cadr g)) 'SEP))))
(sep-set)
(rg-foc! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET)
                          (pair? (cadr g)) (eq? (car (cadr g)) 'CARTESIAN))))
(mac 'cartesian-set-iff)
(vnb-guard (lambda () (di)))
(for-each (lambda (l) (dk-focus! l) (vnb-guard (lambda () (ass))))
          (filter (lambda (l) (let ((g (rg-gof l)))
                    (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) '(CARR r)) (eq? (caddr g) 'SET))))
                  (proof-leaves)))
;; B: forall z. z in SEP => z in cart  (sep-me on the actual assumption lands z in cart)
(rg-foc! rg-typingB-leaf?)
(di)(di)
(let ((asm (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'SEP))) (rg-asms))))
  (sep-me asm)
  (vnb-guard (lambda () (ass))))

;;; ---- transitivity: (a-b)+(b-c) = a-c in I ----
(rg-foc! (lambda (g) (and (pair? g) (eq? (car g) 'FORALL))))   ; only trans remains
(di)(di)(di)(di)(di)(di)                      ; u,u; v,v; w,w
(di)                                          ; assume ([u,v] in rel AND [v,w] in rel)
(ai (list 'AND (list 'IN '(LIST u v) '(RINGOID-REL r)) (list 'IN '(LIST v w) '(RINGOID-REL r))))
(mac-h 'ringoid-rel-mem (list 'IN '(LIST u v) '(RINGOID-REL r)))
(ai (list 'AND (list 'IN '(LIST u v) '(CARTESIAN (CARR r) (CARR r))) (list 'IN rg-Xuv '(IDL r))))
(mac-h 'ringoid-rel-mem (list 'IN '(LIST v w) '(RINGOID-REL r)))
(ai (list 'AND (list 'IN '(LIST v w) '(CARTESIAN (CARR r) (CARR r))) (list 'IN rg-Xvw '(IDL r))))
(fact 'ringoid-ideal-add 'r rg-Xuv rg-Xvw)    ; (u-v)+(v-w) in idl
(fact 'ringoid-diff-telescope 'r 'u 'v 'w)    ; (u-v)+(v-w) = u-w
(mac 'ringoid-rel-mem)                         ; goal [u,w]in rel -> AND(cart, u-w in idl)
(for-each (lambda (leaf) (dk-focus! leaf)
   (let ((g (rg-goal)))
     (if (and (pair? g) (eq? (car g) 'IN) (pair? (caddr g)) (eq? (car (caddr g)) 'CARTESIAN))
         (for-each (lambda (k) (dk-focus! k) (vnb-guard (lambda () (ass)))) (dk-opened (lambda () (ci))))
         (begin (subst (list '= rg-Xuw (list (list 'ADD 'r) rg-Xuv rg-Xvw)))
                (vnb-guard (lambda () (ass)))))))
  (dk-opened (lambda () (di))))

(qed 'ringoid-rel-is-equivalence)

;;; ================= ringoid-setoid-is-setoid =================
;;; RINGOID-SETOID(r) = [CARR(r), RINGOID-REL r] is a setoid.  The LIST-tuple instance
;;; pattern (like METRIC-TOP = [PTS, OPENS]): `slot' reduces the accessors, `len-r' the
;;; length, and the equivalence conjunct is the theorem above.
(sp (make-wff '(FORALL r (IMPLIES (IS-RINGOID r) (IS-SETOID (RINGOID-SETOID r))))))
(di)(di)
(fact 'ringoid-carr-in-set 'r)                ; carr(r) in set
(mac 'IS-SETOID)                              ; length=2 and pts in set and rel in set and is-equivalence
(slot 'pts)                                   ; pts(RINGOID-SETOID r) -> nth(1, RINGOID-SETOID r)
(slot 'rel)                                   ; rel(RINGOID-SETOID r) -> nth(2, RINGOID-SETOID r)
(mac 'RINGOID-SETOID)                         ; RINGOID-SETOID r -> [carr(r), RINGOID-REL r]
(nth-r)                                        ; nth(1,..)->carr(r) ; nth(2,..)->RINGOID-REL r
(rg-split-goal!)
;; length([carr, RINGOID-REL r]) = 2
(rg-foc! (lambda (g) (and (pair? g) (eq? (car g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))))
(len-r)
(rfl)
;; carr(r) in set
(rg-foc! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) '(CARR r)) (eq? (caddr g) 'SET))))
(ass)
;; RINGOID-REL r in set  (sep-set, cartesian-set-iff, carr in set)
(rg-foc! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'RINGOID-REL) (eq? (caddr g) 'SET))))
(mac 'RINGOID-REL)
(sep-set)
(rg-foc! (lambda (g) (and (pair? g) (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'CARTESIAN) (eq? (caddr g) 'SET))))
(mac 'cartesian-set-iff)
(vnb-guard (lambda () (di)))
(for-each (lambda (l) (dk-focus! l) (vnb-guard (lambda () (ass))))
          (filter (lambda (l) (let ((g (rg-gof l)))
                    (and (pair? g) (eq? (car g) 'IN) (equal? (cadr g) '(CARR r)) (eq? (caddr g) 'SET))))
                  (proof-leaves)))
;; is-equivalence(RINGOID-REL r, carr(r))  -- the theorem just proved
(rg-foc! (lambda (g) (and (pair? g) (eq? (car g) 'is-equivalence))))
(fact 'ringoid-rel-is-equivalence 'r)
(vnb-guard (lambda () (ass)))

(qed 'ringoid-setoid-is-setoid)
