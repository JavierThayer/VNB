;;; singleton-membership.scm -- lemmas MOVED 2026-10-27 (integration of the 10-26/27 wave) out of
;;; theorem-library/field-ring-view.scm, so that files of library core may cite them (the library gate).
;;; The proofs are the originals, verbatim; the helper defines are a copy of field-ring-view.scm's.  Loaded
;;; immediately before field-ring-view.scm.
;;;   singleton-membership singleton-unfold

;;; ---- helper defines copied from field-ring-view.scm ----


;;; ---- the moved proofs ----
(sp (make-wff '(FORALL y_ (== (SINGLETON y_) (MAKE-SET (LIST y_))))))
(di) (mac 'SINGLETON) (qrfl) (qed 'singleton-unfold)

(sp (make-wff '(FORALL y_ (FORALL x_ (IFF (IN x_ (SINGLETON y_))
                                          (AND (IN x_ SET) (= x_ y_)))))))
(di)
;; RM1 2026-10-09: the macetes now owe definedness of the matched term, and
;; [y_] is certified only where something makes y_ a set or the term occurs in
;; an IN hypothesis.  So the IFF is split FIRST and each side unfolded where its
;; certificate lives: forward, inside the hypothesis x_ in make-set([y_]);
;; backward, after y_ in SET is landed from x_ in SET and x_ = y_.
(define sm-br (dk-opened (lambda () (di))))

;; ---- FORWARD: membership gives x = y
(dk-focus! (car sm-br))
(mac-h 'singleton-unfold '(IN x_ (SINGLETON y_)))
(mac-h 'make-set-membership '(IN x_ (MAKE-SET (LIST y_))))
(dk-split! (car (dk-asms)))
(let* ((ex (any-pred (dk-head? 'FORSOME) (dk-asms))))
  (dk-split! (dk-landed-1 (lambda () (ai ex)))))
(let ((le (any-pred (lambda (a) (and (pair? a) (eq? (car a) '<=)
                                     (equal? (caddr a) '(LENGTH (LIST y_)))))
                    (dk-asms))))
  (dk-have! '(= (LENGTH (LIST y_)) 1) (lambda () (len-r) (rfl)))
  (dk-rewrite-h! le '(LENGTH (LIST y_)) 1))
(display "fwd asms: ") (write (map expression->string (dk-asms))) (newline)
(let* ((eqn (any-pred (lambda (a) (and (pair? a) (eq? (car a) '=)
                                       (pair? (cadr a)) (eq? (car (cadr a)) 'NTH)))
                      (dk-asms)))
       (i   (cadr (cadr eqn))))
  (display "index var: ") (write i) (newline)
  ;; nn-le-antisym's antecedents are CURRIED (a <= b implies b <= a implies ...)
  ;; and it is guarded on both being in NN, so `fact' detaches all four from
  ;; context once 1 in nn is there -- no AND to build.
  (fact 'nn-one-in)
  (fact 'nn-le-antisym i 1)
  (dk-have! (list '= (list 'NTH i (list 'LIST 'y_)) 'y_)
    (lambda () (subst (list '= i 1)) (nth-r) (rfl)))
  (fact 'eq-sym (list 'NTH i '(LIST y_)) 'x_)
  (fact 'eq-trans 'x_ (list 'NTH i '(LIST y_)) 'y_))
(for-each (lambda (n) (dk-focus! n) (ass))
          (dk-opened (lambda () (di))))
;; ---- BACKWARD: x = y gives membership, witnessed by index 1
(dk-focus! (cadr sm-br))
(dk-split! (car (dk-asms)))
(dk-have! '(IN y_ SET) (lambda () (subst '(= y_ x_)) (ass)))
(mac 'singleton-unfold) (mac 'make-set-membership) (len-r)
(fact 'nn-one-in) (fact 'nn-le-refl 1)
(fact 'eq-sym 'x_ 'y_)
(for-each
 (lambda (n)
   (dk-focus! n)
   (let ((g (dk-goal)))
     (if (and (pair? g) (eq? (car g) 'FORSOME))
         (begin (ew 1)
                (nth-r)
                (display (expression->string (dk-goal))) (newline)
                (from-context!))
         (ass))))
 (dk-opened (lambda () (di))))
(display "TOTAL leaves: ") (write (length (proof-leaves))) (newline)
(for-each (lambda (n) (display "  leaf: ")
            (display (expression->string (wff-formula (sequent-node-assertion n)))) (newline))
          (proof-leaves))

(qed 'singleton-membership)

