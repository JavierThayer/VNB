;;; core-replay-checks.scm -- the suite checks of the CORE REPLAYER (core-replay.scm), loaded by
;;; test-suite.scm.  Design s.5 checks 1 (refusal half), 2, 4, 6 and 8, plus the Emacs API.  Every
;;; accepted case has its refused twin: a replayer that accepted everything, or refused everything,
;;; fails at least one of each pair.  The pages are the fixtures of test-core-pages/ (core-only
;;; scripts written by test-core-pages/make-fixtures.scm); the refused pages are those fixtures
;;; altered in memory here.

(define (crk--page name) (core-page-read name))
(define (crk--steps page) (cp-steps page))
(define (crk--with-steps page steps)          ; same header, these steps, renumbered 1..n
  (append (list 'core-page (cadr page))
          (filter (lambda (f) (not (and (pair? f) (eq? (car f) 'step)))) (cddr page))
          (let loop ((ss steps) (i 1))
            (if (null? ss) '()
                (cons (cons 'step (cons i (cddr (car ss)))) (loop (cdr ss) (+ i 1)))))))
(define (crk--without-renumber page steps)
  (append (list 'core-page (cadr page))
          (filter (lambda (f) (not (and (pair? f) (eq? (car f) 'step)))) (cddr page))
          steps))
(define (crk--replace-cmd step cmd)           ; (step K (at-node N) CMD . rest)
  (cons 'step (cons (cadr step) (cons (caddr step) (cons cmd (cddddr step))))))
(define (crk--replace-field step tag val)
  (map (lambda (f) (if (and (pair? f) (eq? (car f) tag)) val f)) step))
(define (crk--verdict-head v) (and (pair? v) (list (car v) (cadr v) (caddr v))))
(define (crk--reason-has? v s)
  (and (pair? v) (eq? (car v) 'refused) (string-search-forward s (cadddr v) 0) #t))

(define crk-fixtures
  '((core-fixture-and-comm 6) (core-fixture-mint 5) (core-fixture-ineq 3)
    (core-fixture-cite 5) (core-fixture-share 4) (core-fixture-arith 1)))

;;; ---- accepted: the six fixtures
(check "CORE-REPLAY accepted: the six fixture pages are core-replayed (di ai ass ew ta inst detach! ineq arith)"
  (lambda () (map (lambda (f) (core-replay-page (crk--page (car f)))) crk-fixtures))
  (map (lambda (f) (list 'core-replayed (cadr f))) crk-fixtures))

(check "CORE-REPLAY isolation: a replay leaves *ps*, the fresh counter and the theorem table as they were"
  (lambda ()
    (let ((ps0 *ps*) (c0 *fresh-counter*) (l0 *fresh-log*) (s0 *proof-script*))
      (core-replay-page (crk--page 'core-fixture-mint))
      (list (eq? *ps* ps0) (= *fresh-counter* c0) (eq? *fresh-log* l0) (eq? *proof-script* s0)
            (hash-table-ref/default *theorem-table* 'core-fixture-mint #f))))
  '(#t #t #t #t #f))

;;; ---- check 1, refusal half: an altered argument
(check "CORE-REPLAY refused (check 1): an altered ai argument is refused at step 3, the entry point declined"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-mint)) (ss (crk--steps p)))
      (crk--verdict-head
       (core-replay-page
        (crk--with-steps p (list (car ss) (cadr ss)
                                 (crk--replace-cmd (caddr ss) '(ai (forsome x (in x b))))
                                 (cadddr ss) (list-ref ss 4)))))))
  '(refused 3 ai))
(check-true "CORE-REPLAY refused (check 1): altered RECORDED hypotheses are refused at that step, `differs'"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-and-comm)) (ss (crk--steps p))
           (bad (crk--replace-field (list-ref ss 3) 'hyps
                                    '(hyps (sequent ((in p set) (in q set)) (in p set))
                                           (sequent ((in p set) (in q set)) (in q set)))))
           (v (core-replay-page (crk--with-steps p (append (list-head ss 3) (list bad) (list-tail ss 4))))))
      (and (equal? (crk--verdict-head v) '(refused 4 di)) (crk--reason-has? v "differs")))))
;;; one entry removed
(check "CORE-REPLAY refused (check 1): one ass removed (renumbered): the final check refuses, root not grounded"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-and-comm)) (ss (crk--steps p)))
      (crk--verdict-head (core-replay-page (crk--with-steps p (append (list-head ss 4) (list-tail ss 5)))))))
  '(refused 6 qed))
(check "CORE-REPLAY refused (check 1): one entry removed (not renumbered): refused at the gap"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-and-comm)) (ss (crk--steps p)))
      (crk--verdict-head (core-replay-page (crk--without-renumber p (append (list-head ss 2) (list-tail ss 3)))))))
  '(refused 3 di))
;;; a non-core form inserted
(check "CORE-REPLAY refused (check 1): a non-core `prop' step inserted is refused at its step"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-and-comm)) (ss (crk--steps p)))
      (crk--verdict-head
       (core-replay-page (crk--with-steps p (append (list-head ss 2)
                                                    (list (crk--replace-cmd (list-ref ss 2) '(prop)))
                                                    (list-tail ss 2)))))))
  '(refused 3 prop))
(check "CORE-REPLAY refused (check 1): a non-core `fact' in place of ta + inst is refused at its step"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-cite)) (ss (crk--steps p)))
      (crk--verdict-head
       (core-replay-page (crk--with-steps p (cons (car ss) (cons (crk--replace-cmd (cadr ss) '(fact nn-in-rr k))
                                                                 (cddr ss))))))))
  '(refused 2 fact))
(define crk-eval-ran #f)
(check "CORE-REPLAY refused (check 1): a Scheme form as a command is refused and NOT evaluated (no eval)"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-arith)) (ss (crk--steps p))
           (v (core-replay-page
               (crk--with-steps p (list (crk--replace-cmd (car ss) '(set! crk-eval-ran #t)))))))
      (list (crk--verdict-head v) crk-eval-ran)))
  '((refused 1 set!) #f))
(check "CORE-REPLAY refused: a page written under another kernel is refused at step 0"
  (lambda ()
    (let ((p (crk--page 'core-fixture-arith)))
      (car (core-replay-page (map (lambda (f) (if (and (pair? f) (eq? (car f) 'kernel-hash))
                                                  '(kernel-hash "0000-not-this-kernel") f))
                                  p)))))
  'refused)

;;; ---- check 2: mints
(define crk-c0 *fresh-counter*)
(define crk-map-a #f)
(check "CORE-REPLAY mints (check 2): core-replayed after the fresh counter is advanced by 1000; v1 maps to a NEW name"
  (lambda ()
    (let* ((base (begin (core-replay-page (crk--page 'core-fixture-mint)) *core-replay-last-map*))
           (v (fluid-let ((*fresh-counter* (+ crk-c0 1000))) (core-replay-page (crk--page 'core-fixture-mint)))))
      (set! crk-map-a *core-replay-last-map*)
      (list v (= 1 (length crk-map-a)) (eq? (cdar base) (cdar crk-map-a)))))
  '((core-replayed 5) #t #f))
(check-true "CORE-REPLAY mints (check 2): refused when the map is forced non-injective (a seeded name denotes v1's image)"
  (lambda ()
    (let ((v (fluid-let ((*fresh-counter* (+ crk-c0 1000))
                         (*core-replay-seed-map* (list (cons 'vseed (cdar crk-map-a)))))
               (core-replay-page (crk--page 'core-fixture-mint)))))
      (and (equal? (crk--verdict-head v) '(refused 3 ai)) (crk--reason-has? v "not a bijection")))))
(check-true "CORE-REPLAY mints: a page that uses a mint before the step that mints it is refused"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-mint)) (ss (crk--steps p))
           (v (core-replay-page
               (crk--with-steps p (list (car ss) (cadr ss) (crk--replace-cmd (caddr ss) '(cut (in v1 a))))))))
      (crk--reason-has? v "not yet learned"))))

;;; ---- check 4: sharing (the two conjuncts of core-fixture-share are ONE node)
(check "CORE-REPLAY sharing (check 4): a step at a node already justified by a matching inference is accepted WITHOUT running"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-share)) (ss (crk--steps p))
           (v (core-replay-page (crk--with-steps p (append (list-head ss 3) (list (list-ref ss 2)) (list-tail ss 3))))))
      (list v *core-replay-last-stats*)))
  '((core-replayed 5) (4 1 0)))
(check "CORE-REPLAY sharing (check 4): the same duplicate with a sequent that is no replay node is refused"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-share)) (ss (crk--steps p))
           (dup (crk--replace-field (crk--replace-field (list-ref ss 2) 'at-node '(at-node 9))
                                    'sequent '(sequent () (implies (in a set) (in a nn))))))
      (crk--verdict-head (core-replay-page (crk--with-steps p (append (list-head ss 3) (list dup) (list-tail ss 3)))))))
  '(refused 4 di))

;;; ---- check 6: ineq premises are FORMULAS, resolved at replay
(check "CORE-REPLAY ineq (check 6): replays with the context and the premises permuted"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-ineq)) (ss (crk--steps p)) (s3 (caddr ss))
           (seq (cps-sequent s3))
           (s3b (crk--replace-field (crk--replace-cmd s3 (cons 'ineq (reverse (cdr (cps-cmd s3)))))
                                    'sequent (list 'sequent (reverse (car seq)) (cadr seq)))))
      (core-replay-page (crk--with-steps p (list (car ss) (cadr ss) s3b)))))
  '(core-replayed 3))
(check-true "CORE-REPLAY ineq (check 6): a premise that is not in the node's context is refused at the ineq step"
  (lambda ()
    (let* ((p (crk--page 'core-fixture-ineq)) (ss (crk--steps p))
           (v (core-replay-page
               (crk--with-steps p (list (car ss) (cadr ss) (crk--replace-cmd (caddr ss) '(ineq (<= x 2) (in x rr))))))))
      (and (equal? (crk--verdict-head v) '(refused 3 ineq)) (crk--reason-has? v "not in the node's context")))))

;;; ---- check 8: coverage of the kernel map
(check "CORE-REPLAY coverage (check 8): every kernel-map entry point has a dispatch row or is refused-unexercised; 56 core names"
  (lambda () (list (core-replay-coverage-missing) (length (core-names)) (length (core-replay-kernel-entry-points))))
  '(() 56 57))
(check "CORE-REPLAY coverage (check 8, control): without the `mac' row and with pi-spec! off the refused list, the gate names them"
  (lambda ()
    (core-replay-coverage-missing (filter (lambda (r) (not (eq? (car r) 'mac))) *core-dispatch*)
                                  '(pi-truth! pi-contraposit!)))
  '(<macete:cartesian-decompose> <macete:tuple-equality-decompose> pi-spec!))

;;; ---- the Emacs API
(check "CORE-REPLAY api: core-page-text prints one line per step and the verdict line; an absent page says so"
  (lambda ()
    (let ((t1 (core-page-text 'core-fixture-mint)))
      (list (string-search-forward "step 4: (ew v1)" t1 0)
            (string-search-forward "verdict: core-replayed 5" t1 0)
            (core-page-text 'core-fixture-no-such-page))))
  (let ((t1 (core-page-text 'core-fixture-mint)))
    (list (string-search-forward "step 4: (ew v1)" t1 0)
          (- (string-length t1) (string-length "verdict: core-replayed 5"))
          "no core page for core-fixture-no-such-page")))
(check "CORE-REPLAY api: the refusal verdict line"
  (lambda () (core-replay-verdict-string '(refused 3 prop "not a core command: prop")))
  "verdict: refused at step 3 (prop): not a core command: prop")
(check "CORE-REPLAY api: begin / next / back on the workspace; forward to done, the proof grounded; back restores"
  (lambda ()
    (fluid-let ((*ps* #f) (*proof-script* '()) (*live-trace* '()) (*vnb-undo-stack* '())
                (*core-replay-session* #f) (*current-goal* #f) (*proof-mints* '()))
      (let ((out '()))
        (with-output-to-string
          (lambda ()
            (let* ((n  (core-replay-begin 'core-fixture-and-comm))
                   (s1 (core-replay-next)) (s2 (core-replay-next))
                   (b1 (core-replay-back))
                   (leaves-after-back (length (proof-open-leaves *ps*)))
                   (rest (let loop ((acc '())) (let ((r (core-replay-next))) (if (eq? r 'done) (reverse (cons r acc)) (loop (cons r acc)))))))
              (set! out (list n s1 s2 b1 leaves-after-back rest (proof-done? *ps*) *proof-script*)))))
        out)))
  '(6 1 2 1 1 (2 3 4 5 6 done) #t ()))
(check "CORE-REPLAY api (control): next on a page step that the workspace state refuses leaves the graph as it was"
  (lambda ()
    (fluid-let ((*ps* #f) (*proof-script* '()) (*live-trace* '()) (*vnb-undo-stack* '())
                (*core-replay-session* #f) (*current-goal* #f) (*proof-mints* '()))
      (let ((out #f))
        (with-output-to-string
          (lambda ()
            (core-replay-begin 'core-fixture-and-comm)
            (core-replay-next)
            ;; corrupt step 2 in the session: an ai on a formula that is not in context
            (vector-set! (vector-ref *core-replay-session* 2) 1
                         (crk--replace-cmd (vector-ref (vector-ref *core-replay-session* 2) 1) '(ai (and (in q set) (in q set)))))
            (let* ((n0 (length (dg-sequent-nodes (proof-state-dg *ps*))))
                   (r (core-replay-next)))
              (set! out (list (car r) (cadr r) (= n0 (length (dg-sequent-nodes (proof-state-dg *ps*))))
                              (vector-ref *core-replay-session* 4))))))
        out)))
  '(refused 2 #t 1))
