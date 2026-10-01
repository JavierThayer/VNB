;;; rule-checkers-schema.scm -- checkers for the thirteen `schema' kernel operations
;;;
;;; THE POINT.  `dg-apply-rule!' records the name of an operation and the
;;; hypothesis sequents it is handed; until 2026-09-20 it checked nothing, so a
;;; caller that built the wrong hypotheses recorded a valid-looking inference.
;;; A CHECKER verifies a finished inference: given the rule tag, the hypothesis
;;; sequents and the conclusion sequent, it decides whether the hypotheses are
;;; the ones the named operation prescribes.  It returns #t to accept, or a
;;; STRING giving the reason to refuse.
;;;
;;; INDEPENDENCE.  A checker states the rule as a RELATION between the
;;; conclusion and the hypotheses and tests the relation.  Nothing here calls a
;;; `pi-*!' procedure or reuses its code -- not even `reduce-lambda-in-expr',
;;; which is the beta rules' builder: the contraction used below (`rcs--dev')
;;; is written again, in this file, from the definition of beta reduction.  Only
;;; the expression layer is used: `alpha-equiv?', `free-vars', `subst-free',
;;; `subst-free*', and the sequent accessors.
;;;
;;; The context helpers (`chk-asms', `chk-goal', `chk-mem?', `chk-subset?',
;;; `chk-set=?', `chk-minus', `chk-every') are the shared ones at the head of
;;; rule-checkers-logic.scm, so THIS FILE MUST LOAD AFTER THAT ONE.
;;;
;;; ASSUMPTION LISTS ARE COMPARED AS SETS, up to alpha-equivalence.  The order
;;; of a context is presentation, not meaning: `context-add-assumption' conses
;;; on the front and skips a formula the context already holds, so the order and
;;; the multiplicity of a context are artefacts of the path taken to it.  Every
;;; comparison below therefore goes through `chk-set=?'.
;;;
;;; WHAT IS NOT RE-CHECKED (policy, recorded here so it is visible):
;;;   * the beta rules' OBLIGATION policy.  A redex whose licence -- the
;;;     argument's membership in the lambda's domain -- is not evident fires
;;;     anyway and owes `(IN u A)' as an extra hypothesis.  The checker demands
;;;     that every contracted redex be EITHER licensed by the context and the
;;;     binders it sits under OR accompanied by that obligation; it does not
;;;     demand that the kernel's choice between the two match its own.
;;;     REDEXES ARE CONTRACTED INNERMOST FIRST, and a redex's licence is judged
;;;     on its argument IN THE FORM IT HAS AFTER the redexes inside it have
;;;     been contracted -- see the beta section below.
;;;   * `iota-in-elim' IS checked for its premise (the context must establish
;;;     that the description denotes), but only by the two evident shapes -- an
;;;     assumption `(IN t X)' or an equation naming t.  The structure-accessor
;;;     path of `asm-establishes-defined?' cannot apply to an IOTA term (it
;;;     wants a one-argument application), so nothing is lost.
;;;
;;; The thirteen operations, each with the relation enforced:
;;;
;;;   sep-sethood          G => SEP(x,A,p) in SET        <=  G => A in SET
;;;   sep-mem-intro        G => y in SEP(x,A,p)          <=  G => y in A ; G => p[x:=y]
;;;   sep-mem-elim         y in SEP(x,A,p) consumed; context gains y in A, p[x:=y]
;;;   comp-mem-intro       G => y in COMP(x,p)           <=  G => y in SET ; G => p[x:=y]
;;;   comp-mem-elim        y in COMP(x,p) consumed; context gains y in SET, p[x:=y]
;;;   big-union-sethood    G => BIG-UNION(z,A,b) in SET  <=  G => A in SET ;
;;;                                                          G => forall v in A. b[z:=v] in SET
;;;   big-union-mem-intro  G => x in BIG-UNION(z,A,b)    <=  G => w in A ; G => x in b[z:=w]
;;;   big-union-mem-elim   x in BIG-UNION(z,A,b) consumed; context gains e in A and
;;;                        x in b[z:=e] for an eigenvariable e fresh for everything else
;;;   iota-def             G => C  <=  G => exists-unique x. p ; G, p[x:=IOTA(x,p)] => C
;;;   iota-in-elim         G => C  <=  G, p[x:=IOTA(x,p)] => C, the context establishing
;;;                        that IOTA(x,p) denotes
;;;   lambda-type          G => VNB-LAMBDA(bs,A,b) in FUN(A,B)  <=  G => the pointwise
;;;                        typing ; G => A in SET, the lambda's declared domain being
;;;                        the FUN's domain
;;;   lambda-beta          G => C  <=  G => C', C' obtained from C by contracting
;;;                        redexes innermost first, each contracted redex's
;;;                        argument (after its own inner contractions) licensed
;;;                        by the context or owed as `(IN u A)' (+ obligations)
;;;   lambda-beta-hyp      the same contraction on one cited assumption (+ obligations)
;;;
;;; Written for batch 10 (10-B).  `else' is deliberately not used in any `cond'
;;; below: it is shadowed in the per-file load environment.

;;; -----------------------------------------------------------------------
;;; Sequent access and set comparison of contexts
;;;
;;; A checker is handed hypothesis SEQUENTS and a conclusion that may be a
;;; sequent or the sequent NODE the inference goes into; both are accepted.
;;; Formulas are compared raw, as `alpha-equiv?' requires.

(define (rcs--sequent-of s)
  (cond ((sequent? s) s)
        ((sequent-node? s) (sequent-node-sequent s))
        (#t (error "rule-checkers-schema: not a sequent" s))))

(define (rcs--asms s) (chk-asms (rcs--sequent-of s)))
(define (rcs--goal s) (chk-goal (rcs--sequent-of s)))

;;; The context with every alpha-copy of F removed (what
;;; `context-remove-assumption' does).
(define (rcs--drop f fs) (chk-minus fs (list f)))

(define (rcs--same-asms? s1 s2) (chk-set=? (rcs--asms s1) (rcs--asms s2)))

;;; Is V free in none of EXPRS?
(define (rcs--fresh-for? v exprs)
  (chk-every (lambda (e) (not (memq v (free-vars e)))) exprs))

;;; Shape tests for the three binder-carrying class terms.
(define (rcs--sep?  t) (and (pair? t) (eq? (car t) 'SEP)       (= (length t) 4) (symbol? (cadr t))))
(define (rcs--comp? t) (and (pair? t) (eq? (car t) 'COMP)      (= (length t) 3) (symbol? (cadr t))))
(define (rcs--bu?   t) (and (pair? t) (eq? (car t) 'BIG-UNION) (= (length t) 4) (symbol? (cadr t))))
(define (rcs--in?   f) (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)))

;;; -----------------------------------------------------------------------
;;; SEPARATION  SEP(x, A, p) = { x in A | p }

;;; sep-sethood:  Gamma => SEP(x,A,p) in SET   from   Gamma => A in SET.
(define (rcs-sep-sethood rule hyps concl)
  (let ((g (rcs--goal concl)))
    (cond
      ((not (= (length hyps) 1)) "sep-sethood: expects exactly one hypothesis")
      ((not (and (rcs--in? g) (eq? (caddr g) 'SET) (rcs--sep? (cadr g))))
       "sep-sethood: the conclusion is not (IN (SEP x A p) SET)")
      ((not (rcs--same-asms? (car hyps) concl))
       "sep-sethood: the hypothesis does not keep the conclusion's assumptions")
      ((not (alpha-equiv? (rcs--goal (car hyps)) (list 'IN (caddr (cadr g)) 'SET)))
       "sep-sethood: the hypothesis is not (IN A SET) for the separation's own domain A")
      (#t #t))))

;;; The two membership-INTRODUCTION rules differ only in the first subgoal, so
;;; they share one relation: goal (IN y C), C a binder term; first hypothesis
;;; the DOMAIN obligation, second the BODY at y.
(define (rcs--mem-intro-check tag hyps concl shape? domain-goal body-at)
  (let ((g (rcs--goal concl)))
    (cond
      ((not (= (length hyps) 2))
       (string-append tag ": expects exactly two hypotheses"))
      ((not (and (rcs--in? g) (shape? (caddr g))))
       (string-append tag ": the conclusion is not a membership in a term of that form"))
      ((not (and (rcs--same-asms? (car hyps) concl) (rcs--same-asms? (cadr hyps) concl)))
       (string-append tag ": a hypothesis does not keep the conclusion's assumptions"))
      ((not (alpha-equiv? (rcs--goal (car hyps)) (domain-goal (cadr g) (caddr g))))
       (string-append tag ": the first hypothesis is not the domain membership"))
      ((not (alpha-equiv? (rcs--goal (cadr hyps)) (body-at (cadr g) (caddr g))))
       (string-append tag ": the second hypothesis is not the body at the member"))
      (#t #t))))

;;; The two membership-ELIMINATION rules likewise: one hypothesis, same goal,
;;; the cited membership consumed and two formulas gained.
(define (rcs--mem-elim-check tag hyps concl shape? gains)
  (cond
    ((not (= (length hyps) 1)) (string-append tag ": expects exactly one hypothesis"))
    ((not (alpha-equiv? (rcs--goal (car hyps)) (rcs--goal concl)))
     (string-append tag ": the hypothesis changes the goal"))
    (#t
     (let ((gamma  (rcs--asms concl))
           (gamma* (rcs--asms (car hyps))))
       (let loop ((fs gamma))
         (cond
           ((null? fs)
            (string-append tag ": no assumption of the eliminated form yields the hypothesis' context"))
           ((let ((f (car fs)))
              (and (rcs--in? f) (shape? (caddr f))
                   (chk-set=? gamma*
                               (append (gains (cadr f) (caddr f))
                                       (rcs--drop f gamma)))))
            #t)
           (#t (loop (cdr fs)))))))))

;;; sep-mem-intro: y in SEP(x,A,p)  from  y in A  and  p[x:=y].
(define (rcs-sep-mem-intro rule hyps concl)
  (rcs--mem-intro-check "sep-mem-intro" hyps concl rcs--sep?
    (lambda (y subj) (list 'IN y (caddr subj)))
    (lambda (y subj) (subst-free (cadr subj) y (cadddr subj)))))

;;; sep-mem-elim: the assumption y in SEP(x,A,p) is consumed and the context
;;; gains y in A and p[x:=y].
(define (rcs-sep-mem-elim rule hyps concl)
  (rcs--mem-elim-check "sep-mem-elim" hyps concl rcs--sep?
    (lambda (y subj)
      (list (list 'IN y (caddr subj))
            (subst-free (cadr subj) y (cadddr subj))))))

;;; -----------------------------------------------------------------------
;;; COMPREHENSION  COMP(x, p) = { x | p }.  Members of a class are sets, so the
;;; domain obligation is sethood.

(define (rcs-comp-mem-intro rule hyps concl)
  (rcs--mem-intro-check "comp-mem-intro" hyps concl rcs--comp?
    (lambda (y subj) (list 'IN y 'SET))
    (lambda (y subj) (subst-free (cadr subj) y (caddr subj)))))

(define (rcs-comp-mem-elim rule hyps concl)
  (rcs--mem-elim-check "comp-mem-elim" hyps concl rcs--comp?
    (lambda (y subj)
      (list (list 'IN y 'SET)
            (subst-free (cadr subj) y (caddr subj))))))

;;; -----------------------------------------------------------------------
;;; BIG-UNION  BIG-UNION(z, A, b) = union over z in A of b

;;; big-union-sethood: A is a set and every member of the family is a set.
;;; The second hypothesis is read back as a guarded universal over a variable v
;;; that must not be captured by A: its body is b with z renamed to v.
(define (rcs-big-union-sethood rule hyps concl)
  (let ((g (rcs--goal concl)))
    (cond
      ((not (= (length hyps) 2)) "big-union-sethood: expects exactly two hypotheses")
      ((not (and (rcs--in? g) (eq? (caddr g) 'SET) (rcs--bu? (cadr g))))
       "big-union-sethood: the conclusion is not (IN (BIG-UNION z A body) SET)")
      ((not (and (rcs--same-asms? (car hyps) concl) (rcs--same-asms? (cadr hyps) concl)))
       "big-union-sethood: a hypothesis does not keep the conclusion's assumptions")
      (#t
       (let* ((subj (cadr g))
              (z    (cadr subj))
              (A    (caddr subj))
              (body (cadddr subj))
              (h2   (rcs--goal (cadr hyps))))
         (cond
           ((not (alpha-equiv? (rcs--goal (car hyps)) (list 'IN A 'SET)))
            "big-union-sethood: the first hypothesis is not (IN A SET)")
           ((not (and (pair? h2) (eq? (car h2) 'FORALL) (= (length h2) 3)
                      (symbol? (cadr h2))
                      (let ((imp (caddr h2)))
                        (and (pair? imp) (eq? (car imp) 'IMPLIES) (= (length imp) 3)
                             (rcs--in? (cadr imp)) (eq? (cadr (cadr imp)) (cadr h2))
                             (rcs--in? (caddr imp)) (eq? (caddr (caddr imp)) 'SET)))))
            "big-union-sethood: the second hypothesis is not  forall v. v in _ => _ in SET")
           (#t
            (let* ((v   (cadr h2))
                   (imp (caddr h2))
                   (dom (caddr (cadr imp)))
                   (bod (cadr (caddr imp))))
              (cond
                ((not (alpha-equiv? dom A))
                 "big-union-sethood: the universal is not guarded by the union's own domain A")
                ((not (or (eq? v z) (rcs--fresh-for? v (list A))))
                 "big-union-sethood: the universal's variable is captured by the domain A")
                ;; 2026-09-24 (gap 2): v must not be free in the family's body
                ;; either.  With v free in b and v /= z, the universal binds that
                ;; v too, so the hypothesis speaks of a different family.  The
                ;; old test accepted  BIG-UNION(z, NN, v) in SET  from  NN in SET
                ;; and  forall v. v in NN => v in SET  (both provable); v is free
                ;; nowhere else, so it generalises, and at v := SET the union over
                ;; the nonempty NN of the constant family SET is SET: SET in SET.
                ((not (or (eq? v z) (rcs--fresh-for? v (list body))))
                 "big-union-sethood: the universal's variable is free in the family's body, which it would capture")
                ((not (alpha-equiv? bod (subst-free z v body)))
                 "big-union-sethood: the universal's body is not the family's body at v")
                (#t #t))))))))))

;;; big-union-mem-intro: the witness is read off the first hypothesis, which is
;;; its membership in A; the second places x in the family's body at it.
(define (rcs-big-union-mem-intro rule hyps concl)
  (let ((g (rcs--goal concl)))
    (cond
      ((not (= (length hyps) 2)) "big-union-mem-intro: expects exactly two hypotheses")
      ((not (and (rcs--in? g) (rcs--bu? (caddr g))))
       "big-union-mem-intro: the conclusion is not (IN x (BIG-UNION z A body))")
      ((not (and (rcs--same-asms? (car hyps) concl) (rcs--same-asms? (cadr hyps) concl)))
       "big-union-mem-intro: a hypothesis does not keep the conclusion's assumptions")
      (#t
       (let* ((x    (cadr g))
              (subj (caddr g))
              (z    (cadr subj))
              (A    (caddr subj))
              (body (cadddr subj))
              (h1   (rcs--goal (car hyps))))
         (cond
           ((not (and (rcs--in? h1) (alpha-equiv? (caddr h1) A)))
            "big-union-mem-intro: the first hypothesis is not a membership in the union's domain A")
           ((not (alpha-equiv? (rcs--goal (cadr hyps))
                               (list 'IN x (subst-free z (cadr h1) body))))
            "big-union-mem-intro: the second hypothesis is not (IN x body[z := witness])")
           (#t #t)))))))

;;; big-union-mem-elim: the membership is consumed and the context gains
;;; e in A and x in body[z:=e] for an EIGENVARIABLE e, which must be free in
;;; nothing else -- not in the surviving context, the goal, A, body or x.
(define (rcs-big-union-mem-elim rule hyps concl)
  (cond
    ((not (= (length hyps) 1)) "big-union-mem-elim: expects exactly one hypothesis")
    ((not (alpha-equiv? (rcs--goal (car hyps)) (rcs--goal concl)))
     "big-union-mem-elim: the hypothesis changes the goal")
    (#t
     (let* ((goal   (rcs--goal concl))
            (gamma  (rcs--asms concl))
            (gamma* (rcs--asms (car hyps))))
       (let loop ((fs gamma) (why "big-union-mem-elim: no assumption of the eliminated form yields the hypothesis' context"))
         (cond
           ((null? fs) why)
           ((not (and (rcs--in? (car fs)) (rcs--bu? (caddr (car fs)))))
            (loop (cdr fs) why))
           (#t
            (let* ((f    (car fs))
                   (x    (cadr f))
                   (subj (caddr f))
                   (z    (cadr subj))
                   (A    (caddr subj))
                   (body (cadddr subj))
                   (rest (rcs--drop f gamma)))
              ;; the eigenvariable is whatever the new membership in A names
              (let try ((cands gamma*) (bad #f))
                (cond
                  ((null? cands)
                   (loop (cdr fs) (or bad why)))
                  ((not (and (rcs--in? (car cands)) (symbol? (cadr (car cands)))
                             (alpha-equiv? (caddr (car cands)) A)
                             (chk-set=? gamma*
                                         (cons (car cands)
                                               (cons (list 'IN x (subst-free z (cadr (car cands)) body))
                                                     rest)))))
                   (try (cdr cands) bad))
                  ((not (rcs--fresh-for? (cadr (car cands))
                                         (cons goal (cons A (cons body (cons x rest))))))
                   (try (cdr cands)
                        "big-union-mem-elim: the eigenvariable is not fresh -- it occurs free in the context, the goal, or the family"))
                  (#t #t)))))))))))

;;; -----------------------------------------------------------------------
;;; IOTA  (IOTA x p) = the unique x such that p

;;; iota-def: the existence-and-uniqueness obligation, and the main branch with
;;; the defining property granted.  The description is recovered from the first
;;; hypothesis, which is written out as
;;;     FORSOME x. p AND (FORALL y. p[x:=y] => x = y)
;;; with y fresh for p.
(define (rcs-iota-def rule hyps concl)
  (cond
    ((not (= (length hyps) 2)) "iota-def: expects exactly two hypotheses")
    ((not (rcs--same-asms? (car hyps) concl))
     "iota-def: the existence obligation does not keep the conclusion's assumptions")
    ((not (alpha-equiv? (rcs--goal (cadr hyps)) (rcs--goal concl)))
     "iota-def: the main branch changes the goal")
    (#t
     (let ((ex (rcs--goal (car hyps))))
       (cond
         ((not (and (pair? ex) (eq? (car ex) 'FORSOME) (= (length ex) 3) (symbol? (cadr ex))
                    (let ((c (caddr ex))) (and (pair? c) (eq? (car c) 'AND) (= (length c) 3)))))
          "iota-def: the first hypothesis is not an existence obligation FORSOME x. p AND uniqueness")
         (#t
          (let* ((x    (cadr ex))
                 (conj (caddr ex))
                 (p    (cadr conj))
                 (uniq (caddr conj)))
            (cond
              ((not (and (pair? uniq) (eq? (car uniq) 'FORALL) (= (length uniq) 3)
                         (symbol? (cadr uniq))
                         (let ((imp (caddr uniq)))
                           (and (pair? imp) (eq? (car imp) 'IMPLIES) (= (length imp) 3)))))
               "iota-def: the second conjunct is not a universal implication")
              (#t
               (let* ((y   (cadr uniq))
                      (imp (caddr uniq)))
                 (cond
                   ((eq? y x) "iota-def: the uniqueness variable is the description's own variable")
                   ((not (rcs--fresh-for? y (list p)))
                    "iota-def: the uniqueness variable is free in the property p")
                   ((not (alpha-equiv? (cadr imp) (subst-free x y p)))
                    "iota-def: the uniqueness antecedent is not p at the second witness")
                   ((not (alpha-equiv? (caddr imp) (list '= x y)))
                    "iota-def: the uniqueness consequent is not the equation x = y")
                   ((not (chk-set=? (rcs--asms (cadr hyps))
                                     (cons (subst-free x (list 'IOTA x p) p) (rcs--asms concl))))
                    "iota-def: the main branch does not gain exactly the defining property p[x := IOTA(x,p)]")
                   (#t #t))))))))))))

;;; Does the context establish that T denotes?  A true atomic formula is strict,
;;; so an assumption (IN t X) or an equation naming t says that t denotes.
(define (rcs--context-defines? gamma t)
  (let loop ((fs gamma))
    (and (pair? fs)
         (or (let ((f (car fs)))
               (and (pair? f)
                    (or (and (eq? (car f) 'IN) (= (length f) 3) (alpha-equiv? (cadr f) t))
                        (and (eq? (car f) '=) (= (length f) 3)
                             (or (alpha-equiv? (cadr f) t) (alpha-equiv? (caddr f) t))))))
             (loop (cdr fs))))))

;;; Every IOTA subterm of E, outermost first.
(define (rcs--iota-subterms e)
  (let walk ((e e) (acc '()))
    (cond ((not (pair? e)) acc)
          ((and (eq? (car e) 'IOTA) (= (length e) 3) (symbol? (cadr e)))
           (walk (caddr e) (cons e acc)))
          (#t (let loop ((xs e) (acc acc))
                (if (null? xs) acc (loop (cdr xs) (walk (car xs) acc))))))))

;;; iota-in-elim: the context already says the description denotes, so the
;;; defining property is granted.  One hypothesis, same goal, exactly the
;;; property added.
(define (rcs-iota-in-elim rule hyps concl)
  (cond
    ((not (= (length hyps) 1)) "iota-in-elim: expects exactly one hypothesis")
    ((not (alpha-equiv? (rcs--goal (car hyps)) (rcs--goal concl)))
     "iota-in-elim: the hypothesis changes the goal")
    (#t
     (let* ((gamma  (rcs--asms concl))
            (gamma* (rcs--asms (car hyps)))
            (added  (let loop ((fs gamma*) (acc '()))
                      (cond ((null? fs) (reverse acc))
                            ((chk-mem? (car fs) gamma) (loop (cdr fs) acc))
                            (#t (loop (cdr fs) (cons (car fs) acc)))))))
       (cond
         ((not (chk-subset? gamma gamma*))
          "iota-in-elim: the hypothesis drops an assumption")
         ((null? added)
          ;; the property was already in the context: the sequent is unchanged
          #t)
         ((not (= (length added) 1))
          "iota-in-elim: the hypothesis adds more than the defining property")
         (#t
          (let ((d (car added)))
            (let loop ((ts (rcs--iota-subterms d)) (why "iota-in-elim: the added assumption is not p[x := IOTA(x,p)] for any description in it"))
              (cond
                ((null? ts) why)
                ((not (alpha-equiv? d (subst-free (cadr (car ts)) (car ts) (caddr (car ts)))))
                 (loop (cdr ts) why))
                ((not (rcs--context-defines? gamma (car ts)))
                 (loop (cdr ts)
                       "iota-in-elim: nothing in the context establishes that the description denotes"))
                (#t #t))))))))))

;;; -----------------------------------------------------------------------
;;; VNB-LAMBDA: typing

;;; The pointwise typing subgoal, read BACK.  For a single binder it is
;;;     forall v. v in A => body[x:=v] in B
;;; and for a binder list against a CARTESIAN domain one guarded universal per
;;; factor, in order, with the typed body innermost.  Each v must be fresh (it
;;; may be the binder itself, unrenamed) and the domains must be the factors of
;;; the lambda's own domain.
;;; Returns #t or a reason.
(define (rcs--lambda-typing-ok? f bvars doms body B)
  (let loop ((f f) (bvars bvars) (doms doms) (vs '()))
    (cond
      ((null? bvars)
       ;; vs holds the (binder . quantified variable) pairs, in reverse order
       (let ((b* (subst-free* (reverse vs) body)))
         (if (alpha-equiv? f (list 'IN b* B))
             #t
             "lambda-type: the typed body is not the lambda's body at the quantified variables")))
      ((not (and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3) (symbol? (cadr f))
                 (let ((imp (caddr f)))
                   (and (pair? imp) (eq? (car imp) 'IMPLIES) (= (length imp) 3)
                        (rcs--in? (cadr imp)) (eq? (cadr (cadr imp)) (cadr f))))))
       "lambda-type: the typing hypothesis is not a guarded universal for every binder")
      ((not (alpha-equiv? (caddr (cadr (caddr f))) (car doms)))
       "lambda-type: a guard is not the corresponding factor of the lambda's domain")
      ((not (or (eq? (cadr f) (car bvars))
                (and (rcs--fresh-for? (cadr f) (list body B))
                     (not (memq (cadr f) (map cdr vs))))))
       "lambda-type: a quantified variable is not fresh for the lambda's body and codomain")
      (#t (loop (caddr (caddr f)) (cdr bvars) (cdr doms)
                (cons (cons (car bvars) (cadr f)) vs))))))

(define (rcs-lambda-type rule hyps concl)
  (let ((g (rcs--goal concl)))
    (cond
      ((not (= (length hyps) 2)) "lambda-type: expects exactly two hypotheses")
      ((not (and (rcs--in? g)
                 (let ((subj (cadr g)) (cls (caddr g)))
                   (and (pair? subj) (eq? (car subj) 'VNB-LAMBDA) (= (length subj) 4)
                        (pair? cls) (eq? (car cls) 'FUN) (= (length cls) 3)))))
       "lambda-type: the conclusion is not (IN (VNB-LAMBDA bs A body) (FUN A B))")
      ((not (and (rcs--same-asms? (car hyps) concl) (rcs--same-asms? (cadr hyps) concl)))
       "lambda-type: a hypothesis does not keep the conclusion's assumptions")
      (#t
       (let* ((subj (cadr g))
              (cls  (caddr g))
              (bs   (cadr subj))
              (A    (cadr cls))
              (B    (caddr cls))
              (body (cadddr subj)))
         (cond
           ;; THE SOUNDNESS CONDITION: the domain the term declares is the
           ;; domain the FUN claims.  Without it one lambda types into FUN(A,B)
           ;; for every A.
           ((not (alpha-equiv? (caddr subj) A))
            "lambda-type: the lambda's declared domain is not the FUN's domain")
           ((not (alpha-equiv? (rcs--goal (cadr hyps)) (list 'IN A 'SET)))
            "lambda-type: the second hypothesis is not the sethood of the domain (IN A SET)")
           ((symbol? bs)
            (rcs--lambda-typing-ok? (rcs--goal (car hyps)) (list bs) (list A) body B))
           ((and (pair? bs) (eq? (car bs) 'LIST) (pair? (cdr bs))
                 (pair? A) (eq? (car A) 'CARTESIAN)
                 (= (length (cdr bs)) (length (cdr A))))
            (rcs--lambda-typing-ok? (rcs--goal (car hyps)) (cdr bs) (cdr A) body B))
           (#t "lambda-type: the binder list does not match a CARTESIAN domain factor for factor")))))))

;;; -----------------------------------------------------------------------
;;; VNB-LAMBDA: beta
;;;
;;; THE RELATION.  The conclusion's formula C and the hypothesis' formula C'
;;; are related when
;;;
;;;   C' is REACHABLE from C by a sequence of contractions, each taken at a
;;;   position of the term reached so far, and each either LICENSED where it
;;;   sits or OWED as one of the obligation hypotheses;
;;;
;;; a term a contraction CREATES may be contracted in its turn, under the same
;;; two conditions, judged where the created redex sits.  It is verified by
;;; walking C and C' in parallel: where they agree there is nothing to check;
;;; where they differ, C's side must be a redex, and the term it contracts to
;;; -- body and arguments AS THEY STAND -- must itself be related to C''s side.
;;; The contraction is computed here (`rcs--contract'), from the definition of
;;; beta reduction, not from the kernel's reducer.
;;;
;;; ONE LAYER WAS NOT ENOUGH (12-I, 2026-09-20).  Until today the relation
;;; offered each redex two readings, body and arguments either untouched or
;;; fully developed, and nothing between.  The kernel's walk is GUARDED, so it
;;; produces neither extreme: for the summand `finsum-reindex-ag' builds,
;;; (z in T |-> f(phi(z))) with f and phi both lambdas, applied at a point, it
;;; contracts phi(z) -- licensed by the binder's own domain -- leaves f(...)
;;; alone, since the obligation that redex would owe names the bound z, and
;;; then contracts the outer redex, carrying the half-contracted body with it.
;;; That is a PARTIAL development, and a sound inference was being refused
;;; ("the hypothesis' goal is not the goal with redexes contracted", 12-E).
;;; Reachability covers it, and covers the redexes a contraction creates, with
;;; no licence weakened: every step of the sequence carries the scope and the
;;; bound variables of the position it is taken at, and is licensed or owed
;;; there.  The search is bounded by FUEL and refuses when it runs out.
;;;
;;; The SCOPE is carried down, exactly as the meaning of the rule requires: a
;;; redex under `forall v in A. ...' or inside the body of a binder over A knows
;;; that its bound variable lies in A.  That is what licenses reducing there.
;;;
;;; INNERMOST FIRST, AND THE LICENCE IS ABOUT THE TERM, NOT ITS SPELLING.
;;; Contraction is a bottom-up pass: the arguments of a redex are contracted
;;; before the redex itself, so what is substituted for the binder is the
;;; argument's CONTRACTED form, and the membership that licenses the step is
;;; that form's.  Example (qq-field-is-field, 2026-09-20):
;;;
;;;   (VNB-LAMBDA [x_,y_] CARTESIAN(QQ,QQ) x_*y_)
;;;      (a_, (VNB-LAMBDA x_ DIFFERENCE(QQ,SINGLETON(0)) RECIP(x_))(a_))
;;;
;;; The outer redex's second argument is itself a redex; it contracts to
;;; `RECIP(a_)', and it is `RECIP(a_) in QQ' that the context holds.  Testing
;;; the membership of the argument AS WRITTEN refuses a licensed reduction --
;;; the checker did exactly that until 2026-09-20 and stopped four library
;;; proofs.  Both spellings are therefore accepted, with the soundness argument
;;; beside `rcs--beta-licences-ok?' -- where the developed spelling also brings
;;; the argument's own redexes into the accounting.

(define (rcs--redex-single? e)
  (and (pair? e) (= (length e) 2)
       (pair? (car e)) (eq? (caar e) 'VNB-LAMBDA) (= (length (car e)) 4)
       (symbol? (cadr (car e)))))

(define (rcs--redex-multi? e)
  (and (pair? e) (pair? (car e)) (eq? (caar e) 'VNB-LAMBDA) (= (length (car e)) 4)
       (pair? (cadr (car e))) (eq? (car (cadr (car e))) 'LIST)
       (= (length (cdr (cadr (car e)))) (length (cdr e)))))

(define (rcs--redex? e) (or (rcs--redex-single? e) (rcs--redex-multi? e)))

;;; The complete development: contract every redex, innermost first, in
;;; parallel.  A redex created BY the substitution is not contracted -- one
;;; pass, which is what "contracting the redexes that are there" means.
(define (rcs--dev e)
  (cond
    ((not (pair? e)) e)
    ((rcs--redex-single? e)
     (subst-free (cadr (car e)) (rcs--dev (cadr e)) (rcs--dev (cadddr (car e)))))
    ((rcs--redex-multi? e)
     (subst-free* (map cons (cdr (cadr (car e))) (map rcs--dev (cdr e)))
                  (rcs--dev (cadddr (car e)))))
    (#t (cons (rcs--dev (car e)) (map rcs--dev (cdr e))))))

;;; The memberships a binder contributes inside its own body.
(define (rcs--binder-scope bs A)
  (cond ((symbol? bs) (list (list 'IN bs A)))
        ((and (pair? bs) (eq? (car bs) 'LIST)
              (pair? A) (eq? (car A) 'CARTESIAN)
              (= (length (cdr bs)) (length (cdr A))))
         (map (lambda (v d) (list 'IN v d)) (cdr bs) (cdr A)))
        (#t '())))

;;; Adding to the scope.  A membership that holds where the redex sits holds in
;;; its contracted form too -- the contraction of a redex inside the guard is
;;; itself accounted for by this same relation, so the two formulas are the same
;;; proposition -- and the kernel threads the UNCONTRACTED form while it emits
;;; the contracted one.  Both are carried, so neither spelling refuses a licence
;;; the other grants.
(define (rcs--scope-add fs scope)
  (let loop ((fs fs) (acc scope))
    (if (null? fs)
        acc
        (let* ((f (car fs)) (d (rcs--dev f)))
          (loop (cdr fs) (if (equal? f d) (cons f acc) (cons f (cons d acc))))))))

;;; THE SHADOWING RULE (2026-09-20, batch 11-C).  A scope entry, and an
;;; assumption of the sequent, speak about the variables in scope at the ROOT of
;;; the formula.  Under a binder that re-binds one of those names the same
;;; formula is about another variable and licenses nothing there.  The checker
;;; carried both through every binder, exactly as the kernel's reducer did, so
;;; it verified the inference that made FALSITY derivable:
;;;
;;;   forall u in NN. forall u in ZZ. (lambda z_ in NN. z_)(u) = u
;;;
;;; reduced to `u = u' on the strength of the OUTER guard and was accepted.
;;; `bvars' is the list of variables bound between the root and the redex; the
;;; walk drops the scope entries they shadow, `rcs--unshadowed' drops the
;;; assumptions they shadow at the licence test, and an OBLIGATION naming one of
;;; them excuses nothing -- posted in the parent's context it is a formula about
;;; another variable.
(define (rcs--mentions-any? vars e)
  (and (pair? vars)
       (let ((fvs (free-vars e)))
         (chk-any (lambda (v) (memq v fvs)) vars))))

(define (rcs--unshadowed bvars fs)
  (if (null? bvars)
      fs
      (filter (lambda (f) (not (rcs--mentions-any? bvars f))) fs)))

;;; The variables a bind-spec binds -- a symbol, or (LIST x y ...).
(define (rcs--bspec-vars bs)
  (cond ((symbol? bs) (list bs))
        ((and (pair? bs) (eq? (car bs) 'LIST)) (filter symbol? (cdr bs)))
        (#t '())))

(define (rcs--guarded-forall? e)
  (and (pair? e) (eq? (car e) 'FORALL) (= (length e) 3)
       (let ((imp (caddr e)))
         (and (pair? imp) (eq? (car imp) 'IMPLIES) (= (length imp) 3)
              (rcs--in? (cadr imp)) (eq? (cadr (cadr imp)) (cadr e))))))

;;; Every redex of E, each as `rcs--rx-record' writes it -- the arguments as
;;; spelled and developed, the domain, the scope that holds where it sits, the
;;; variables bound between the root and it, and its own arguments' redexes.
;;; Used to account for the redexes that a contraction consumes or discards:
;;; they are contracted too, and owe their own licences.
;;;
;;; The binder cases are driven from `binder-shape' (expressions.scm), so a head
;;; declared a binder there is one here with no second list to edit.
(define (rcs--collect-redexes e scope bvars)
  (define (under vs extra x)
    (rcs--collect-redexes x
                          (rcs--scope-add extra (rcs--unshadowed vs scope))
                          (append vs bvars)))
  (cond
    ((not (pair? e)) '())
    ((rcs--redex? e)
     (let* ((lam  (car e))
            (bspec (cadr lam))
            (dom  (caddr lam))
            (body (cadddr lam)))
       (cons (rcs--rx-record e scope bvars)
             (append (under (rcs--bspec-vars bspec) (rcs--binder-scope bspec dom) body)
                     (rcs--collect-redexes dom scope bvars)
                     (rcs--collect-list (cdr e) scope bvars)))))
    ((rcs--guarded-forall? e)
     (let* ((v (cadr e)) (imp (caddr e)) (guard (cadr imp)))
       (append (under (list v) '() guard)
               (under (list v) (list guard) (caddr imp)))))
    ((and (symbol? (car e)) (memq (binder-shape (car e)) '(domain lambda))
          (= (length e) 4))
     (append (rcs--collect-redexes (caddr e) scope bvars)     ; the domain is outside
             (under (rcs--bspec-vars (cadr e))
                    (rcs--binder-scope (cadr e) (caddr e))
                    (cadddr e))))
    ((and (symbol? (car e)) (eq? 'simple (binder-shape (car e)))
          (= (length e) 3) (symbol? (cadr e)))
     (under (list (cadr e)) '() (caddr e)))
    (#t (rcs--collect-list e scope bvars))))

(define (rcs--collect-list es scope bvars)
  (let loop ((es es) (acc '()))
    (if (or (not (pair? es)) (null? es))
        acc
        (loop (cdr es) (append acc (rcs--collect-redexes (car es) scope bvars))))))

;;; ONE contraction, at the root of the redex E, with the body and the
;;; arguments AS THEY STAND.  What the substitution creates -- or copies out of
;;; the arguments -- is not contracted here: each such redex is a step of its
;;; own, taken below, at the position where it appears and with the scope and
;;; the bound variables that hold there.
(define (rcs--contract e)
  (cond
    ((rcs--redex-single? e)
     (subst-free (cadr (car e)) (cadr e) (cadddr (car e))))
    ((rcs--redex-multi? e)
     (subst-free* (map cons (cdr (cadr (car e))) (cdr e)) (cadddr (car e))))
    (#t #f)))

;;; The record of one contraction: the arguments as spelled and as developed
;;; (both spellings may carry the licence -- see `rcs--beta-licences-ok?'), the
;;; lambda's domain, the scope and bound variables where the step is taken, and
;;; the redexes sitting INSIDE the arguments, which the developed spelling of
;;; the licence commits this inference to.
(define (rcs--rx-record e scope bvars)
  (let* ((lam   (car e))
         (dargs (map rcs--dev (cdr e)))
         ;; the VALUE of the contraction, on the developed arguments (2026-10-01)
         (value (if (symbol? (cadr lam))
                    (subst-free (cadr lam) (car dargs) (cadddr lam))
                    (subst-free* (map cons (cdr (cadr lam)) dargs) (cadddr lam)))))
    (list (cdr e) dargs (caddr lam) scope bvars
          (rcs--collect-list (cdr e) scope bvars)
          value)))

;;; THE FUEL.  Contraction does not terminate in general -- (\x.x x)(\x.x x) --
;;; and the search backtracks (contract this redex, or walk past it), so the
;;; number of contractions it may take is bounded.  Exhaustion is a REFUSAL
;;; that says so, never an acceptance and never a loop.
(define rcs--beta-fuel-limit 400)

(define (rcs--fuel-new) (vector rcs--beta-fuel-limit #f))

(define (rcs--fuel-take! f)
  (cond ((> (vector-ref f 0) 0) (vector-set! f 0 (- (vector-ref f 0) 1)) #t)
        (#t (vector-set! f 1 #t) #f)))

(define (rcs--fuel-spent? f) (vector-ref f 1))

;;; rcs--beta-match: is H reachable from C by contractions?  Returns the list
;;; of the contractions taken, each as `rcs--rx-record' writes it, or #f.  At
;;; each node the search tries the contraction FIRST and the parallel walk
;;; second, so it backtracks over both readings of every redex it meets: that
;;; is what lets a PARTIAL development match.  The entry point gives the search
;;; a fresh tank of fuel; the checkers
;;; below use `rcs--beta-match/fuel' directly, so that an exhausted tank can be
;;; told apart from a genuine mismatch in the refusal they print.
(define (rcs--beta-match c h scope bvars acc)
  (rcs--beta-match/fuel c h scope bvars acc (rcs--fuel-new)))

(define (rcs--beta-match/fuel c h scope bvars acc fuel)
  (cond
    ((alpha-equiv? c h) acc)
    (#t
     (or (and (rcs--redex? c)
              (rcs--fuel-take! fuel)
              (let ((c1 (rcs--contract c)))
                (and c1
                     ;; the contractum sits where the redex sat: same scope,
                     ;; same bound variables, and it may be contracted further
                     (rcs--beta-match/fuel
                       c1 h scope bvars
                       (cons (rcs--rx-record c scope bvars) acc) fuel))))
         (rcs--beta-match-children c h scope bvars acc fuel)))))

(define (rcs--beta-match-children c h scope bvars acc fuel)
  ;; descending under a binder: drop what it shadows, add what it grants
  (define (under vs extra cc hh a)
    (rcs--beta-match/fuel cc hh
                     (rcs--scope-add extra (rcs--unshadowed vs scope))
                     (append vs bvars) a fuel))
  (cond
    ((or (not (pair? c)) (not (pair? h))) #f)
    ;; under forall v in A the variable v is in A
    ((and (rcs--guarded-forall? c) (rcs--guarded-forall? h) (eq? (cadr c) (cadr h)))
     (let* ((v (cadr c)) (ic (caddr c)) (ih (caddr h)) (guard (cadr ic)))
       (let ((acc1 (under (list v) '() guard (cadr ih) acc)))
         (and acc1 (under (list v) (list guard) (caddr ic) (caddr ih) acc1)))))
    ;; the domain-carrying binders: inside the body the variable is in A.  Read
    ;; off `binder-shape' (expressions.scm), not a second list of heads.
    ((and (symbol? (car c)) (memq (binder-shape (car c)) '(domain lambda))
          (eq? (car h) (car c))
          (= (length c) 4) (= (length h) 4) (equal? (cadr c) (cadr h)))
     (let ((acc1 (rcs--beta-match/fuel (caddr c) (caddr h) scope bvars acc fuel)))  ; domain: outside
       (and acc1
            (under (rcs--bspec-vars (cadr c))
                   (rcs--binder-scope (cadr c) (caddr c))
                   (cadddr c) (cadddr h) acc1))))
    ;; the simple binders (FORALL unguarded, FORSOME, IOTA, COMP): they grant
    ;; nothing and SHADOW everything of their name.
    ((and (symbol? (car c)) (eq? 'simple (binder-shape (car c)))
          (eq? (car h) (car c)) (= (length c) 3) (= (length h) 3)
          (symbol? (cadr c)) (eq? (cadr c) (cadr h)))
     (under (list (cadr c)) '() (caddr c) (caddr h) acc))
    ((not (= (length c) (length h))) #f)
    (#t (let loop ((cs c) (hs h) (a acc))
          (if (null? cs)
              a
              (let ((a1 (rcs--beta-match/fuel (car cs) (car hs) scope bvars a fuel)))
                (and a1 (loop (cdr cs) (cdr hs) a1))))))))

;;; The membership that licenses a redex, and the obligation it owes when the
;;; context does not evidently hold it.
(define (rcs--beta-obligation args A)
  (if (= (length args) 1)
      (list 'IN (car args) A)
      (list 'IN (cons 'LIST args) A)))

(define (rcs--cartesian-of? A n)
  (and (pair? A) (eq? (car A) 'CARTESIAN) (= (length (cdr A)) n)))

(define (rcs--componentwise? as ds known)
  (let loop ((as as) (ds ds))
    (or (null? as)
        (and (chk-mem? (list 'IN (car as) (car ds)) known)
             (loop (cdr as) (cdr ds))))))

(define (rcs--rx-args  r) (car r))       ; the arguments as the CONCLUSION spells them
(define (rcs--rx-dargs r) (cadr r))      ; the arguments DEVELOPED (see rcs--rx-record)
(define (rcs--rx-dom   r) (caddr r))
(define (rcs--rx-scope r) (cadddr r))
(define (rcs--rx-bvars r) (car (cddddr r)))   ; bound between the root and the redex
(define (rcs--rx-inner r) (cadr (cddddr r)))  ; the redexes inside the arguments
(define (rcs--rx-value r) (caddr (cddddr r)))  ; the reduct, on the developed arguments (2026-10-01)

(define (rcs--beta-licensed? args A known)
  (cond
    ((= (length args) 1)
     (or (chk-mem? (list 'IN (car args) A) known)
         (let ((u (car args)))
           (and (pair? u) (eq? (car u) 'LIST)
                (rcs--cartesian-of? A (length (cdr u)))
                (rcs--componentwise? (cdr u) (cdr A) known)))))
    ((rcs--cartesian-of? A (length args))
     (rcs--componentwise? args (cdr A) known))
    (#t (chk-mem? (list 'IN (cons 'LIST args) A) known))))

;;; The two spellings of one redex's licence: the argument as the conclusion
;;; writes it, and the argument after the redexes inside it have been
;;; contracted.  EITHER may carry the membership.  The kernel contracts the
;;; arguments FIRST and judges the licence on the contracted ones
;;; (reduce-lambda-in-expr/scope), so the contracted spelling is the one it
;;; uses; the uncontracted one is kept because a driver may have typed the term
;;; it wrote.
;;;
;;; THE DEVELOPED SPELLING IS NOT FREE.  `u in A' and `u* in A' are the same
;;; proposition only when the contractions that take u to u* are themselves
;;; part of this inference -- otherwise the checker would accept a licence for
;;; a term the inference never formed, and a redex whose argument is undefined
;;; (an off-domain application inside it) would pass on the strength of its
;;; contractum.  So a licence granted through the developed spelling ADDS the
;;; argument's own redexes to the list to be accounted for, which is what the
;;; old two-variant matcher did by collecting them.
(define (rcs--rx-owed r)
  (let ((o1 (rcs--beta-obligation (rcs--rx-dargs r) (rcs--rx-dom r)))
        (o2 (rcs--beta-obligation (rcs--rx-args  r) (rcs--rx-dom r)))
        (o3 (list 'IN (rcs--rx-value r) 'SET)))          ; the value's sethood (2026-10-01)
    (if (equal? o1 o2) (list o1 o3) (list o1 o2 o3))))

;;; THE VALUE CERTIFICATE, the checker's own reading (the builder's is
;;; `pi--value-may-be-class?', primitive-inferences.scm; written apart on purpose).
;;; A contraction owes `(IN value SET)' exactly when the value MAY denote a proper
;;; class: SET or ORD; an untyped bare symbol; POWER / FUN / TUPLES / INJECTION /
;;; BIJECTION of such a thing; SEP, VNB-LAMBDA, BIG-UNION or IMAGE over such a domain;
;;; COMP; UNION, INTERSECTION, DIFFERENCE, COMPLEMENT-IN, CARTESIAN with such a part;
;;; an IF with such a branch; a registered functoid applied, by its body.  Everything
;;; else -- numerals, typed symbols, the set constants, LIST, PAIR, INTERVAL, NTH,
;;; LENGTH, CHOICE, IOTA, arithmetic, an application of a variable, an accessor of a
;;; structure the context holds -- denotes a set or nothing, and owes nothing.
;; the memberships a redex's argument carries, licensed or owed: they type the value
(define (rcs--arg-typings args A)
  (cond ((and (= (length args) 1) (pair? (car args)) (eq? (car (car args)) 'LIST)
              (pair? A) (eq? (car A) 'CARTESIAN) (= (length (cdr (car args))) (length (cdr A))))
         (cons (list 'IN (car args) A) (map (lambda (a d) (list 'IN a d)) (cdr (car args)) (cdr A))))
        ((= (length args) 1) (list (list 'IN (car args) A)))
        ((and (pair? A) (eq? (car A) 'CARTESIAN) (= (length args) (length (cdr A))))
         (cons (list 'IN (cons 'LIST args) A) (map (lambda (a d) (list 'IN a d)) args (cdr A))))
        (else (list (list 'IN (cons 'LIST args) A)))))

(define (chk-value-may-be-class? t known)
  (define (raw e) (if (wff? e) (wff-formula e) e))
  (define (holds? pred)
    (let loop ((es known))
      (cond ((null? es) #f) ((pred (raw (car es))) #t) (else (loop (cdr es))))))
  (define (typed? u)
    (holds? (lambda (f) (and (pair? f) (eq? (car f) 'IN) (= (length f) 3) (chk-same? (cadr f) u)))))
  (define (struct-pred? s)
    (holds? (lambda (f) (and (pair? f) (= (length f) 2) (symbol? (car f)) (chk-same? (cadr f) s)
                             (let ((nm (string-downcase (symbol->string (car f)))))
                               (and (> (string-length nm) 3) (string=? (substring nm 0 3) "is-")
                                    (environment-bound? system-global-environment 'find-shape-structure)
                                    (find-shape-structure (string->symbol (substring nm 3 (string-length nm))))
                                    #t))))))
  (define (registry-ref name)             ; see pi--registry-ref: the registry lives in the
    (call-with-current-continuation         ; load's environment, not system-global
      (lambda (k)
        (with-exception-handler (lambda (e) (k #f))
          (lambda () (hash-table-ref/default *functoid-registry* name #f))))))
  (define (unfold t)
    (and (pair? t) (symbol? (car t))
         (let ((reg (registry-ref (car t))))
           (and reg (list? reg) (>= (length reg) 2)
                (list? (car reg)) (= (length (car reg)) (length (cdr t)))
                (subst-free* (map cons (car reg) (cdr t)) (cadr reg))))))
  (define (any-may? ts d) (let loop ((ts ts)) (and (pair? ts) (or (may? (car ts) d) (loop (cdr ts))))))
  (define (may? t d)
    (cond ((> d 8) #t)
          ((not (pair? t))
           (and (symbol? t)
                (not (memq t '(NN ZZ QQ RR CC EMPTY-SET RR-STAR RR-POS-STAR POS-INF NEG-INF)))
                (or (memq t '(SET ORD)) (not (typed? t)))
                #t))
          ((memq (car t) '(LIST PAIR INTERVAL NTH LENGTH CHOICE IOTA + - * min max abs succ ^)) #f)
          ((memq (car t) '(POWER FUN TUPLES INJECTION BIJECTION)) (any-may? (cdr t) (+ d 1)))
          ((eq? (car t) 'COMP) #t)
          ((and (memq (car t) '(SEP VNB-LAMBDA BIG-UNION)) (= (length t) 4)) (may? (caddr t) (+ d 1)))
          ((and (eq? (car t) 'IMAGE) (= (length t) 3)) (may? (caddr t) (+ d 1)))
          ((memq (car t) '(UNION INTERSECTION DIFFERENCE COMPLEMENT-IN CARTESIAN)) (any-may? (cdr t) (+ d 1)))
          ((eq? (car t) 'IF) (any-may? (cddr t) (+ d 1)))
          ((and (= (length t) 2) (symbol? (car t)) (struct-pred? (cadr t))) #f)
          ((unfold t) => (lambda (b) (may? b (+ d 1))))
          (else #f)))
  (may? t 0))

;;; Each contracted redex must be licensed where it sits, or owe its membership
;;; among the obligation hypotheses; and no obligation may be owed by no redex.
;;;
;;; The second half is hygiene, not soundness -- an extra obligation is an
;;; extra leaf to prove, which only weakens the inference -- so its owner may
;;; also be a redex that merely OCCURS in the conclusion (`others'): the kernel
;;; develops an argument before substituting it, and a body that discards its
;;; binder then owes for a contraction that leaves no trace in the result.
(define (rcs--beta-licences-ok? tag redexes gamma obligations others)
  (let loop ((rs redexes))
    (cond
      ((null? rs)
       (let check ((os obligations))
         (cond
           ((null? os) #t)
           ((let same ((rs (append redexes others)))
              (and (pair? rs)
                   (or (chk-mem? (car os) (rcs--rx-owed (car rs)))
                       (same (cdr rs)))))
            (check (cdr os)))
           (#t (string-append tag ": an obligation hypothesis belongs to no contracted redex")))))
      (#t
       (let* ((r     (car rs))
              (bvs   (rcs--rx-bvars r))
              ;; an assumption naming a variable bound where the redex sits is
              ;; about ANOTHER variable and licenses nothing
              (known (append (rcs--rx-scope r) (rcs--unshadowed bvs gamma)))
              (owed? (lambda (o)
                       (and (not (rcs--mentions-any? bvs o))
                            (chk-mem? o obligations))))
              (as-written (rcs--beta-obligation (rcs--rx-args  r) (rcs--rx-dom r)))
              (developed  (rcs--beta-obligation (rcs--rx-dargs r) (rcs--rx-dom r))))
         (cond
           ;; the argument AS THE CONCLUSION WRITES IT: nothing else is needed
           ;; the VALUE must be a set, by certificate or by obligation (2026-10-01)
           ((and (chk-value-may-be-class? (rcs--rx-value r)
                                          (append (rcs--arg-typings (rcs--rx-dargs r) (rcs--rx-dom r))
                                                  (rcs--arg-typings (rcs--rx-args r) (rcs--rx-dom r))
                                                  known gamma))
                 (not (owed? (list 'IN (rcs--rx-value r) 'SET))))
            (string-append
             tag ": a redex was contracted to a value that may be a proper class, and no obligation (IN value SET) was posted"))
           ((or (rcs--beta-licensed? (rcs--rx-args r) (rcs--rx-dom r) known)
                (owed? as-written))
            (loop (cdr rs)))
           ;; the DEVELOPED argument: the contractions inside it come with it
           ((or (rcs--beta-licensed? (rcs--rx-dargs r) (rcs--rx-dom r) known)
                (owed? developed))
            (loop (append (rcs--rx-inner r) (cdr rs))))
           (#t
            (string-append
             tag ": a redex was contracted off its domain -- neither the context nor the binders it sits under give the argument's membership, in either spelling, and no obligation was posted (an obligation naming a variable bound where the redex sits is not one: it would be read in the parent's context, about another variable)"))))))))

;;; lambda-beta: the goal reduced, plus one obligation per unlicensed redex.
(define (rcs-lambda-beta rule hyps concl)
  (cond
    ((null? hyps) "lambda-beta: expects at least the reduced goal")
    ((not (rcs--same-asms? (car hyps) concl))
     "lambda-beta: the reduced goal does not keep the conclusion's assumptions")
    ((not (chk-every (lambda (o) (rcs--same-asms? o concl)) (cdr hyps)))
     "lambda-beta: an obligation does not keep the conclusion's assumptions")
    (#t
     (let* ((fuel (rcs--fuel-new))
            (acc  (rcs--beta-match/fuel (rcs--goal concl) (rcs--goal (car hyps))
                                        '() '() '() fuel)))
       (cond
         ((not acc)
          (if (rcs--fuel-spent? fuel)
              "lambda-beta: no contraction path from the goal to the hypothesis' goal was found before the search ran out of fuel"
              "lambda-beta: the hypothesis' goal is not the goal with redexes contracted"))
         (#t
          (rcs--beta-licences-ok? "lambda-beta" acc (rcs--asms concl)
                                  (map rcs--goal (cdr hyps))
                                  ;; only the ORPHAN check reads this, and it
                                  ;; runs only when an obligation was posted
                                  (if (null? (cdr hyps))
                                      '()
                                      (rcs--collect-redexes (rcs--goal concl) '() '())))))))))

;;; lambda-beta-hyp: one assumption replaced by its contraction, everything
;;; else kept, plus the same obligations.
(define (rcs-lambda-beta-hyp rule hyps concl)
  (cond
    ((null? hyps) "lambda-beta-hyp: expects at least the main hypothesis")
    ((not (alpha-equiv? (rcs--goal (car hyps)) (rcs--goal concl)))
     "lambda-beta-hyp: the hypothesis changes the goal")
    ((not (chk-every (lambda (o) (rcs--same-asms? o concl)) (cdr hyps)))
     "lambda-beta-hyp: an obligation does not keep the conclusion's assumptions")
    (#t
     ;; Every candidate pair is tried: one that MATCHES but whose licences do
     ;; not hold must not hide another that is the step actually taken.  The
     ;; last licence failure is what is reported when no pair goes through.
     (let* ((gamma  (rcs--asms concl))
            (gamma* (rcs--asms (car hyps)))
            (obs    (map rcs--goal (cdr hyps)))
            (why    #f)
            (spent  #f))
       (let outer ((fs gamma))
         (cond
           ((null? fs)
            (or why
                (if spent
                    "lambda-beta-hyp: no contraction path to the replaced assumption was found before the search ran out of fuel"
                    "lambda-beta-hyp: no assumption of the conclusion is replaced by its contraction")))
           (#t
            (let ((rest (rcs--drop (car fs) gamma)))
              (let inner ((cs gamma*))
                (cond
                  ((null? cs) (outer (cdr fs)))
                  ((not (chk-set=? gamma* (cons (car cs) rest))) (inner (cdr cs)))
                  (#t
                   (let* ((fuel (rcs--fuel-new))
                          (acc  (rcs--beta-match/fuel (car fs) (car cs) '() '() '() fuel)))
                     (if (rcs--fuel-spent? fuel) (set! spent #t))
                     (if (not acc)
                         (inner (cdr cs))
                         (let ((v (rcs--beta-licences-ok?
                                    "lambda-beta-hyp" acc gamma obs
                                    (if (null? obs)
                                        '()
                                        (rcs--collect-redexes (car fs) '() '())))))
                           (if (eq? v #t)
                               #t
                               (begin (set! why v) (inner (cdr cs))))))))))))))))))

;;; -----------------------------------------------------------------------
;;; Registration

;; The beta checker's walk reads `binder-shape' (expressions.scm) rather than
;; keeping its own list of heads: a binder declared there shadows the scope and
;; the context here with no edit.  (declare-binder-walker! is the gate.)
(declare-binder-walker! 'rcs--collect-redexes     'from-binder-shapes)
(declare-binder-walker! 'rcs--beta-match-children 'from-binder-shapes)

(register-rule-checker! 'sep-sethood          rcs-sep-sethood)
(register-rule-checker! 'sep-mem-intro        rcs-sep-mem-intro)
(register-rule-checker! 'sep-mem-elim         rcs-sep-mem-elim)
(register-rule-checker! 'comp-mem-intro       rcs-comp-mem-intro)
(register-rule-checker! 'comp-mem-elim        rcs-comp-mem-elim)
(register-rule-checker! 'big-union-sethood    rcs-big-union-sethood)
(register-rule-checker! 'big-union-mem-intro  rcs-big-union-mem-intro)
(register-rule-checker! 'big-union-mem-elim   rcs-big-union-mem-elim)
(register-rule-checker! 'iota-def             rcs-iota-def)
(register-rule-checker! 'iota-in-elim         rcs-iota-in-elim)
(register-rule-checker! 'lambda-type          rcs-lambda-type)
(register-rule-checker! 'lambda-beta          rcs-lambda-beta)
(register-rule-checker! 'lambda-beta-hyp      rcs-lambda-beta-hyp)
