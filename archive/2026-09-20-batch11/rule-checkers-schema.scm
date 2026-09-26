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
;;; The relation: the hypothesis' formula is obtained from the conclusion's by
;;; CONTRACTING some redexes.  It is verified by walking the two formulas in
;;; parallel: where they agree there is nothing to check; where they differ the
;;; conclusion's side must be a redex whose contraction is what stands on the
;;; hypothesis' side.  The contraction is computed here (`rcs--dev'), from the
;;; definition of beta reduction, not from the kernel's reducer.
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
;;; proofs.  Both spellings are therefore accepted (`rcs--rx-licensed?'), with
;;; the soundness argument beside that procedure.

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

(define (rcs--guarded-forall? e)
  (and (pair? e) (eq? (car e) 'FORALL) (= (length e) 3)
       (let ((imp (caddr e)))
         (and (pair? imp) (eq? (car imp) 'IMPLIES) (= (length imp) 3)
              (rcs--in? (cadr imp)) (eq? (cadr (cadr imp)) (cadr e))))))

;;; Every redex of E, each recorded as (args contracted-args domain scope) with
;;; the scope that holds where it sits.  Used to account for the redexes that
;;; disappear inside a contraction: they are contracted too, and owe their own
;;; licences.
(define (rcs--collect-redexes e scope)
  (cond
    ((not (pair? e)) '())
    ((rcs--redex? e)
     (let* ((lam  (car e))
            (bspec (cadr lam))
            (dom  (caddr lam))
            (body (cadddr lam)))
       (cons (list (cdr e) (map rcs--dev (cdr e)) dom scope)
             (append (rcs--collect-redexes body (rcs--scope-add (rcs--binder-scope bspec dom) scope))
                     (rcs--collect-redexes dom scope)
                     (rcs--collect-list (cdr e) scope)))))
    ((rcs--guarded-forall? e)
     (let* ((imp (caddr e)) (guard (cadr imp)))
       (append (rcs--collect-redexes guard scope)
               (rcs--collect-redexes (caddr imp) (rcs--scope-add (list guard) scope)))))
    ((and (memq (car e) '(VNB-LAMBDA SEP BIG-UNION)) (= (length e) 4))
     (append (rcs--collect-redexes (caddr e) scope)
             (rcs--collect-redexes (cadddr e)
                                   (rcs--scope-add (rcs--binder-scope (cadr e) (caddr e)) scope))))
    (#t (rcs--collect-list e scope))))

(define (rcs--collect-list es scope)
  (let loop ((es es) (acc '()))
    (if (or (not (pair? es)) (null? es))
        acc
        (loop (cdr es) (append acc (rcs--collect-redexes (car es) scope))))))

;;; Does contracting the redex C itself give H?  The body and the arguments may
;;; each stand as they are or be developed in their turn; whichever variant
;;; matches, the redexes it consumed are returned with this one.  #f if none.
(define (rcs--redex-match c h scope)
  (let* ((lam   (car c))
         (bspec (cadr lam))
         (dom   (caddr lam))
         (body  (cadddr lam))
         (args  (cdr c))
         (vars  (if (symbol? bspec) (list bspec) (cdr bspec)))
         (inner (rcs--scope-add (rcs--binder-scope bspec dom) scope))
         (dargs (map rcs--dev args))
         (bodies  (list (cons body '())
                        (cons (rcs--dev body) (rcs--collect-redexes body inner))))
         (argsets (list (cons args '())
                        (cons dargs (rcs--collect-list args scope)))))
    ;; The second slot of the record is the argument list AS SUBSTITUTED: only
    ;; when the contracted arguments are what went in are their inner redexes
    ;; part of this inference, and only then may their memberships license it.
    (let loop-b ((bs bodies))
      (and (pair? bs)
           (or (let loop-a ((as argsets))
                 (and (pair? as)
                      (or (and (alpha-equiv?
                                 h (subst-free* (map cons vars (car (car as))) (car (car bs))))
                               (cons (list args (car (car as)) dom scope)
                                     (append (cdr (car bs)) (cdr (car as)))))
                          (loop-a (cdr as)))))
               (loop-b (cdr bs)))))))

;;; rcs--beta-match: is H the result of contracting some redexes of C?
;;; Returns the list of contracted redexes, each as
;;; (args contracted-args domain scope), or #f.
(define (rcs--beta-match c h scope acc)
  (cond
    ((alpha-equiv? c h) acc)
    (#t
     (let ((hit (and (rcs--redex? c) (rcs--redex-match c h scope))))
       (if hit
           (append hit acc)
           (rcs--beta-match-children c h scope acc))))))

(define (rcs--beta-match-children c h scope acc)
  (cond
    ((or (not (pair? c)) (not (pair? h))) #f)
    ;; under forall v in A the variable v is in A
    ((and (rcs--guarded-forall? c) (rcs--guarded-forall? h) (eq? (cadr c) (cadr h)))
     (let* ((ic (caddr c)) (ih (caddr h)) (guard (cadr ic)))
       (let ((acc1 (rcs--beta-match guard (cadr ih) scope acc)))
         (and acc1 (rcs--beta-match (caddr ic) (caddr ih)
                                    (rcs--scope-add (list guard) scope) acc1)))))
    ;; the three domain-carrying binders: inside the body the variable is in A
    ((and (memq (car c) '(VNB-LAMBDA SEP BIG-UNION)) (eq? (car h) (car c))
          (= (length c) 4) (= (length h) 4) (equal? (cadr c) (cadr h)))
     (let ((acc1 (rcs--beta-match (caddr c) (caddr h) scope acc)))
       (and acc1
            (rcs--beta-match (cadddr c) (cadddr h)
                             (rcs--scope-add (rcs--binder-scope (cadr c) (caddr c)) scope)
                             acc1))))
    ((not (= (length c) (length h))) #f)
    (#t (let loop ((cs c) (hs h) (a acc))
          (if (null? cs)
              a
              (let ((a1 (rcs--beta-match (car cs) (car hs) scope a)))
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
(define (rcs--rx-dargs r) (cadr r))      ; the arguments AS SUBSTITUTED (see rcs--redex-match)
(define (rcs--rx-dom   r) (caddr r))
(define (rcs--rx-scope r) (cadddr r))

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
;;; contracted.  EITHER may carry the membership, and accepting either is sound:
;;; the inner contraction is itself one of the contractions this inference
;;; performs, so it is licensed or owed by this same relation, and under that
;;; accounting the two terms denote the same thing -- `u in A' and `u' in A'
;;; are then the same proposition.  The kernel contracts the arguments FIRST and
;;; judges the licence on the contracted ones (reduce-lambda-in-expr/scope), so
;;; the contracted spelling is the one it uses; the uncontracted one is kept
;;; because a driver may have typed the term it wrote.
(define (rcs--rx-licensed? r known)
  (or (rcs--beta-licensed? (rcs--rx-dargs r) (rcs--rx-dom r) known)
      (rcs--beta-licensed? (rcs--rx-args  r) (rcs--rx-dom r) known)))

(define (rcs--rx-owed r)
  (let ((o1 (rcs--beta-obligation (rcs--rx-dargs r) (rcs--rx-dom r)))
        (o2 (rcs--beta-obligation (rcs--rx-args  r) (rcs--rx-dom r))))
    (if (equal? o1 o2) (list o1) (list o1 o2))))

;;; Each contracted redex must be licensed where it sits, or owe its membership
;;; among the obligation hypotheses; and no obligation may be owed by no redex.
(define (rcs--beta-licences-ok? tag redexes gamma obligations)
  (let loop ((rs redexes))
    (cond
      ((null? rs)
       (let check ((os obligations))
         (cond
           ((null? os) #t)
           ((let same ((rs redexes))
              (and (pair? rs)
                   (or (chk-mem? (car os) (rcs--rx-owed (car rs)))
                       (same (cdr rs)))))
            (check (cdr os)))
           (#t (string-append tag ": an obligation hypothesis belongs to no contracted redex")))))
      ((or (rcs--rx-licensed? (car rs) (append (rcs--rx-scope (car rs)) gamma))
           (chk-any (lambda (o) (chk-mem? o obligations)) (rcs--rx-owed (car rs))))
       (loop (cdr rs)))
      (#t (string-append
           tag ": a redex was contracted off its domain -- neither the context nor the binders it sits under give the argument's membership, in either spelling, and no obligation was posted")))))

;;; lambda-beta: the goal reduced, plus one obligation per unlicensed redex.
(define (rcs-lambda-beta rule hyps concl)
  (cond
    ((null? hyps) "lambda-beta: expects at least the reduced goal")
    ((not (rcs--same-asms? (car hyps) concl))
     "lambda-beta: the reduced goal does not keep the conclusion's assumptions")
    ((not (chk-every (lambda (o) (rcs--same-asms? o concl)) (cdr hyps)))
     "lambda-beta: an obligation does not keep the conclusion's assumptions")
    (#t
     (let ((acc (rcs--beta-match (rcs--goal concl) (rcs--goal (car hyps)) '() '())))
       (if (not acc)
           "lambda-beta: the hypothesis' goal is not the goal with redexes contracted"
           (rcs--beta-licences-ok? "lambda-beta" acc (rcs--asms concl)
                                   (map rcs--goal (cdr hyps))))))))

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
     (let* ((gamma  (rcs--asms concl))
            (gamma* (rcs--asms (car hyps)))
            (obs    (map rcs--goal (cdr hyps))))
       (let outer ((fs gamma))
         (cond
           ((null? fs)
            "lambda-beta-hyp: no assumption of the conclusion is replaced by its contraction")
           (#t
            (let ((rest (rcs--drop (car fs) gamma)))
              (let inner ((cs gamma*))
                (cond
                  ((null? cs) (outer (cdr fs)))
                  ((not (chk-set=? gamma* (cons (car cs) rest))) (inner (cdr cs)))
                  (#t
                   (let ((acc (rcs--beta-match (car fs) (car cs) '() '())))
                     (if acc
                         (rcs--beta-licences-ok? "lambda-beta-hyp" acc gamma obs)
                         (inner (cdr cs)))))))))))))))

;;; -----------------------------------------------------------------------
;;; Registration

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
