;;; vnb-commands.lisp -- machine-readable VNB command registry
;;;
;;; Format: (command-name arg-list "description")
;;;
;;; arg-list symbols:
;;;   wff      -- a <wff> object, built with (make-wff-from-string "...")
;;;   formula  -- a raw S-expression or string (auto-parsed); e.g. '(IN x NN)
;;;   term     -- a raw term S-expression or string
;;;   name     -- a Scheme symbol naming a theorem, macete, or proof
;;;   k        -- a positive integer index (1-based)
;;;   n        -- a positive integer (1-based goal number)
;;;   instance -- a symbol naming a concrete structure instance
;;;   struct   -- a symbol naming a structure type (e.g. 'RING)
;;;   is-thm   -- a symbol naming the IS-STRUCT theorem for the instance
;;;
;;; Emacs Lisp usage:
;;;   (with-temp-buffer
;;;     (insert-file-contents "/path/to/vnb-commands.lisp")
;;;     (setq vnb-command-list (read (current-buffer))))
;;; Then completing-read over (mapcar #'car vnb-command-list).

(

;;; ------------------------------------------------------------------
;;; Proof lifecycle

(sp      (wff)
         "Start proof. Argument must be a <wff>; use (make-wff-from-string \"...\") to construct it. Resets the proof script recorder.")

(focus   (n)
         "Switch focus to the n-th open goal (1-based). Does not record an inference; just changes which subgoal subsequent commands act on.")

(qed     (name)
         "Close the current proof and install the proved formula as theorem NAME. Also saves the proof script under NAME. Errors if any goals remain open.")

;;; ------------------------------------------------------------------
;;; Zero-argument proof commands (act on the focus goal)

(di      ()
         "Direct inference. Decomposes the top-level connective of the goal: AND splits into conjuncts; IMPLIES moves antecedent to context; FORALL introduces a fresh variable; IFF splits into two directions.")

(pbc     ()
         "Proof by contradiction. Adds NOT(goal) to the context and changes the goal to FALSITY.")

(ass     ()
         "Assumption. Closes the goal if it is alpha-equivalent to a formula already in the context.")

(arith   ()
         "Arithmetic decision. Closes a ground arithmetic goal over NN/ZZ/QQ/RR/CC. Handles +, -, *, recip, abs, conjugate, succ, power, <=, =, IN.")

(rs      ()
         "Ring simplify. Closes a ring-identity goal (= e1 e2) by reducing both sides to polynomial normal form over the free associative ZZ-algebra. Works on bare equality goals and on universally quantified ring goals without prior (di).")

(rfl     ()
         "Reflexivity. Closes a goal of the form (= a a) when a is demonstrably defined.")

(qrfl    ()
         "Quasi-reflexivity. Closes a goal of the form (== a a) unconditionally (a may be undefined).")

(oi-l    ()
         "Or-intro left. Reduces a disjunctive goal (p OR q) to p.")

(oi-r    ()
         "Or-intro right. Reduces a disjunctive goal (p OR q) to q.")

(ci      ()
         "Cartesian intro. Proves a goal of the form [a1,...,an] IN CARTESIAN(A1,...,An) by splitting into n membership subgoals ai IN Ai.")

(ti      ()
         "Tuples intro. Proves a goal of the form [a1,...,an] IN TUPLES(A) by splitting into n membership subgoals ai IN A.")

(ii      ()
         "Intersection intro. Proves x IN INTERSECTION(A,B,...) by splitting into one subgoal per set.")

(nth-r   ()
         "NTH reduce. Simplifies NTH(k, [e1,...,en]) to ek wherever it appears in the goal. Requires k to be a literal integer.")

(beta    ()
         "Beta reduction. Reduces (lambda([x1,...,xn], body))(v1,...,vn) to body[xi:=vi] in the goal.")

(tfi     ()
         "Transfinite induction. Fires on a goal of the form FORALL(alpha IN ORD, P(alpha)). Produces two subgoals: zero case P(0) and limit/successor cases.")

(tfi3    ()
         "Transfinite induction (3-case). Like tfi but splits into three subgoals: zero, successor, and limit ordinal cases separately.")

(ni      ()
         "NN induction. Fires on a goal of the form FORALL(n IN NN, P(n)). Produces two subgoals: base case P(0) and step case FORALL(n IN NN, P(n) IMPLIES P(succ(n))).")

(bu-set  ()
         "Big-union sethood. Fires on a goal of the form (IN (BIG-UNION z A body) SET). Produces two subgoals: A IN SET, and FORALL(z IN A, body IN SET).")

;;; ------------------------------------------------------------------
;;; One-argument proof commands

(ai      (formula)
         "Antecedent inference. Splits an IMPLIES(formula, q) assumption from the context into two subgoals: prove formula, and (with formula in context) prove q. formula is a string or S-expression.")

(cut     (formula)
         "Cut (introduce lemma). Splits the current goal into two subgoals: (1) prove formula, (2) assuming formula, prove the original goal. formula is a string or S-expression.")

(ew      (term)
         "Exists-witness. Provides a witness for an existential goal FORSOME(x, P(x)), reducing it to P(term). term is a string or S-expression.")

(bc      (formula)
         "Backchain. Applies an implication formula (IMPLIES ante goal) from the context, reducing the current goal to ante. formula is a string or S-expression.")

(wk      (formula)
         "Weaken. Drops formula from the context. formula is a string or S-expression naming the assumption to remove.")

(ui      (k)
         "Union intro. Selects the k-th component for a goal of the form x IN UNION(A1,...,An), reducing it to x IN Ak. k is a 1-based integer.")

(ue      (formula)
         "Union elim. Eliminates a union membership assumption formula (of the form x IN UNION(A1,...,An)) from the context by case-splitting. formula is a string or S-expression.")

(bu-mi   (term)
         "Big-union mem-intro. Provides a witness for a goal of the form x IN BIG-UNION(z, A, body), reducing it to two subgoals: term IN A, and x IN body[z:=term]. term is a string or S-expression.")

(bu-me   (formula)
         "Big-union mem-elim. Eliminates a big-union membership assumption formula (of the form x IN BIG-UNION(z, A, body)) from the context by introducing a fresh eigenvariable e and adding e IN A and x IN body[z:=e] to context. formula is a string or S-expression.")

(ta      (name)
         "Theorem assumption. Adds the formula of theorem NAME to the context. NAME is a quoted symbol, e.g. 'ring-add-comm.")

(mac     (name)
         "Apply macete. Rewrites the goal using the macete named NAME. NAME is a quoted symbol. Macetes include accessor reductions, def-functoid rewrites, and user-defined rewrite rules.")

;;; ------------------------------------------------------------------
;;; Two-argument proof commands

(inst    (formula term)
         "Instantiate. Applies a universal formula FORALL(x, P(x)) from the context by substituting term for x, adding P(term) to context. formula is a string or S-expression; term is the instantiation value.")

(mac-h   (name formula)
         "Apply macete to a hypothesis -- the dual of mac. Unfolds a defined predicate (or applies any unconditional IFF/=/== equivalence macete) NAME inside the assumption FORMULA, replacing it by its body in place; pair with ai to split the result. For a CONDITIONAL equivalence, side-conditions not already in context are spawned as subgoals (the main line stays in focus). NAME is a quoted symbol; FORMULA is a string, S-expression, or 1-based assumption index.")

(ce      (formula k)
         "Cartesian elim. Extracts the k-th component from a context assumption formula of the form [a1,...,an] IN CARTESIAN(A1,...,An), adding ak IN Ak to context. k is a 1-based integer.")

(te      (formula k)
         "Tuples elim. Extracts the k-th component from a context assumption of the form [a1,...,an] IN TUPLES(A), adding ak IN A to context. k is a 1-based integer.")

(ie      (formula k)
         "Intersection elim. Extracts the k-th component from a context assumption of the form x IN INTERSECTION(A1,...,An), adding x IN Ak to context. k is a 1-based integer.")

;;; ------------------------------------------------------------------
;;; Theory / script management (not proof-state commands)

(save-proof   (name)
              "Save the current proof script under NAME. Called automatically by (qed name); call manually to checkpoint a script mid-proof.")

(replay-proof (name)
              "Replay the saved proof script named NAME on the current proof state. An optional second argument is an alist of substitutions applied to every command argument before replay: (replay-proof 'my-proof '((x . y) (a . b))).")

(spec    (instance struct is-thm)
         "Specialize structure. Given that IS-STRUCT(INSTANCE) is proved and installed as IS-THM, instantiate every generic theorem of the form FORALL(s, IS-STRUCT(s) IMPLIES P[s]) to P[INSTANCE]. Not a proof command -- operates on the theorem table. E.g. (spec 'CC-RING 'RING 'cc-is-ring).")

;;; ------------------------------------------------------------------
;;; Formula/expression builders (not proof commands)

(fa      (bindings body)
         "Build a FORALL formula. bindings is a list of binding specs: (x) for unrestricted, (in x A) or (x in A) for bounded. E.g. (fa '((in x NN) (y)) '(IN (+ x y) NN)).")

(fs      (bindings body)
         "Build a FORSOME formula. Same binding syntax as fa. E.g. (fs '((in x NN)) '(= (* x x) 4)).")

;;; ------------------------------------------------------------------
;;; Display / utilities

(show    ()
         "Display the current proof state (focus goal and open goals). Called automatically after every proof command.")

(pp      (wff)
         "Pretty-print a <wff> to the REPL. Uses the precedence-aware printer (infix for arithmetic, binding-list for quantifiers).")

(calc    (term)
         "Evaluate a ground arithmetic term and print the result. Accepts a string (\"2^10\") or a raw S-expression ('(POWER 2 10)).")

(make-wff-from-string (str)
                      "Parse a formula string into a validated <wff>. This is the standard way to construct a formula for (sp ...) or for passing to proof commands that take a wff argument.")

(parse-string (str)
              "Parse a formula string into a raw S-expression without validation. For use when constructing arguments to (ta), (bc), (inst), etc. directly.")

)
