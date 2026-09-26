;;; subset-lemmas.scm -- the four inclusion facts, PROVEN.
;;;
;;;   subset-mem-fwd          A subset B, x in A  =>  x in B
;;;   subset-mem              the same statement under a second name (see below)
;;;   subset-trans            A subset B subset C  =>  A subset C
;;;   subclass-of-set-is-set  A subset B, B a set  =>  A a set
;;;
;;; All four were ASSERTED, and none of them had any business being so:
;;;
;;;   subset-mem-fwd  structure-library/compactness.scm:194, warrant `well-known',
;;;                   comment "Forward direction of subset-def (definitional)"
;;;   subset-mem      theorem-library/hahn-banach-full-proof.scm:99, `well-known'
;;;   subset-trans    theorem-library/hahn-banach-full-proof.scm:106, `well-known',
;;;                   comment "Inclusion is transitive (subset-def chase)"
;;;   subclass-of-...  structure-library/set-basics.scm:14, warrant `proof', whose
;;;                   text is the derivation in full and ends "Stated rather than
;;;                   derived only because the SEP-then-extensionality step is
;;;                   pure bookkeeping"
;;;
;;; The first three are three tactic steps each off `subset-def' (library.scm:252,
;;; a base-library axiom).  The fourth is the derivation its own warrant describes:
;;; class-extensionality (library.scm:270) identifies A with {z in B : z in A},
;;; which separation makes a set.
;;;
;;; WHY THEY SAT THERE.  Not difficulty -- LOAD ORDER.  `sp' and `qed' do not
;;; exist until `interactive' (load.scm:388), and set-basics loads at 70 and
;;; compactness at 165.  A statement needed that early could be asserted where it
;;; was needed or not exist at all.  Nothing forced the STATEMENT to live there
;;; too: this file loads at the first moment proving is possible and before every
;;; one of the twelve call sites (earliest: theorem-library/diagonalization, 495).
;;;
;;; They are not idle.  subset-mem-fwd alone is in the bill of `diagonalization`
;;; and `totally-bounded-has-cauchy-subsequence`; subclass-of-set-is-set is one of
;;; the three leaves of `ord-no-injection-into-set`.

;;; -----------------------------------------------------------------------
;;; (1) subset-mem-fwd -- the forward direction of subset-def.
;;; Antecedents CURRIED, not conjoined, so `fact' can detach them one at a time
;;; against the live context (the convention structure-library/ideal.scm:73 sets
;;; out); every one of the call sites relies on that.

(sp (make-wff '(FORALL A (FORALL B (FORALL x
                 (IMPLIES (SUBSET A B) (IMPLIES (IN x A) (IN x B))))))))
(di) (di) (di)
(inst*! (dk-landed-1 (lambda () (mac-h 'subset-def '(SUBSET A B)))) 'x)
(ass)
(qed 'subset-mem-fwd)
(topic! 'subset-mem-fwd 'plumbing)

;;; -----------------------------------------------------------------------
;;; (2) subset-mem -- REMOVED 2026-09-20 (batch 11, proven-duplicate-audit).
;;; It was the SAME statement as (1) under a second name, introduced
;;; independently by hahn-banach-full-proof.  Its three call sites now cite
;;; `subset-mem-fwd', which is proven above and loads at the same moment.

;;; -----------------------------------------------------------------------
;;; (3) subset-trans -- chase an element through both inclusions.

(sp (make-wff '(FORALL a (FORALL b (FORALL c
                 (IMPLIES (SUBSET a b) (IMPLIES (SUBSET b c) (SUBSET a c))))))))
(di) (di) (di)
(mac 'subset-def)
(di)                                    ; a GUARDED forall peels binder + guard
(fact 'subset-mem-fwd 'a 'b 'x)
(fact 'subset-mem-fwd 'b 'c 'x)
(ass)
(qed 'subset-trans)
(topic! 'subset-trans 'plumbing)

;;; -----------------------------------------------------------------------
;;; (4) subclass-of-set-is-set -- A is included in the set B, so A has exactly
;;; the members of {z in B : z in A}; class-extensionality makes that an EQUALITY
;;; of classes, and separation makes the right-hand side a set.

(define sl-sep '(SEP z_ B (IN z_ A)))

(sp (make-wff '(FORALL A (FORALL B
                 (IMPLIES (IN B SET) (IMPLIES (SUBSET A B) (IN A SET)))))))
(di) (di) (di)

;; the separated copy is a set -- that is exactly what separation says
(have! `(IN ,sl-sep SET) (lambda () (sep-set) (ass)))

;; ... and it has the same members as A
(have! `(FORALL x (IFF (IN x A) (IN x ,sl-sep)))
  (lambda ()
    (di)                                ; introduce x; goal is the IFF
    ;; `di' on an IFF opens BOTH directions with each one's hypothesis already
    ;; in context, so the leaf goals are bare memberships -- no second `di'.
    (for-each
      (lambda (leaf)
        (dk-focus! leaf)
        (let ((target (caddr (dk-goal))))          ; the class x must land in
          (if (and (pair? target) (eq? (car target) 'SEP))
              ;; x in A  =>  x in {z in B : z in A}: in B by inclusion, in A by hypothesis
              (in-sep! (lambda () (fact 'subset-mem-fwd 'A 'B 'x) (ass))
                       (lambda () (ass)))
              ;; x in {z in B : z in A}  =>  x in A: sep-me hands back both halves
              (begin (sep-me `(IN x ,sl-sep)) (ass)))))
      (dk-opened (lambda () (di))))))

;; so they are the same class, and A inherits its sethood
(fact 'class-extensionality 'A sl-sep)
(subst `(= A ,sl-sep))
(ass)
(qed 'subclass-of-set-is-set)
(topic! 'subclass-of-set-is-set 'plumbing)
