;;; meta-def-laws.scm -- K2 PHASE 5: the definedness rules of structure-library/meta-def.scm against the
;;; core (docs/meta-k2-admissibility-2026-10-08.md, section 4.7; report scratchpad/triage/META-5-REPORT.md).
;;; Agent META-5, 2026-10-12.  Every theorem here is (qed ...); helper procedures are local (prefix md-).
;;; (1) the two named hypotheses of phase 4 (meta-ind.scm section 4) from the schemas they are instances of;
;;; (2) strictness of = on the left, DERIVED over the core (eq-subst);
;;; (3) the application rule DEF-APP, DERIVED from fun-domain-apply-def and the strictness of IN.
;;; Agent META-6, 2026-10-13 (the user's decision of that day): (2') strictness of = on the RIGHT, DERIVED
;;; with the other orientation of eq-subst (adm-def-strict-eq-r); (4) the five schemas admitted into the core
;;; (CR-DEF-*): their admissibility, the ADM-X predicates for every T, the two phase-4 hypotheses for every
;;; T, and the four admissibility theorems that carried those hypotheses restated without them (-core).
;;; Load window: after theorem-library/meta-ind-laws.scm and structure-library/meta-def.scm;
;;; scratchpad/meta3/driver-kit-meta3.scm (dk-meta-derive!) before it.  Library: meta.

(define (md+ g . fs) (fold-left (lambda (g f) `(CTX-ADD ,g ,f)) g fs))
(define (md-der g f) `(IN (LIST ,g ,f) (DERIVABLE tt)))
;; finish a lane whose goal the last step landed (detach! lands it on a new node and moves there)
(define (md-close!) (if (and (pair? (dk-open-leaves)) (dk-asm? (dk-goal))) (ass)))
;; the derivability hypothesis in context whose sequent has the formula head HEAD
(define (md-der-hyp head)
  (find-first (lambda (f) (and (dk-head-is? f 'IN) (dk-head-is? (caddr f) 'DERIVABLE) (dk-head-is? (cadr f) 'LIST)
                               (dk-head-is? (caddr (cadr f)) head)))
              (dk-asms)))
;; a relation DEF-X(tt, hs, c) closed: its SEQ-SET conjunct in context, the witnesses WS
(define (md-rel-close! rel hs c ws)
  (dk-have! `(,rel tt ,hs ,c)
    (lambda () (mac rel) (dk-conj-close! (lambda () (if (dk-asm? (dk-goal)) (ass) (dk-meta-ex-fill! ws)))))))

;;; -----------------------------------------------------------------------
;;; 1. The named hypotheses of phase 4 are instances of the two schemas.

;; strictness of IN (DEF-STRICT-IN-L) gives DEF-IN-CLOSED
(sp (make-wff '(FORALL tt (IMPLIES (ADM-DEF-STRICT-IN-L tt) (DEF-IN-CLOSED tt)))))
(dk-peel!)
(let ((iff (dk-meta-iff! 'def-in-closed 'tt))
      (adm (dk-meta-iff-r! (dk-meta-iff! 'adm-def-strict-in-l 'tt))))
  (dk-have! (caddr iff)
    (lambda ()
      (dk-peel!)
      (let* ((goal (dk-goal)) (c (cadr goal)) (g (cadr c)) (w (cadr (caddr c)))
             (hyp (md-der-hyp 'ENC-IN)) (h (cadr hyp)) (a (caddr (caddr h))) (hs `(LIST ,h)))
        (dk-cite! 'der-in-seq 'tt h)
        (dk-split! (dk-meta-iff-r! (dk-meta-iff! 'seq-iff g `(ENC-IN ,w ,a))))
        (dk-split! (dk-cite! 'clf-in-elim w a))
        (dk-cite! 'clf-eq-intro w w)
        (dk-meta-seq! g `(ENC-EQ ,w ,w))
        (md-rel-close! 'DEF-STRICT-IN-L hs c (list g w a))
        (dk-have! `(HYPS-IN ,hs (DERIVABLE tt)) (lambda () (fact 'hyps-in-1 h '(DERIVABLE tt)) (ass)))
        (dk-apply! adm hs c)
        (md-close!))))
  (dk-meta-iff-l! iff)
  (md-close!))
(qed 'def-in-closed-from-strict)

;; the comprehension schema (DEF-COMP) gives DEF-COMP-CLOSED
(sp (make-wff '(FORALL tt (IMPLIES (ADM-DEF-COMP tt) (DEF-COMP-CLOSED tt)))))
(dk-peel!)
(let ((iff (dk-meta-iff! 'def-comp-closed 'tt))
      (adm (dk-meta-iff-r! (dk-meta-iff! 'adm-def-comp 'tt))))
  (dk-have! (caddr iff)
    (lambda ()
      (dk-peel!)
      (let* ((goal (dk-goal)) (c (cadr goal)) (g (cadr c)) (cq (cadr (caddr c))) (q (cadr cq)) (hs '(LIST)))
        (dk-cite! 'clf-eq-intro cq cq)
        (dk-meta-seq! g `(ENC-EQ ,cq ,cq))
        (md-rel-close! 'DEF-COMP hs c (list g q))
        (dk-have! `(HYPS-IN ,hs (DERIVABLE tt)) (lambda () (fact 'hyps-in-0 '(DERIVABLE tt)) (ass)))
        (dk-apply! adm hs c)
        (md-close!))))
  (dk-meta-iff-l! iff)
  (md-close!))
(qed 'def-comp-closed-from-schema)

;;; -----------------------------------------------------------------------
;;; 2. Strictness of = on the left is DERIVED over the core: from [g, s = u], the cut of s = u and, in the
;;; context g + (s = u), eq-subst on p = (s = z) for a name z fresh for s:  p[z := u] = (s = u) is an
;;; assumption, p[z := s] = (s = s).  (The right side, [g, u = u], is not reached this way: CR-EQ-SUBST
;;; rewrites t into s only.  Since 2026-10-13 the core has the other orientation too, CR-EQ-SUBST-SYM, and
;;; the right side is derived below, adm-def-strict-eq-r.)

;; the components of an encoded equation sentence are closed terms
(sp (make-wff '(FORALL x (FORALL y (IMPLIES (IN (ENC-EQ x y) CLF) (AND (IN x CLT) (IN y CLT)))))))
(dk-peel!)
(dk-cite! 'enc-eq-unfold 'x 'y)
(dk-rewrite-h! '(IN (ENC-EQ x y) CLF) '(ENC-EQ x y) '(EAPP 8 (LIST x y)))
(dk-have! '(IN 8 NN) (lambda () (arith)))
(dk-have! '(<= 7 8) (lambda () (arith)))
(dk-have! '(<= 8 9) (lambda () (arith)))
(dk-split-all! (list (dk-meta-iff-r! (dk-meta-iff! 'clf-iff '(EAPP 8 (LIST x y))))))
(dk-split! (dk-cite! 'eapp-expr-inv 8 '(LIST x y)))
(te '(IN (LIST x y) (TUPLES EXPR-SET)) 1)
(te '(IN (LIST x y) (TUPLES EXPR-SET)) 2)
(dk-meta-iff-r! (dk-meta-iff! 'clf-rel2 8 'x 'y))
(ass)
(qed 'clf-eq-elim)

;; Unpack DEF-X(tt, hs, c): return the witnesses; c and hs rewritten away; each hypothesis sequent's
;; derivability and SEQ-SET membership land (meta-ind-laws.scm's mi-rel-open!, for one or two premises).
(define (md-rel-open! rel n)
  (let* ((r (dk-meta-iff-r! (dk-meta-iff! rel 'tt 'hs 'c)))
         (parts (dk-split! r))
         (vs (dk-meta-unpack! (find-first (lambda (f) (dk-head-is? f 'FORSOME)) parts)))
         (ceq (dk-meta-eq-of 'c)) (heq (dk-meta-eq-of 'hs)))
    (subst ceq)
    (dk-rewrite-h! '(IN c SEQ-SET) 'c (caddr ceq))
    (if (> n 0)
        (let* ((lst (caddr heq))
               (h2 (dk-rewrite-h! '(HYPS-IN hs (DERIVABLE tt)) 'hs lst))
               (ss (cdr lst)))
          (dk-have! `(= ,lst ,lst) (lambda () (rfl)))
          (case n
            ((1) (dk-cite! 'hyps-in-1-elim (car ss) '(DERIVABLE tt)))
            ((2) (dk-split! (dk-cite! 'hyps-in-2-elim (car ss) (cadr ss) '(DERIVABLE tt)))))
          (for-each (lambda (s) (dk-cite! 'der-in-seq 'tt s)) ss)))
    vs))

;; z not free in e, from the freshness of z for g and e (fresh-name-exists)
(define (md-not-fv! z g e)
  (let ((u `(UNION (CTX-FV ,g) (EXPR-FV ,e))))
    (dk-have! `(NOT (IN ,z (EXPR-FV ,e)))
      (lambda ()
        (di)
        (let ((iff (dk-meta-iff! 'union-membership `(CTX-FV ,g) `(EXPR-FV ,e) z)))
          (dk-have! (caddr iff) (lambda () (oi-r) (ass)))
          (dk-meta-iff-l! iff)
          (ai `(NOT (IN ,z ,u))))))))

(sp (make-wff '(FORALL tt (FORALL hs (FORALL c (IMPLIES (DEF-STRICT-EQ-L tt hs c)
   (IMPLIES (HYPS-IN hs (DERIVABLE tt)) (IN c (DERIVABLE tt)))))))))
(dk-peel!)
(let* ((vs (md-rel-open! 'def-strict-eq-l 1)) (g (car vs)) (s (cadr vs)) (u (caddr vs))
       (e `(ENC-EQ ,s ,u)) (ss `(ENC-EQ ,s ,s)) (g1 (md+ g e)))
  (dk-split! (dk-meta-iff-r! (dk-meta-iff! 'seq-iff g e)))
  (dk-split! (dk-cite! 'clf-eq-elim s u))
  (dk-split-all! (list (dk-meta-iff-r! (dk-meta-iff! 'clt-iff s))))
  (dk-split-all! (list (dk-meta-iff-r! (dk-meta-iff! 'clt-iff u))))
  (dk-cite! 'clf-eq-intro s s)
  (let* ((z (dk-skolem! (dk-cite! 'fresh-name-exists g s) #t))
         (p `(EAPP 8 (LIST ,s (EFVAR ,z)))) (ps `(EXPR-SUBST ,p ,z ,s)) (pu `(EXPR-SUBST ,p ,z ,u)))
    (md-not-fv! z g s)
    (dk-have! '(IN 8 NN) (lambda () (arith)))
    (fact 'efvar-in-expr z)
    (dk-have! `(IN (LIST ,s (EFVAR ,z)) (TUPLES EXPR-SET)) (lambda () (dk-close-all! (lambda () (ti)))))
    (fact 'eapp-in-expr 8 `(LIST ,s (EFVAR ,z)))
    (let ((eqs (dk-cite! 'subst-hole-r z s s 8)) (equ (dk-cite! 'subst-hole-r z u s 8))
          (fs (dk-cite! 'enc-eq-unfold s s)) (fu (dk-cite! 'enc-eq-unfold s u)))
      (dk-have! `(IN ,ps CLF) (lambda () (subst eqs) (subst `(= ,(caddr fs) ,ss)) (ass)))
      (dk-have! `(IN ,pu CLF) (lambda () (subst equ) (subst `(= ,(caddr fu) ,e)) (ass)))
      (dk-meta-set-of! e 'CLF)
      (dk-have! `(OR (IN ,e ,g1) (IN (ENC-QEQ ,s ,u) ,g1)) (lambda () (oi-l) (dk-cite! 'ctx-add-has g e) (ass)))
      (dk-meta-derive! 'tt `(assumption (,g1 ==> ,e)))
      (dk-have! (md-der g1 pu) (lambda () (subst equ) (subst `(= ,(caddr fu) ,e)) (ass)))
      (dk-meta-derive! 'tt `(eq-subst (,g1 ==> ,ps) (given (,g1 ==> ,pu))))
      (dk-have! (md-der g1 ss) (lambda () (subst `(= ,ss ,(caddr fs))) (subst `(= ,(caddr fs) ,ps)) (ass)))
      (dk-meta-derive! 'tt `(cut (,g ==> ,ss) (given (,g ==> ,e)) (given (,g1 ==> ,ss))))
      (md-close!))))
(qed 'adm-def-strict-eq-l)

;;; Strictness of = on the RIGHT, DERIVED over the core with the other orientation of eq-subst (META-6,
;;; 2026-10-13; CR-EQ-SUBST-SYM, meta-core.scm 4.2): from [g, s = u], the cut of s = u and, in the context
;;; g + (s = u), eq-subst-sym on p = (z = u) for a name z fresh for u, licensed by the context equation
;;; s = u read as "t = s" with t := s, s := u:  p[z := s] = (s = u) is an assumption, p[z := u] = (u = u).
(sp (make-wff '(FORALL tt (FORALL hs (FORALL c (IMPLIES (DEF-STRICT-EQ-R tt hs c)
   (IMPLIES (HYPS-IN hs (DERIVABLE tt)) (IN c (DERIVABLE tt)))))))))
(dk-peel!)
(let* ((vs (md-rel-open! 'def-strict-eq-r 1)) (g (car vs)) (s (cadr vs)) (u (caddr vs))
       (e `(ENC-EQ ,s ,u)) (uu `(ENC-EQ ,u ,u)) (g1 (md+ g e)))
  (dk-split! (dk-meta-iff-r! (dk-meta-iff! 'seq-iff g e)))
  (dk-split! (dk-cite! 'clf-eq-elim s u))
  (dk-split-all! (list (dk-meta-iff-r! (dk-meta-iff! 'clt-iff s))))
  (dk-split-all! (list (dk-meta-iff-r! (dk-meta-iff! 'clt-iff u))))
  (dk-cite! 'clf-eq-intro u u)
  (let* ((z (dk-skolem! (dk-cite! 'fresh-name-exists g u) #t))
         (p `(EAPP 8 (LIST (EFVAR ,z) ,u))) (ps `(EXPR-SUBST ,p ,z ,s)) (pu `(EXPR-SUBST ,p ,z ,u)))
    (md-not-fv! z g u)
    (dk-have! '(IN 8 NN) (lambda () (arith)))
    (fact 'efvar-in-expr z)
    (dk-have! `(IN (LIST (EFVAR ,z) ,u) (TUPLES EXPR-SET)) (lambda () (dk-close-all! (lambda () (ti)))))
    (fact 'eapp-in-expr 8 `(LIST (EFVAR ,z) ,u))
    (let ((eqs (dk-cite! 'subst-hole-l z s u 8)) (equ (dk-cite! 'subst-hole-l z u u 8))
          (fs (dk-cite! 'enc-eq-unfold s u)) (fu (dk-cite! 'enc-eq-unfold u u)))
      (dk-have! `(IN ,ps CLF) (lambda () (subst eqs) (subst `(= ,(caddr fs) ,e)) (ass)))
      (dk-have! `(IN ,pu CLF) (lambda () (subst equ) (subst `(= ,(caddr fu) ,uu)) (ass)))
      (dk-meta-set-of! e 'CLF)
      (dk-have! `(OR (IN ,e ,g1) (IN (ENC-QEQ ,s ,u) ,g1)) (lambda () (oi-l) (dk-cite! 'ctx-add-has g e) (ass)))
      (dk-meta-derive! 'tt `(assumption (,g1 ==> ,e)))
      (dk-have! (md-der g1 ps) (lambda () (subst eqs) (subst `(= ,(caddr fs) ,e)) (ass)))
      (dk-meta-derive! 'tt `(eq-subst-sym (,g1 ==> ,pu) (given (,g1 ==> ,ps))))
      (dk-have! (md-der g1 uu) (lambda () (subst `(= ,uu ,(caddr fu))) (subst `(= ,(caddr fu) ,pu)) (ass)))
      (dk-meta-derive! 'tt `(cut (,g ==> ,uu) (given (,g ==> ,e)) (given (,g1 ==> ,uu))))
      (md-close!))))
(qed 'adm-def-strict-eq-r)

;;; -----------------------------------------------------------------------
;;; 4. THE SCHEMAS ADMITTED INTO THE CORE (the user's decision, 2026-10-13; agent META-6).
;;; DEF-STRICT-IN-L, DEF-STRICT-IN-R, DEF-TOTAL, DEF-BINDER, DEF-COMP and DEF-LIST are core relations now
;;; (CR-DEF-*, structure-library/meta-core.scm 4.7, each with its claim).  Each DEF-X(T, hs, c) is the
;;; conjunction of c in SEQ-SET with the body of CR-DEF-X, written alike, so its admissibility is one
;;; unfolding, one alpha-equivalent assumption and the closure law of CR-DEF-X.

;; DEF-X(tt, hs, c) and the hypotheses derivable  =>  c derivable, through CR-X.
(define (md-admitted! rel cr name)
  (sp (make-wff `(FORALL tt (FORALL hs (FORALL c (IMPLIES (,rel tt hs c)
     (IMPLIES (HYPS-IN hs (DERIVABLE tt)) (IN c (DERIVABLE tt)))))))))
  (dk-peel!)
  (dk-split! (dk-meta-iff-r! (dk-meta-iff! rel 'tt 'hs 'c)))
  (dk-have! `(,cr tt hs c) (lambda () (mac cr) (ass)))
  (dk-cite! (dk-meta-law-name cr) 'tt 'hs 'c)
  (md-close!)
  (qed name))
(md-admitted! 'DEF-STRICT-IN-L 'CR-DEF-STRICT-IN-L 'def-strict-in-l-admitted)
(md-admitted! 'DEF-STRICT-IN-R 'CR-DEF-STRICT-IN-R 'def-strict-in-r-admitted)
(md-admitted! 'DEF-TOTAL 'CR-DEF-TOTAL 'def-total-admitted)
(md-admitted! 'DEF-BINDER 'CR-DEF-BINDER 'def-binder-admitted)
(md-admitted! 'DEF-COMP 'CR-DEF-COMP 'def-comp-admitted)
(md-admitted! 'DEF-LIST 'CR-DEF-LIST 'def-list-admitted)

;; The three ADM-X predicates of meta-def.scm section 3 hold for every T.
(define (md-adm-holds! adm law name)
  (sp (make-wff `(FORALL tt (,adm tt))))
  (di)
  (let* ((t (cadr (dk-goal))) (iff (dk-meta-iff! adm t)))
    (dk-have! (caddr iff)
      (lambda ()
        (dk-peel!)
        (let* ((c (cadr (dk-goal)))
               (hyp (find-first (lambda (f) (dk-head-is? f 'HYPS-IN)) (dk-asms))))
          (dk-cite! law t (cadr hyp) c)
          (md-close!))))
    (dk-meta-iff-l! iff)
    (md-close!))
  (qed name))
(md-adm-holds! 'ADM-DEF-STRICT-IN-L 'def-strict-in-l-admitted 'adm-def-strict-in-l-holds)
(md-adm-holds! 'ADM-DEF-STRICT-IN-R 'def-strict-in-r-admitted 'adm-def-strict-in-r-holds)
(md-adm-holds! 'ADM-DEF-COMP 'def-comp-admitted 'adm-def-comp-holds)

;; The two named hypotheses of phase 4 (meta-ind.scm section 4) hold for every T.
(sp (make-wff '(FORALL tt (DEF-IN-CLOSED tt))))
(di)
(let ((t (cadr (dk-goal))))
  (dk-cite! 'adm-def-strict-in-l-holds t)
  (dk-cite! 'def-in-closed-from-strict t)
  (md-close!))
(qed 'def-in-closed-holds)

(sp (make-wff '(FORALL tt (DEF-COMP-CLOSED tt))))
(di)
(let ((t (cadr (dk-goal))))
  (dk-cite! 'adm-def-comp-holds t)
  (dk-cite! 'def-comp-closed-from-schema t)
  (md-close!))
(qed 'def-comp-closed-holds)

;; The four phase-4 / phase-5 admissibility theorems that carried them, with the hypotheses discharged:
;; each induction is now admissible over the core and the encoded catalog axioms it names, nothing else.
(sp (make-wff '(FORALL tt (FORALL hs (FORALL c (IMPLIES (REL-BIG-UNION-MEM-INTRO tt hs c)
   (IMPLIES (HYPS-IN hs (DERIVABLE tt)) (IN c (DERIVABLE tt)))))))))
(dk-peel!)
(dk-cite! 'def-in-closed-holds 'tt)
(dk-cite! 'adm-big-union-mem-intro 'tt 'hs 'c)
(md-close!)
(qed 'adm-big-union-mem-intro-core)

(sp (make-wff '(FORALL tt (FORALL hs (FORALL c (IMPLIES (SUBSET tt CLF) (IMPLIES (IN AX-TFI tt) (IMPLIES (IN AX-MEM-SET tt)
   (IMPLIES (REL-TRANSFINITE-INDUCTION tt hs c) (IMPLIES (HYPS-IN hs (DERIVABLE tt)) (IN c (DERIVABLE tt))))))))))))
(dk-peel!)
(dk-cite! 'def-comp-closed-holds 'tt)
(dk-cite! 'adm-transfinite-induction 'tt 'hs 'c)
(md-close!)
(qed 'adm-transfinite-induction-core)

(sp (make-wff '(FORALL tt (FORALL hs (FORALL c (IMPLIES (SUBSET tt CLF) (IMPLIES (IN AX-NN-IND tt) (IMPLIES (IN AX-MEM-SET tt)
   (IMPLIES (IN AX-ZERO-NN tt) (IMPLIES (IN AX-SUCC-NN tt)
   (IMPLIES (REL-NN-INDUCTION tt hs c) (IMPLIES (HYPS-IN hs (DERIVABLE tt)) (IN c (DERIVABLE tt))))))))))))))
(dk-peel!)
(dk-cite! 'def-comp-closed-holds 'tt)
(dk-cite! 'def-in-closed-holds 'tt)
(dk-cite! 'adm-nn-induction 'tt 'hs 'c)
(md-close!)
(qed 'adm-nn-induction-core)

(sp (make-wff '(FORALL tt (FORALL hs (FORALL c (IMPLIES (SUBSET tt CLF) (IMPLIES (IN AX-TFI tt) (IMPLIES (IN AX-MEM-SET tt)
   (IMPLIES (IN AX-LIMIT-IFF tt) (IMPLIES (IN AX-ORD-SUCC-ABOVE tt)
   (IMPLIES (REL-TFI-3CASES tt hs c) (IMPLIES (HYPS-IN hs (DERIVABLE tt)) (IN c (DERIVABLE tt))))))))))))))
(dk-peel!)
(dk-cite! 'def-comp-closed-holds 'tt)
(dk-cite! 'adm-tfi-3cases 'tt 'hs 'c)
(md-close!)
(qed 'adm-tfi-3cases-core)
