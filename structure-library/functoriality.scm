;;; functoriality.scm -- every view-as is a FUNCTOR, and here is the proof.
;;;
;;; def-functor (structures.scm) gives the OBJECT action: a functoid
;;;   (V r) = (LIST (c1 r) ... (cn r))
;;; selecting and renaming the source's slots, plus the typing axiom
;;;   IS-SRC(r) => IS-TGT(V r).
;;; With IS-HOM-X now generated for every species, the MORPHISM action is
;;; available too, and it is the identity on the underlying map: a view neither
;;; touches the carrier nor builds new elements, so the very same f that is an
;;; X-hom a -> b is a Y-hom V(a) -> V(b).  That is FUNCTORIALITY, and it is a
;;; theorem, not a definition:
;;;
;;;   V-functorial :  IS-HOM-SRC(a,b,f)  =>  IS-HOM-TGT(V a, V b, f)
;;;
;;; It is PROVED, per view, by the driver below -- no new asserted facts.  The
;;; proof is the same three moves every time, which is the point: unfold the
;;; target hom, rewrite each target accessor of (V a) to the source accessor of
;;; a (the view's own defining equations), and every conjunct is then literally
;;; a conjunct of the hypothesis.  The two IS-TGT conjuncts come from the view's
;;; typing axiom.
;;;
;;; WHEN IT IS FREE, AND WHEN IT IS NOT.  The rewriting above works only if each
;;; carrier of the TARGET corresponds to an INDEPENDENT carrier of the source --
;;; then the target's hom map IS the source's.  FIELD-MULTIPLICATIVE-GROUP maps
;;; the target group's CARR to FIELD's NON-ZERO, which is a DERIVED carrier: a
;;; field hom is typed f in FUN(carr a, carr b), and that it restricts to
;;; f in FUN(non-zero a, non-zero b) is a THEOREM (a field hom kills nothing:
;;; f(x)f(x^-1) = 1), not a conjunct we already have.  Such a view owes a typing
;;; lemma before it is a functor, and this file says so instead of asserting it.

;;; --- the carriers of a structure, independent ones only -------------------
(define (fnc--independent-carriers name)
  (let ((sd (find-shape-structure name)))
    (and sd
         (map car (filter (lambda (s) (eq? (cadr s) 'carrier))
                          (structure-def-slots sd))))))

(define (fnc--all-slots name)
  (let ((sd (find-shape-structure name))) (and sd (structure-slot-names sd))))

;;; The source accessor that the view sends to target slot TGT-SLOT.
(define (fnc--source-of vd tgt-slot)
  (let loop ((ts (view-as-target-comps vd)) (ss (view-as-source-comps vd)))
    (cond ((null? ts) #f)
          ((eq? (car ts) tgt-slot) (car ss))
          (else (loop (cdr ts) (cdr ss))))))

;;; A view is FREE (functoriality follows with no new theorem) iff
;;;   -- every carrier of the target comes from an INDEPENDENT carrier of the
;;;      source (so the target's map IS the source's), and
;;;   -- neither species OVERRIDES its morphisms (declare-hom!).  An overridden
;;;      hom is not preservation-of-slots, so the syntactic argument -- "each of
;;;      the target's conjuncts IS one of the source's" -- does not apply, and
;;;      functoriality becomes a theorem with content (an isometry is continuous).
(define (fnc--free? vd)
  (let ((src (view-as-source-struct vd))
        (tgt (view-as-target-struct vd)))
    (and (not (hom-overridden? src))
         (not (hom-overridden? tgt))
         (let ((src-carr (fnc--independent-carriers src))
               (tgt-carr (fnc--independent-carriers tgt)))
           (and src-carr tgt-carr
                (let loop ((cs tgt-carr))
                  (cond ((null? cs) #t)
                        ((memq (fnc--source-of vd (car cs)) src-carr) (loop (cdr cs)))
                        (else #f))))))))

;;; di that STAYS QUIET when the focus goal cannot be decomposed.  The peel/split
;;; drivers below call `di' speculatively -- after the connectives are gone the
;;; goal is a bare IS-HOM-TGT(...) atom, and plain `(di)' would warn
;;; "direct-inference: cannot decompose" on every such no-op.  A di that cannot
;;; fire is already a no-op; this just drops the warning.  (Not `quietly', which
;;; would also swallow a genuine guard error -- this only suppresses the one
;;; benign not-applicable case, by applying the rule directly and skipping the
;;; warn wrapper.)
;;; A quiet `di'.  It drives the SURFACE tactic, not `pi-direct-inference!'
;;; directly: only the surface goes through `vnb--run!', and only `vnb--run!'
;;; records the step.  Until 2026-09-06 this called the primitive, so the ~6
;;; peeling `di's at the head of every functoriality proof were absent from the
;;; script -- all 14 `*-functorial' scripts then replayed their first `mac-h'
;;; against the unpeeled goal and died at step 1.
(define (fnc--di-quiet)
  (quietly (lambda () (di))))

;;; An IS-HOM-Z(...) atom that still has a definition to unfold.  A REFINEMENT's
;;; hom is IS-Z(a) and IS-Z(b) and IS-HOM-PARENT(a,b,f) -- so unfolding once
;;; leaves one of these behind, on whichever side it appears.
(define (fnc--hom-atom? e)
  (and (pair? e)
       (symbol? (car e))
       (let ((s (symbol->string (car e))))
         (and (> (string-length s) 7)
              (string=? (substring s 0 7) "is-hom-")))
       (hash-table-ref/default *theorem-table* (symbol-append (car e) '-def) #f)
       #t))

;;; --- normalizing a goal that mentions (TGT-SLOT (V a)) --------------------
;;; Rewrite every target accessor of a viewed structure to the SOURCE accessor
;;; of the structure itself:  carr(V a) --> carr(a),  opr(V a) --> add(a), ...
;;; Three moves, IN THIS ORDER:
;;;   1. accessor -> NTH        (the accessor macetes)
;;;   2. unfold the view        ((V a) -> the LIST of source components)
;;;   3. NTH-reduce             (project the LIST)
;;; The order matters.  Unfolding the view FIRST would leave the source
;;; accessors exposed inside the LIST, and step 1 would then rewrite THOSE too.
;;;
;;; It also explains why the (TGT-SLOT (V a)) = (SRC-SLOT a) equations are not
;;; proved as standalone lemmas: an accessor macete rewrites EVERY occurrence,
;;; so it turns the equation's own right-hand side into NTH form as well, and
;;; the two sides no longer match (VNB's `=' is partial, so `rfl' will not close
;;; nth(1,r) = nth(1,r) for an untyped r either).  Normalizing IN PLACE, where
;;; the accessor-of-a-view is the only occurrence, has neither problem.
(define (fnc--normalize-goal! vd)
  (let ((vname (view-as-name vd)))
    ;; `slot', not `mac': an accessor reduction goes through ONE door, so that
    ;; making it structure-relative later is a change to that door and not to
    ;; every caller (interactive.scm; accessor-callsite-audit is the pin).
    (for-each (lambda (acc) (quietly (lambda () (slot acc))))
              (view-as-target-comps vd))
    (quietly (lambda () (mac vname)))
    (let loop ((n 0))
      (when (< n 20) (quietly (lambda () (nth-r))) (loop (+ n 1))))))

;;; --- functoriality --------------------------------------------------------
;;; IS-HOM-SRC(a,b,f...) => IS-HOM-TGT(V a, V b, f...), with the SAME maps: the
;;; target's j-th carrier comes from the source's, so it rides the source's map.
(define (fnc--hom-maps name)
  (let ((k (length (fnc--independent-carriers name))))
    (if (= k 1)
        '(f)
        (map (lambda (i) (symbol-append 'f (string->symbol (number->string i))))
             (iota k 1)))))

(define (fnc--target-maps vd)
  ;; for each TARGET carrier, the source map that carries it
  (let* ((src       (view-as-source-struct vd))
         (src-carr  (fnc--independent-carriers src))
         (src-maps  (fnc--hom-maps src))
         (tgt-carr  (fnc--independent-carriers (view-as-target-struct vd))))
    (map (lambda (c)
           (let ((s (fnc--source-of vd c)))
             (let loop ((cs src-carr) (ms src-maps))
               (cond ((null? cs) (error "functoriality: target carrier not from a source carrier" c))
                     ((eq? s (car cs)) (car ms))
                     (else (loop (cdr cs) (cdr ms)))))))
         tgt-carr)))

(define (fnc--functoriality-statement vd)
  (let* ((vname    (view-as-name vd))
         (src      (view-as-source-struct vd))
         (tgt      (view-as-target-struct vd))
         (hom-src  (symbol-append 'IS-HOM- src))
         (hom-tgt  (symbol-append 'IS-HOM- tgt))
         (fs       (fnc--hom-maps src))
         (gs       (fnc--target-maps vd))
         (body     `(IMPLIES (,hom-src a b ,@fs)
                             (,hom-tgt (,vname a) (,vname b) ,@gs))))
    (make-wff
      `(FORALL a (FORALL b ,(let loop ((vs fs))
                              (if (null? vs)
                                  body
                                  `(FORALL ,(car vs) ,(loop (cdr vs))))))))))

;;; Close one leaf.  It is either
;;;   -- an IS-TGT(V x) conjunct: the view's typing axiom gives it from IS-SRC(x),
;;;      which the unfolded hom hypothesis put in the context.  This one must be
;;;      discharged BEFORE the view is unfolded, or IS-TGT's argument is no
;;;      longer (V x) but a raw tuple and the typing axiom no longer matches; or
;;;   -- one of the preservation conjuncts: normalize it (accessor-of-view ->
;;;      source accessor) and it is LITERALLY an assumption.
;;; The structure named by an (IS-Z t) goal, or #f.
(define (fnc--isx-structure head)
  (let ((s (symbol->string head)))
    (and (> (string-length s) 3)
         (string=? (substring s 0 3) "is-")
         (not (fnc--hom-atom? (list head 'x)))
         (let ((nm (string->symbol (substring s 3 (string-length s)))))
           (and (find-shape-structure nm) nm)))))

;;; TGT's ancestors, nearest first: the subtype theorems `<child>-is-<parent>'
;;; that carry IS-TGT(t) up to IS-ANCESTOR(t).  A refinement TARGET needs them:
;;; unfolding IS-HOM-INTEGRAL-DOMAIN leaves IS-RING(V a) as a leaf, while the
;;; view's typing axiom gives only IS-INTEGRAL-DOMAIN(V a).
(define (fnc--ancestor-steps from to)
  (let loop ((cur from) (acc '()))
    (cond
      ((eq? cur to) (reverse acc))
      (else
       (let ((dsd (lookup-definitional-structure cur)))
         (and dsd
              (let ((parent (definitional-structure-parent dsd)))
                (loop parent
                      (cons (symbol-append cur '-is- parent) acc)))))))))

(define (fnc--close-leaf! vd leaf)
  (let* ((vname  (view-as-name vd))
         (tgt    (view-as-target-struct vd))
         (typing (symbol-append vname '-is- tgt)))
    (dk-focus! leaf)
    (let* ((g    (wff-formula (sequent-node-assertion leaf)))
           (head (and (pair? g) (symbol? (car g)) (car g)))
           (zed  (and head (fnc--isx-structure head)))
           ;; (IS-Z (V x)) -- a typing conjunct, for the target or an ancestor
           (viewed-arg (and zed (pair? (cdr g)) (pair? (cadr g))
                            (eq? (car (cadr g)) vname)
                            (cadr (cadr g)))))
      (if viewed-arg
          (quietly
            (lambda ()
              (fact typing viewed-arg)               ; IS-TGT(V x)
              ;; ... and up the subtype chain to IS-Z(V x) if Z is an ancestor
              (for-each (lambda (step) (fact step (list vname viewed-arg)))
                        (or (fnc--ancestor-steps tgt zed) '()))
              (ass)))
          (begin (fnc--normalize-goal! vd)
                 (quietly (lambda () (ass))))))
    (not (memq leaf (proof-leaves)))))

(define (fnc--prove-functoriality! vd)
  (let* ((vname   (view-as-name vd))
         (src     (view-as-source-struct vd))
         (hom-src (symbol-append 'IS-HOM- src))
         (hom-tgt (symbol-append 'IS-HOM- (view-as-target-struct vd)))
         (nm      (symbol-append vname '-functorial)))
    (sp (fnc--functoriality-statement vd))
    ;; peel the universals, assume the source hom
    (let peel ((n (+ 2 (length (fnc--hom-maps src)))))
      (unless (= n 0) (fnc--di-quiet) (peel (- n 1))))
    (fnc--di-quiet)
    ;; The hypothesis, conjunct by conjunct.  mac-h REPLACES the assumption, so
    ;; take what it LANDED -- never reconstruct the formula and hope it matches.
    ;; A REFINEMENT's hom is IS-X(a) and IS-X(b) and IS-HOM-PARENT(a,b,f), so one
    ;; unfold leaves an IS-HOM-PARENT ATOM: unfold to a FIXPOINT, or the
    ;; preservation laws never reach the context.
    (let ((landed (dk-landed
                    (lambda ()
                      (quietly
                        (lambda ()
                          (mac-h (symbol-append hom-src '-def)
                                 (cons hom-src
                                       (cons 'a (cons 'b (fnc--hom-maps src)))))))))))
      (quietly (lambda () (dk-split! (car landed)))))
    (let unfold ((guard 0))
      (let ((h (find-first fnc--hom-atom? (dk-asms))))
        (when (and h (< guard 8))
          (let ((new (quietly
                       (lambda ()
                         (dk-landed*
                           (lambda ()
                             (mac-h (symbol-append (car h) '-def) h)))))))
            (for-each (lambda (w) (quietly (lambda () (dk-split! w)))) new))
          (unfold (+ guard 1)))))
    ;; Unfold the goal's hom and split it into conjuncts.  `di' splits the FOCUS,
    ;; and splitting an AND leaves the right-nested rest on the OTHER leaf -- so
    ;; sweep the LEAVES, not the focus.  A refinement TARGET needs the same
    ;; fixpoint as the hypothesis: its hom hides an IS-HOM-PARENT atom.
    (quietly (lambda () (mac (symbol-append hom-tgt '-def))))
    (let split ((guard 0))
      (let* ((leaves (proof-leaves))
             (conj   (find-first
                       (lambda (n)
                         (let ((g (wff-formula (sequent-node-assertion n))))
                           (and (pair? g) (eq? (car g) 'AND))))
                       leaves))
             (hom    (and (not conj)
                          (find-first
                            (lambda (n)
                              (fnc--hom-atom?
                                (wff-formula (sequent-node-assertion n))))
                            leaves))))
        (when (and (or conj hom) (< guard 60))
          (dk-focus! (or conj hom))
          (quietly
            (lambda ()
              (if conj
                  (fnc--di-quiet)
                  (mac (symbol-append
                         (car (wff-formula (sequent-node-assertion hom))) '-def)))))
          (split (+ guard 1)))))
    (let ((ok (let loop ((leaves (proof-leaves)) (all #t))
                (if (null? leaves)
                    all
                    (let ((this (fnc--close-leaf! vd (car leaves))))
                      (loop (cdr leaves) (and all this)))))))
      (if (and ok (proof-done? *ps*))
          (begin (qed nm) #t)
          (begin (display ";; functoriality: NOT proved for ") (display vname)
                 (newline)
                 #f)))))

;;; --- the sweep ------------------------------------------------------------
(define (prove-functoriality!)
  (let ((free '()) (owed '()) (failed '()))
    (for-each
      (lambda (vname)
        (let ((vd (lookup-view-as vname)))
          (cond
            ((not (fnc--free? vd)) (set! owed (cons vname owed)))
            (else
             (if (fnc--prove-functoriality! vd)
                 (set! free (cons vname free))
                 (set! failed (cons vname failed)))))))
      (sort (hash-table-keys *view-as-table*)
            (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
    (display ";; functoriality: ") (display (length free))
    (display " view(s) PROVED functorial")
    (when (pair? failed)
      (display ", ") (display (length failed)) (display " failed: ")
      (display (reverse failed)))
    (when (pair? owed)
      (display ";\n;;   ") (display (length owed))
      (display " view(s) owe a typing lemma first (a TARGET carrier comes from a")
      (display " DERIVED source carrier, so the source hom's map is not typed for it): ")
      (display (reverse owed)))
    (newline)
    (list (reverse free) (reverse failed) (reverse owed))))

(prove-functoriality!)
