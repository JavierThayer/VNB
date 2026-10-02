;;; c-continuous-category.scm -- THE CATEGORY OF COUNTABLY-METRISED SPACES AND
;;; CONTINUOUS MAPS: objects the C-METRIC-SPACEs, arrows the maps f : PTS(a) ->
;;; PTS(b) continuous for the canonical metrics C-METRIC(a), C-METRIC(b).
;;;
;;; The user's request (2026-10-02).  The mechanism is `declare-category!'
;;; (structures.scm); the model is theorem-library/categories.scm, whose generic
;;; drivers (membership, sethood, the Hom functors) are copied here under the
;;; prefix `ccm-' (each theorem-library file loads in its own environment).
;;;
;;; THE TECHNIQUE.  The arrow body is IS-CONTINUOUS(C-METRIC a, C-METRIC b, f),
;;; and IS-CONTINUOUS carries IS-METRIC-SPACE of both ends and the FUN typing over
;;; PTS(C-METRIC .).  So an arrow of this category IS an arrow of the CONTINUOUS
;;; category (categories.scm) between the canonical metric spaces, and the
;;; composition law is `hom-continuous-compose' pulled back along C-METRIC: open
;;; both arrows, re-close them as IS-CONTINUOUS-ARROW, cite, and re-type the
;;; composite over PTS(a), PTS(c) by `compose-type'.  No eps-delta chase.
;;;
;;; THE IDENTITY LAW IN TWO STEPS.  The obligation
;;; IS-C-METRIC-SPACE(a) => IS-C-CONTINUOUS-ARROW(a, a, id)  has
;;; IS-CONTINUOUS(C-METRIC a, C-METRIC a, id) in its conclusion, and the first
;;; conjunct of IS-CONTINUOUS is IS-METRIC-SPACE(C-METRIC a).  The identity law
;;; is first proven GIVEN that fact,
;;;   hom-c-continuous-id-of-metric:
;;;     IS-C-METRIC-SPACE(a) => IS-METRIC-SPACE(C-METRIC a)
;;;       => IS-C-CONTINUOUS-ARROW(a, a, ID-FUN(PTS a)),
;;; and the obligation `hom-c-continuous-id' (at the end of the file) discharges
;;; the hypothesis by `c-metric-is-metric-space'
;;; (theorem-library/c-metric-is-metric.scm).
;;;
;;; Theorems:
;;;   c-metric-canonical-carrier     PTS(C-METRIC s) == PTS(s)
;;;   hom-c-continuous-member-iff    the hom-set's membership (generic)
;;;   hom-c-continuous-in-set        the hom-set is a set
;;;   hom-c-continuous-compose       arrows compose (via hom-continuous-compose)
;;;   hom-c-continuous-id-of-metric  the identity law, given the metric lemma
;;;   hom-c-continuous-id            the identity law (the obligation)
;;;   hom-c-continuous-post-type     Hom(a, -) on hom-sets
;;;   hom-c-continuous-pre-type      Hom(-, b) on hom-sets
;;;
;;; Cites: c-metric-carrier (theorem-library/c-metric-summable.scm);
;;; c-metric-is-metric-space (theorem-library/c-metric-is-metric.scm);
;;; hom-continuous-compose, hom-continuous-id (theorem-library/categories.scm);
;;; compose-type, fun-set-iff and the SEP rules (early).  Load after all three files.
;;; Nothing is asserted; every qed is expected modulo 0.  Prefix `ccm-'.

(declare-category! 'C-CONTINUOUS 'C-METRIC-SPACE '(a b f)
  '(IS-CONTINUOUS (C-METRIC a) (C-METRIC b) f))

(notation! 'IS-C-CONTINUOUS-ARROW 'kind 'predicate 'arity 3
           'english "$3 is a continuous map of countably-metrised spaces from $1 to $2")
(notation! 'HOM-C-CONTINUOUS 'kind 'functoid 'arity 2
           'english "the continuous maps of countably-metrised spaces from $1 to $2")

;;; =======================================================================
;;; Helpers (copied from categories.scm, prefix cat- -> ccm-).
;;; =======================================================================

(define ccm-cat 'C-CONTINUOUS)
(define (ccm-ctx f who)
  (or (dk-ctx-form f) (error "c-continuous-category: not in context --" who (expression->string f))))
(define (ccm-done! name)
  (if (proof-done? *ps*) (qed name) (error "c-continuous-category: failed to prove" name)))
(define (ccm-inst thm . terms)
  (let loop ((f (lookup-theorem thm)) (ts terms))
    (if (null? ts) f
        (loop (subst-free (quantifier-var f) (car ts) (quantifier-body f)) (cdr ts)))))
(define (ccm-conjuncts f)
  (if (dk-head-is? f 'AND)
      (append (ccm-conjuncts (cadr f)) (ccm-conjuncts (caddr f)))
      (list f)))
(define (ccm-and fs)
  (if (null? (cdr fs)) (car fs) (list 'AND (car fs) (ccm-and (cdr fs)))))

(define (ccm-arrow cat) (category-arrow-name cat))
(define (ccm-arrow-def cat) (category-arrow-def-name cat))
(define (ccm-hs cat) (category-hom-set-name cat))
(define (ccm-thm cat suffix) (symbol-append 'hom- cat suffix))
(define (ccm-x cat) (category-structure cat))
(define (ccm-isx cat) (symbol-append 'IS- (ccm-x cat)))
(define (ccm-carrier cat) (car (category--carriers (ccm-x cat))))

;;; the slot typings of IS-X(v), landed on a lane
(define (ccm-land-typings! x v)
  (let* ((isx  (symbol-append 'IS- x))
         (accs (map car (structure-def-slots (lookup-structure x))))
         (ts   (filter (lambda (c) (and (dk-head-is? c 'IN) (pair? (cadr c)) (= (length (cadr c)) 2)
                                        (memq (car (cadr c)) accs) (equal? (cadr (cadr c)) v)
                                        (not (dk-asm? c))))
                       (ccm-conjuncts (caddr (ccm-inst isx v))))))
    (if (pair? ts)
        (let ((conj (ccm-and ts)))
          (dk-have! conj
            (lambda ()
              (mac-h isx (ccm-ctx (list isx v) "IS-X"))
              (dk-split-all!)
              (dk-conj-close!)))
          (if (pair? (cdr ts)) (dk-split-all! (list (ccm-ctx conj "typings"))))))))

(define (ccm-open-arrow! cat hyp)
  (mac-h (ccm-arrow-def cat) hyp)
  (dk-split-all!))

;;; =======================================================================
;;; The carrier of the canonical instance.
;;; =======================================================================

(sp (make-wff '(FORALL s (== (PTS (C-METRIC s)) (PTS s)))))
(dk-peel!)
(mac 'C-METRIC)
(let* ((gl (dk-goal)) (cw (cadr (cadr gl))) (vs (cadr cw)) (w (caddr cw)))
  (dk-cite! 'c-metric-carrier vs w)
  (ass))
(ccm-done! 'c-metric-canonical-carrier)

;;; =======================================================================
;;; Membership and sethood (generic).
;;; =======================================================================

(define (ccm-prove-member-iff! cat)
  (sp (make-wff (category-member-iff cat)))
  (dk-peel!)
  (mac (ccm-hs cat))
  (for-each
    (lambda (lf)
      (dk-focus! lf)
      (if (dk-head-is? (dk-goal) 'AND)
          (begin
            (sep-me (dk-pick (lambda (x) (and (dk-head-is? x 'IN) (dk-head-is? (caddr x) 'SEP)))
                             "the SEP membership"))
            (dk-conj-close!))
          (begin
            (dk-split-all!)
            (in-sep! (lambda () (ass)) (lambda () (ass))))))
    (dk-opened (lambda () (di))))
  (ccm-done! (ccm-thm cat '-member-iff)))

(define (ccm-prove-in-set! cat)
  (sp (category-obligation (ccm-thm cat '-in-set)))
  (dk-peel!)
  (let* ((hs (cadr (dk-goal))) (va (cadr hs)) (vb (caddr hs)))
    (ccm-land-typings! (ccm-x cat) va)
    (ccm-land-typings! (ccm-x cat) vb)
    (mac (ccm-hs cat))
    (sep-set)
    (mac 'fun-set-iff)
    (dk-conj-close!)
    (ccm-done! (ccm-thm cat '-in-set))))

(ccm-prove-member-iff! ccm-cat)
(ccm-prove-in-set! ccm-cat)

;;; =======================================================================
;;; Composition: hom-continuous-compose pulled back along C-METRIC.
;;; =======================================================================

;;; From IS-CONTINUOUS(s, t, h) in context land IS-METRIC-SPACE(s),
;;; IS-METRIC-SPACE(t), h in FUN(PTS s, PTS t) (on a lane, so the hypothesis
;;; survives), then IS-CONTINUOUS-ARROW(s, t, h).  Returns the arrow.
(define (ccm-continuous-arrow! s t h)
  (let* ((hyp  (ccm-ctx (list 'IS-CONTINUOUS s t h) "IS-CONTINUOUS"))
         (ty   (list 'AND (list 'IS-METRIC-SPACE s)
                 (list 'AND (list 'IS-METRIC-SPACE t)
                            (list 'IN h (list 'FUN (list 'PTS s) (list 'PTS t))))))
         (arr  (list 'IS-CONTINUOUS-ARROW s t h)))
    (dk-have! ty
      (lambda ()
        (mac-h 'is-continuous hyp)
        (dk-split-all!)
        (dk-conj-close!)))
    (dk-split-all! (list (ccm-ctx ty "the continuity typings")))
    (dk-have! arr
      (lambda ()
        (mac 'is-continuous-arrow-def)
        (dk-conj-close!)))
    (ccm-ctx arr "the CONTINUOUS arrow")))

(sp (category-obligation 'hom-c-continuous-compose))
(dk-peel!)
(let* ((arrow (ccm-arrow ccm-cat))
       (gl (dk-goal)) (va (cadr gl)) (vc (caddr gl)) (gf (cadddr gl))
       (vg (cadr gf)) (vf (caddr gf))
       (hf (dk-pick (lambda (x) (and (dk-head-is? x arrow) (equal? (cadddr x) vf))) "the f arrow"))
       (vb (caddr hf))
       (hg (ccm-ctx (list arrow vb vc vg) "the g arrow"))
       (ma (list 'C-METRIC va)) (mb (list 'C-METRIC vb)) (mc (list 'C-METRIC vc))
       (pa (list 'PTS va)) (pb (list 'PTS vb)) (pc (list 'PTS vc)))
  (ccm-open-arrow! ccm-cat hf)
  (ccm-open-arrow! ccm-cat hg)
  (ccm-land-typings! 'C-METRIC-SPACE va)
  (ccm-continuous-arrow! ma mb vf)
  (ccm-continuous-arrow! mb mc vg)
  (let* ((res (dk-cite! 'hom-continuous-compose ma mb mc vf vg))
         (cgf (list 'IS-CONTINUOUS ma mc gf)))
    (dk-have! cgf
      (lambda ()
        (mac-h 'is-continuous-arrow-def (ccm-ctx res "the composite CONTINUOUS arrow"))
        (dk-split-all!)
        (ass)))
    (dk-have! (list 'AND (list 'IN vf (list 'FUN pa pb)) (list 'IN vg (list 'FUN pb pc))))
    (dk-cite! 'compose-type pa pb pc vg vf)
    (mac (ccm-arrow-def ccm-cat))
    (dk-conj-close!)))
(ccm-done! 'hom-c-continuous-compose)

;;; =======================================================================
;;; The identity, GIVEN that the canonical metric is a metric space.
;;; =======================================================================

(sp (make-wff '(FORALL a (IMPLIES (IS-C-METRIC-SPACE a)
                 (IMPLIES (IS-METRIC-SPACE (C-METRIC a))
                   (IS-C-CONTINUOUS-ARROW a a (ID-FUN (PTS a))))))))
(dk-peel!)
(let* ((gl (dk-goal)) (va (cadr gl))
       (ma (list 'C-METRIC va)) (pa (list 'PTS va)) (pm (list 'PTS ma))
       (arr (dk-cite! 'hom-continuous-id ma)))
  (dk-cite! 'c-metric-canonical-carrier va)
  (ccm-open-arrow! 'CONTINUOUS arr)
  (mac (ccm-arrow-def ccm-cat))
  (dk-conj-close!
    (lambda ()
      (if (dk-asm? (dk-goal))
          (ass)
          (begin
            (subst (list '= pa pm))
            (ass))))))
(ccm-done! 'hom-c-continuous-id-of-metric)

;;; =======================================================================
;;; The Hom functors (categories.scm's driver, copied).
;;; =======================================================================

(define (ccm-post h s) (list 'VNB-LAMBDA 'hmpf_ s (list 'COMPOSE h 'hmpf_)))
(define (ccm-pre k s)  (list 'VNB-LAMBDA 'hmpf_ s (list 'COMPOSE 'hmpf_ k)))

(define (ccm-open-member! cat f x y)
  (mac-h (ccm-thm cat '-member-iff) (ccm-ctx (list 'IN f (list (ccm-hs cat) x y)) "membership"))
  (dk-split-all!))

(define (ccm-object! cat v arrow-hyp)
  (if (not (dk-asm? (list (ccm-isx cat) v)))
      (dk-have! (list (ccm-isx cat) v)
        (lambda ()
          (mac-h (ccm-arrow-def cat) (ccm-ctx arrow-hyp "the arrow"))
          (dk-split-all!)
          (ass)))))

(define (ccm-carrier-set! cat v)
  (let ((goal (list 'IN (list (ccm-carrier cat) v) 'SET)))
    (if (not (dk-asm? goal))
        (dk-have! goal
          (lambda ()
            (mac-h (ccm-isx cat) (ccm-ctx (list (ccm-isx cat) v) "IS-X"))
            (dk-split-all!)
            (ass))))))

(define (ccm-close-composite! cat x y z outer inner)
  (let* ((c (ccm-carrier cat))
         (cx (list c x)) (cy (list c y)) (cz (list c z)))
    (dk-cite! (ccm-thm cat '-compose) x y z inner outer)
    (dk-have! (list 'AND (list 'IN inner (list 'FUN cx cy)) (list 'IN outer (list 'FUN cy cz))))
    (dk-cite! 'compose-type cx cy cz outer inner)
    (mac (ccm-thm cat '-member-iff))
    (dk-conj-close!)))

(define (ccm-prove-post-type! cat)
  (let ((hs (ccm-hs cat)) (arrow (ccm-arrow cat)))
    (sp (make-wff `(FORALL a (FORALL b (FORALL c (FORALL h
           (IMPLIES (,(ccm-isx cat) a) (IMPLIES (IN h (,hs b c))
             (IN ,(ccm-post 'h (list hs 'a 'b)) (FUN (,hs a b) (,hs a c)))))))))))
    (dk-peel!)
    (let* ((gl (dk-goal)) (lam (cadr gl)) (dom (caddr lam)) (va (cadr dom)) (vb (caddr dom))
           (vh (cadr (cadddr lam))) (vc (caddr (caddr (caddr gl)))))
      (ccm-open-member! cat vh vb vc)
      (ccm-object! cat vb (list arrow vb vc vh))
      (ccm-carrier-set! cat va)
      (dk-cite! (ccm-thm cat '-in-set) va vb)
      (dk-lam-type!
        (lambda ()
          (let* ((landed (dk-peel!)) (vf (cadr (car landed))))
            (ccm-open-member! cat vf va vb)
            (ccm-close-composite! cat va vb vc vh vf)))
        (lambda () (ass)))
      (ccm-done! (ccm-thm cat '-post-type)))))

(define (ccm-prove-pre-type! cat)
  (let ((hs (ccm-hs cat)) (arrow (ccm-arrow cat)))
    (sp (make-wff `(FORALL a (FORALL b (FORALL c (FORALL k
           (IMPLIES (,(ccm-isx cat) b) (IMPLIES (IN k (,hs c a))
             (IN ,(ccm-pre 'k (list hs 'a 'b)) (FUN (,hs a b) (,hs c b)))))))))))
    (dk-peel!)
    (let* ((gl (dk-goal)) (lam (cadr gl)) (dom (caddr lam)) (va (cadr dom)) (vb (caddr dom))
           (vk (caddr (cadddr lam))) (vc (cadr (caddr (caddr gl)))))
      (ccm-open-member! cat vk vc va)
      (ccm-object! cat va (list arrow vc va vk))
      (ccm-object! cat vc (list arrow vc va vk))
      (ccm-carrier-set! cat vc)
      (dk-cite! (ccm-thm cat '-in-set) va vb)
      (dk-lam-type!
        (lambda ()
          (let* ((landed (dk-peel!)) (vf (cadr (car landed))))
            (ccm-open-member! cat vf va vb)
            (ccm-close-composite! cat vc va vb vf vk)))
        (lambda () (ass)))
      (ccm-done! (ccm-thm cat '-pre-type)))))

(ccm-prove-post-type! ccm-cat)
(ccm-prove-pre-type! ccm-cat)

;;; =======================================================================
;;; The identity law: the canonical metric IS a metric space
;;; (c-metric-is-metric-space), so the hypothesis of
;;; hom-c-continuous-id-of-metric is discharged.
;;; =======================================================================

(sp (category-obligation 'hom-c-continuous-id))
(dk-peel!)
(let ((va (cadr (dk-goal))))
  (dk-cite! 'c-metric-is-metric-space va)
  (dk-cite! 'hom-c-continuous-id-of-metric va)
  (ass))
(ccm-done! 'hom-c-continuous-id)
