;;; vnb-panel-check.el --- drive the real Focus panel and check what it paints
;;;
;;; Run it:
;;;
;;;     emacs --batch -l emacs/vnb-panel-check.el
;;;
;;; It starts a real prover (the band, so ~0.3 s), begins a real proof, and
;;; inspects the panel Emacs actually painted.  Prints
;;;
;;;     === PANEL CHECK: N passed, M failed ===
;;;
;;; and exits non-zero if anything failed.  Takes about half a minute.
;;;
;;; WHY IT EXISTS.  On 2026-09-13 the panel repeated its Keys block ~17 times
;;; on the first `start proof' of a session, and no amount of source reading
;;; found it: `vnb-launch--paint-proof' opens with `erase-buffer', every call
;;; site binds the buffer, and five paints in a row leave exactly one copy.
;;; Every piece was correct alone.  The defect was only reachable through the
;;; whole pipeline -- painter, hover decorator, prover round trip, process
;;; filter -- where the painter re-entered itself and blew
;;; `max-lisp-eval-depth', killing the filter so the panel read "(no proof in
;;; progress)".  A check that drives the pipeline finds that in one run; a
;;; check that calls the painter in isolation certifies it clean forever.
;;;
;;; CONTROL, run before believing it (2026-09-13): against the pre-fix
;;; vnb-launch.el this harness reported 35 Keys blocks, and with the process
;;; filter dying it does not reach the summary at all --
;;;
;;;     error in process filter: Lisp nesting exceeds 'max-lisp-eval-depth'
;;;     emacs exit 255, no "=== PANEL CHECK" line
;;;
;;; so the rule is the suite's: exit status alone means nothing, LOOK FOR THE
;;; SUMMARY LINE.

(defvar vpc--passed 0)
(defvar vpc--failed 0)

(defun vpc-check (name ok &optional detail)
  (if ok
      (setq vpc--passed (1+ vpc--passed))
    (setq vpc--failed (1+ vpc--failed))
    (message "FAIL: %s%s" name (if detail (format "  -- %s" detail) "")))
  ok)

(defun vpc--pump (n)
  (dotimes (_ n) (accept-process-output nil 0.2))
  (dotimes (_ 10) (sit-for 0.2)))

(defun vpc--count (needle)
  (save-excursion
    (goto-char (point-min))
    (let ((n 0))
      (while (search-forward needle nil t) (setq n (1+ n)))
      n)))

(defun vpc--widest ()
  (save-excursion
    (goto-char (point-min))
    (let ((w 0))
      (while (not (eobp))
        (setq w (max w (- (line-end-position) (line-beginning-position))))
        (forward-line 1))
      w)))

(load (expand-file-name "vnb-launch.el"
                        (file-name-directory load-file-name))
      nil t)

(vnb-launch--ensure-prover)
(vnb-launch--show-proof-workspace)
(vnb-launch--send
 "(sp (make-wff-from-string \"forall([x in nn], x in nn)\"))")
(vpc--pump 40)

(with-current-buffer vnb-proof-buffer-name
  ;; THE REGRESSION.  One panel per paint.  The count was 35 in this very
  ;; harness before the re-entrancy guard went in.
  (vpc-check "exactly one Keys block in the panel"
             (= 1 (vpc--count "goal:        d direct-inf"))
             (format "found %d" (vpc--count "goal:        d direct-inf")))
  (vpc-check "exactly one panel title"
             (= 1 (vpc--count "VNB Focus Workspace")))
  ;; The filter died silently before, and THIS is what the user saw.
  (vpc-check "the panel shows the goal, not \"(no proof in progress)\""
             (and (vpc--count "forall([x in nn]")
                  (= 0 (vpc--count "(no proof in progress)"))))
  (vpc-check "the open-goal count is painted"
             (> (vpc--count "1 open goal") 0))
  ;; Every advertised key must be bound, or the block lies.
  (vpc-check "every key the panel advertises is bound"
             (let ((bad '()))
               (dolist (k (split-string
                           "d = + u a A D e m M t F i w b B p y Y f o q n I h r S T W g"))
                 (unless (commandp (lookup-key vnb-proof-mode-map k))
                   (push k bad)))
               (or (null bad) (progn (message "   unbound: %S" bad) nil))))
  ;; An 80-column terminal frame must not wrap the panel.
  (vpc-check "no panel line exceeds 79 columns"
             (< (vpc--widest) 80)
             (format "widest is %d" (vpc--widest))))

;; The hover table is fetched OUT of the paint now; check the feature still
;; arrives rather than being quietly switched off by the fix.
(vpc-check "hover table fetched" (hash-table-p vnb-hover--table))
(with-current-buffer vnb-proof-buffer-name
  (vpc-check "the sequent is hover-decorated"
             (let ((hits 0) (pos (point-min)))
               (while (setq pos (next-single-property-change pos 'help-echo))
                 (when (get-text-property pos 'help-echo) (setq hits (1+ hits))))
               (> hits 0))))

;; And the proof still runs: di, then ass.
(vnb-launch--send "(di)")  (vpc--pump 20)
(vnb-launch--send "(ass)") (vpc--pump 20)
(with-current-buffer vnb-proof-buffer-name
  (vpc-check "di then ass closes the goal"
             (> (vpc--count "Proof complete.") 0)))


;; ----- the deduction-graph display mode (the user, 2026-10-03) -----
;; After di + ass the proof is complete: every node is GROUNDED, the root is [0].
(vnb-graph-browse)
(vpc--pump 5)
(with-current-buffer vnb-graph-buffer-name
  (vpc-check "graph mode: the buffer is in vnb-graph-mode and holds nodes"
             (and (derived-mode-p 'vnb-graph-mode) (> (length vnb-graph--nodes) 1))
             (format "%d node(s)" (length vnb-graph--nodes)))
  (vpc-check "graph mode: the node is painted Focus-style (Assumptions / rule / Turnstile)"
             (and (= 1 (vpc--count "Assumptions:")) (= 1 (vpc--count "Turnstile: "))))
  (vnb-graph-goto 0)
  (vpc-check "graph mode: C-c g 0 shows the root"
             (= 0 (car (aref vnb-graph--nodes vnb-graph--index))))
  ;; `format-mode-line' is empty under --batch (no window), so the status text
  ;; the mode line carries is tested at its source.
  (vpc-check "graph mode: the status reads [GROUNDED] by RULE from [N]"
             (let ((st (vnb-graph--status-string (aref vnb-graph--nodes vnb-graph--index))))
               (and (string-match-p "\\[GROUNDED\\] by [a-z-]+ from \\[[0-9]+\\]" st) t))
             (vnb-graph--status-string (aref vnb-graph--nodes vnb-graph--index)))
  (vpc-check "graph mode: the hypothesis number under the sequent is a button"
             (save-excursion (goto-char (point-min))
                             (and (search-forward "Justified by" nil t)
                                  (next-button (point)) t)))
  (vnb-graph-next)
  (vpc-check "graph mode: C-c n moves to the next node" (= vnb-graph--index 1))
  (vnb-graph-prev)
  (vpc-check "graph mode: C-c p moves back" (= vnb-graph--index 0))
  (vpc-check "graph mode: the advertised keys are bound"
             (cl-every (lambda (k) (commandp (lookup-key vnb-graph-mode-map (kbd k))))
                       '("C-c n" "C-c p" "C-c g" "n" "p" "g" "r" "l")))
  (vpc-check "graph mode: the toolbar has the arrows and go-to"
             (and (assq 'vnb-gtb-prev (cdr tool-bar-map))
                  (assq 'vnb-gtb-next (cdr tool-bar-map))
                  (assq 'vnb-gtb-goto (cdr tool-bar-map)))))

;; ----- the toolbar's Save Script button -----
;; It was gated on `vnb-pf--proof-live-p', which goes nil at `qed' -- so the
;; button greyed itself out at the exact moment a user reaches for Save, while
;; `W' (ungated) worked.  Read the :enable form out of the real toolbar keymap
;; and evaluate it, rather than testing a stand-in predicate.
(defun vpc--toolbar-entry (item)
  "The raw (SYMBOL menu-item NAME COMMAND . PLIST) cell for toolbar ITEM.
Read from the keymap alist, not via `lookup-key\=', which resolves the
menu-item down to the bare command and drops the :enable form -- and it is
the :enable form that is on trial here."
  (assq item (cdr vnb-launch--toolbar-map)))

(defun vpc--toolbar-enabled-p (item)
  (let* ((entry (vpc--toolbar-entry item))
         (form  (and entry (plist-get (nthcdr 4 entry) :enable))))
    (if form (eval form t) 'no-enable-form)))

(vnb-launch--install-toolbar)
(vpc-check "the Save Script toolbar item exists"
           (eq (nth 3 (vpc--toolbar-entry 'vnb-tb-save-script))
               'vnb-pf-save-proof-script))
(vpc-check "Save Script is enabled with the proof COMPLETE"
           (eq t (and (vpc--toolbar-enabled-p 'vnb-tb-save-script) t))
           "greyed out after qed -- but the script outlives the proof")

(message "=== PANEL CHECK: %d passed, %d failed ===" vpc--passed vpc--failed)
(kill-emacs (if (> vpc--failed 0) 1 0))
