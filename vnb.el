;;; vnb.el --- Emacs interface for the VNB proof checker
;;
;; Plain Elisp; no external package dependencies.
;; Compatible with GNU Emacs and XEmacs.
;;
;; DO NOT BYTE-COMPILE: GNU Emacs and XEmacs byte-code formats are
;; incompatible.  Load this file interpreted (via load or require) only.
;;
;; USAGE
;;   M-x vnb        start the prover; sets up REPL + proof-state windows
;;
;; WORKFLOW
;;   Type proof commands in the *VNB* REPL buffer.  Use the short forms
;;   from interactive.scm:
;;     (sp (make-wff '(IMPLIES A A)))   start a new proof
;;     (di)                  direct inference (decompose goal)
;;     (ai f)                antecedent inference (decompose assumption f)
;;     (ass)                 close goal by assumption
;;     (rfl)                 reflexivity: close (= a a)
;;     (qrfl)                quasi-reflexivity: close (== a a)
;;     (ta 'name)            add named theorem to context
;;     (mac 'name)           apply macete by name
;;     (inst f t)            instantiate (FORALL x ...) = f with term t
;;     (bc f)                backchain on implication f
;;     (cut f)               introduce lemma f
;;     (rs)                  ring simplify: close ring equality (auto-detect gens)
;;     (spec inst struct thm) transport generic ring/group/... theorems to instance
;;     (focus n)             switch focus to n-th open goal (1-based)
;;     (show)                redisplay proof state
;;
;; KEY BINDINGS (in *VNB* buffer)
;;   C-c C-s   send (show) to refresh the proof-state display
;;   C-c C-p   switch to *VNB State* buffer
;;
;; KEY BINDINGS (in *VNB State* buffer)
;;   q         switch back to *VNB* REPL buffer
;;
;; PROOF STATE DISPLAY
;;   The prover wraps (show) output in sentinel lines:
;;     ;;VNB-STATE-BEGIN
;;     ... proof state ...
;;     ;;VNB-STATE-END
;;   The preoutput filter strips the sentinel lines from the REPL and
;;   copies the state text into the *VNB State* buffer.  State content
;;   still appears in the REPL as well (without the sentinel lines).

(require 'comint)

;;; -----------------------------------------------------------------------
;;; Configuration

(defvar vnb-program (expand-file-name "~/prover/prover")
  "Path to the VNB prover executable.")

(defvar vnb-buffer-name "*VNB*"
  "Name of the VNB REPL (comint) buffer.")

(defvar vnb-state-buffer-name "*VNB State*"
  "Name of the read-only proof-state display buffer.")

;;; -----------------------------------------------------------------------
;;; Compatibility shims

(defun vnb--process-live-p (buf)
  "Return non-nil if BUF has a running comint process."
  (let ((proc (get-buffer-process buf)))
    (and proc (eq (process-status proc) 'run))))

;;; -----------------------------------------------------------------------
;;; Proof-state output filter
;;;
;;; We wrap the process filter directly rather than using
;;; comint-preoutput-filter-functions, which behaves differently between
;;; GNU Emacs and XEmacs.  vnb--preoutput-acc accumulates output across
;;; calls while waiting for a complete sentinel block.

(defvar vnb--preoutput-acc ""
  "Buffer-local accumulator for partial VNB state sentinel blocks.")

(defvar vnb--orig-filter nil
  "Buffer-local storage for the comint process filter we wrapped.")

(make-variable-buffer-local 'vnb--preoutput-acc)
(make-variable-buffer-local 'vnb--orig-filter)

(defun vnb--preoutput-filter (string)
  "Strip VNB sentinel lines; extract state content for the display buffer.
Handles sentinel blocks that arrive in multiple output chunks."
  (setq vnb--preoutput-acc (concat vnb--preoutput-acc string))
  (let ((result "")
        (continue t))
    (while continue
      (let* ((begin-pos (string-match ";;VNB-STATE-BEGIN\n" vnb--preoutput-acc))
             (begin-end (and begin-pos (match-end 0))))
        (cond
          ;; No BEGIN sentinel anywhere: flush everything to the REPL.
          ((not begin-pos)
           (setq result (concat result vnb--preoutput-acc))
           (setq vnb--preoutput-acc "")
           (setq continue nil))
          (t
           (let* ((end-pos (string-match ";;VNB-STATE-END\n?"
                                         vnb--preoutput-acc begin-end))
                  (end-end (and end-pos (match-end 0))))
             (cond
               ;; BEGIN found but END not yet arrived: emit pre-BEGIN text,
               ;; keep the rest buffered for the next filter call.
               ((not end-pos)
                (setq result (concat result
                                     (substring vnb--preoutput-acc 0 begin-pos)))
                (setq vnb--preoutput-acc
                      (substring vnb--preoutput-acc begin-pos))
                (setq continue nil))
               ;; Complete block: strip sentinel lines, display state.
               (t
                (let ((pre    (substring vnb--preoutput-acc 0 begin-pos))
                      (state  (substring vnb--preoutput-acc begin-end end-pos))
                      (after  (substring vnb--preoutput-acc end-end)))
                  (vnb--display-state state)
                  ;; Emit pre-sentinel text and state content to REPL;
                  ;; sentinel lines themselves are suppressed.
                  (setq result (concat result pre state))
                  (setq vnb--preoutput-acc after)))))))))
    result))

;;; Named process filter -- works identically in GNU Emacs and XEmacs.
;;; Runs vnb--preoutput-filter on the incoming string, then passes the
;;; result to whatever filter comint had installed before us.

(defun vnb--process-filter (process string)
  "VNB process filter: intercept state sentinels, then call original filter."
  (let* ((buf      (process-buffer process))
         (filtered (if buf
                       (with-current-buffer buf
                         (vnb--preoutput-filter string))
                     string))
         (orig     (and buf
                        (with-current-buffer buf vnb--orig-filter))))
    (if orig
        (funcall orig process filtered)
      (comint-output-filter process filtered))))

(defun vnb--install-process-filter ()
  "Wrap the process filter for the current VNB buffer.
Stores the existing filter in vnb--orig-filter and replaces it with
vnb--process-filter.  Safe to call multiple times."
  (let ((proc (get-buffer-process (current-buffer))))
    (when (and proc (not (eq (process-filter proc) 'vnb--process-filter)))
      (setq vnb--orig-filter (process-filter proc))
      (set-process-filter proc 'vnb--process-filter))))

;;; -----------------------------------------------------------------------
;;; Proof-state display buffer

(defun vnb--display-state (text)
  "Replace the contents of the VNB State buffer with TEXT."
  (let ((buf (get-buffer-create vnb-state-buffer-name)))
    (with-current-buffer buf
      (unless (eq major-mode 'vnb-state-mode)
        (vnb-state-mode))
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert text)
        (goto-char (point-min))))))

;;; -----------------------------------------------------------------------
;;; Mode definitions

(define-derived-mode vnb-mode comint-mode "VNB"
  "Major mode for the VNB proof checker REPL.
Runs the prover as a subprocess via comint."
  (make-local-variable 'comint-prompt-regexp)
  (setq comint-prompt-regexp "^[0-9]+ \\]=> \\|^\\.\\.\\.> ")
  (setq vnb--preoutput-acc "")
  (setq vnb--orig-filter nil))

(define-derived-mode vnb-state-mode fundamental-mode "VNB-State"
  "Read-only display mode for VNB proof state."
  (setq buffer-read-only t))

;;; -----------------------------------------------------------------------
;;; Key bindings

(define-key vnb-mode-map "\C-c\C-s" 'vnb-show-state)
(define-key vnb-mode-map "\C-c\C-p" 'vnb-goto-state)

(define-key vnb-state-mode-map "q" 'vnb-goto-repl)
(define-key vnb-state-mode-map "\C-c\C-s" 'vnb-show-state)

;;; -----------------------------------------------------------------------
;;; Commands

(defun vnb-show-state ()
  "Send (show) to the VNB prover to refresh the proof-state display."
  (interactive)
  (let ((buf (get-buffer vnb-buffer-name)))
    (if buf
        (comint-send-string buf "(show)\n")
      (message "VNB prover is not running.  Use M-x vnb to start it."))))

(defun vnb-goto-state ()
  "Switch to the *VNB State* proof-state display buffer."
  (interactive)
  (let ((buf (get-buffer vnb-state-buffer-name)))
    (if buf
        (pop-to-buffer buf)
      (message "No VNB proof state buffer yet."))))

(defun vnb-goto-repl ()
  "Switch to the *VNB* REPL buffer."
  (interactive)
  (let ((buf (get-buffer vnb-buffer-name)))
    (if buf
        (pop-to-buffer buf)
      (message "No VNB REPL buffer."))))

;;; -----------------------------------------------------------------------
;;; Entry point

(defun vnb ()
  "Start the VNB proof checker in a side-by-side two-buffer layout.
Left window: *VNB* REPL.  Right window: *VNB State* proof state."
  (interactive)
  (let ((repl-buf  (get-buffer-create vnb-buffer-name))
        (state-buf (get-buffer-create vnb-state-buffer-name)))
    ;; Initialise the state buffer.
    (with-current-buffer state-buf
      (unless (eq major-mode 'vnb-state-mode)
        (vnb-state-mode)))
    ;; Start the prover process if not already running.
    (with-current-buffer repl-buf
      (unless (vnb--process-live-p repl-buf)
        (vnb-mode)
        (comint-exec repl-buf "VNB" vnb-program nil nil)
        (vnb--install-process-filter)))
    ;; Side-by-side layout: REPL on the left, state on the right.
    (delete-other-windows)
    (switch-to-buffer repl-buf)
    (split-window nil nil t)                    ; horizontal split
    (set-window-buffer (next-window) state-buf)
    (goto-char (point-max))))

;;; -----------------------------------------------------------------------
;;; Synchronous eval: send expression, wait for next REPL prompt

(defun vnb--trim (str)
  "Strip leading and trailing whitespace from STR."
  (when (string-match "^[ \t\n\r]+" str)
    (setq str (substring str (match-end 0))))
  (when (string-match "[ \t\n\r]+$" str)
    (setq str (substring str 0 (match-beginning 0))))
  str)

(defun vnb--extract-value (raw)
  "Extract Scheme return value from RAW accumulated REPL output.
Strips the trailing prompt and the echoed input line, then returns the
text after \";Value: \" or \"No return value\" for void results."
  ;; Strip trailing prompt: "\nN ]=> " at end of string.
  (when (string-match "\n[0-9]+ \\]=> .*\\'" raw)
    (setq raw (substring raw 0 (match-beginning 0))))
  ;; Strip echoed input (everything up to and including the first newline).
  (when (string-match "\n" raw)
    (setq raw (substring raw (match-end 0))))
  (setq raw (vnb--trim raw))
  (cond
    ((string-match ";Value: " raw)
     (vnb--trim (substring raw (match-end 0))))
    ((string-match ";No return value" raw)
     "No return value")
    (t raw)))

(defun vnb--prompt-past-p (pos)
  "Return non-nil if a Scheme REPL prompt appears in current buffer after POS."
  (save-excursion
    (goto-char pos)
    (re-search-forward "[0-9]+ \\]=> " nil t)))

(defun vnb-eval-string (str &optional timeout)
  "Send STR to the VNB prover; return its Scheme return value as a string.
TIMEOUT is maximum seconds to wait (default 30).
Completion is detected by watching for the next REPL prompt in the *VNB*
buffer, which comint updates regardless of how accept-process-output works."
  (let* ((timeout (or timeout 30))
         (buf     (get-buffer vnb-buffer-name))
         (proc    (and buf (get-buffer-process buf))))
    (unless (and proc (eq (process-status proc) 'run))
      (error "VNB prover is not running.  Use M-x vnb to start it."))
    (with-current-buffer buf
      (let ((start (point-max))
            (n 0))
        (process-send-string proc (concat str "\n"))
        (while (and (< n timeout)
                    (not (vnb--prompt-past-p start)))
          (accept-process-output proc 1)
          (setq n (1+ n)))
        (vnb--extract-value
         (buffer-substring-no-properties start (point-max)))))))

(defun vnb-insert-result (str)
  "Evaluate STR in the VNB prover and insert the result at point."
  (interactive "sVNB expression: ")
  (insert (vnb-eval-string str)))

;;; -----------------------------------------------------------------------
;;; Command alist
;;;
;;; Each entry: (short-name  usage-signature  one-line description)
;;; The alist form vnb-commands-alist maps short-name -> usage for completion.

(defvar vnb-commands
  '(;; ---- Starting a proof ----
    ("sp"      "(sp WIC)"
     "Start a new proof; WIC must be a wff-in-context from (make-wff FORMULA).
  A raw S-expression is rejected -- use (sp (make-wff '(formula))) .")
    ;; ---- Decomposition ----
    ("di"      "(di)"
     "Direct inference: decompose current goal by its top connective.
  AND  -> two subgoals; IMPLIES -> add antecedent to assumptions;
  FORALL chain -> introduce fresh variables; FORSOME -> witness.")
    ("pbc"     "(pbc)"
     "Proof by contradiction: assume (NOT goal), prove FALSITY.")
    ("ass"     "(ass)"
     "Close goal immediately if it matches an assumption or is TRUTH.")
    ;; ---- Equality / arithmetic ----
    ("rfl"     "(rfl)"
     "Close goal (= a a) when a is demonstrably defined.")
    ("qrfl"    "(qrfl)"
     "Close goal (== a a) unconditionally (quasi-equality).")
    ("arith"   "(arith)"
     "Close goal by ground arithmetic: evaluates closed numeric sentences
  over NN/ZZ/QQ/RR/CC using exact Scheme arithmetic.  No axiom chain.")
    ("rs"      "(rs)"
     "Ring simplify: close a ring equality goal (= lhs rhs) by reducing both
  sides to the same polynomial normal form.  Works directly on a bare
  equality or on a universally quantified goal of the form
    (FORALL x (IMPLIES (IN x RR) ... (= lhs rhs)))
  without a prior (di).  Generators are detected automatically; each one
  must be certified as an element of NN/ZZ/QQ/RR/CC by a context
  assumption (IN x DOMAIN) or by the enclosing FORALL typing.")
    ;; ---- One-argument commands ----
    ("ai"      "(ai FORMULA)"
     "Antecedent inference: decompose assumption FORMULA by its connective.
  AND  -> split into two assumptions; IMPLIES -> generate IMPLIES goal;
  FORSOME -> introduce witness.")
    ("cut"     "(cut FORMULA)"
     "Introduce a lemma FORMULA: subgoal 1 proves it, subgoal 2 uses it.")
    ("ew"      "(ew TERM)"
     "Exists witness: to prove (FORSOME x p), prove p[x/TERM].")
    ("bc"      "(bc FORMULA)"
     "Backchain on FORMULA = (IMPLIES p goal): generate subgoal p.")
    ("wk"      "(wk FORMULA)"
     "Weaken: remove FORMULA from the current assumptions.")
    ("ta"      "(ta 'NAME)"
     "Add the named theorem or axiom NAME to the current assumptions.")
    ("mac"     "(mac 'NAME)"
     "Apply macete NAME: rewrite the current goal using the named theorem.")
    ;; ---- Two-argument commands ----
    ("inst"    "(inst FORMULA TERM)"
     "Instantiate FORALL: from (FORALL x p) = FORMULA in context, add p[x/TERM].")
    ("ui"      "(ui K)"
     "Union intro: prove (IN x (UNION ...)) via the K-th branch.")
    ("ue"      "(ue FORMULA)"
     "Union elim: case-split on (IN x (UNION ...)) = FORMULA in assumptions.")
    ("ce"      "(ce FORMULA K)"
     "Cartesian elim: from (IN x (CARTESIAN A1...An)) = FORMULA, extract K-th component.")
    ("ie"      "(ie FORMULA K)"
     "Intersection elim: from (IN x (INTERSECTION A1...An)) = FORMULA, use K-th set.")
    ;; ---- No-argument constructor commands ----
    ("ci"      "(ci)"
     "Cartesian intro: split (IN (LIST a1...an) (CARTESIAN A1...An)) into n subgoals.")
    ("nth-r"   "(nth-r)"
     "NTH reduce: simplify (NTH k (LIST e1...en)) to e_k.")
    ("oi-l"    "(oi-l)"
     "Or intro left: to prove (OR p q), prove p instead.")
    ("oi-r"    "(oi-r)"
     "Or intro right: to prove (OR p q), prove q instead.")
    ("ii"      "(ii)"
     "Intersection intro: split (IN x (INTERSECTION A1...An)) into n subgoals.")
    ;; ---- Focus and display ----
    ("focus"   "(focus N)"
     "Switch focus to the N-th open goal (1-based).")
    ("show"    "(show)"
     "Display the current proof state; updates the *VNB State* buffer.")
    ;; ---- Formula constructors ----
    ("fa"      "(fa BINDINGS BODY)"
     "Build nested FORALL formula from BINDINGS list.
  Each binding is (x), (IN x A), or (IN (LIST n1...nk) A).  Example:
    (fa '((IN x RR) (IN y RR)) '(= (+ x y) (+ y x)))")
    ("fs"      "(fs BINDINGS BODY)"
     "Build nested FORSOME formula from BINDINGS list.  See fa.")
    ;; ---- Context machinery ----
    ("make-wff"               "(make-wff FORMULA)"
     "Wrap FORMULA in a wff-in-context tagged with the current context stack.")
    ("wff-free-vars"          "(wff-free-vars WIC)"
     "Free variables of WIC respecting bound names from active local contexts.")
    ("declare-local-context"  "(declare-local-context BINDING NAME)"
     "Declare a named local context.  BINDING is (IN (LIST n1...nk) A).
  Names n1...nk become bound in subsequent make-wff calls.")
    ("undeclare-local-context" "(undeclare-local-context NAME)"
     "Exit the named local context (does not destroy it; get-context still works).")
    ("get-context"            "(get-context NAME)"
     "Return the binding of the named local context.")
    ("unravel"                "(unravel WIC)"
     "Wrap WIC's formula with explicit FORALL quantifiers for each context layer,
  producing a self-contained statement in the base theory.")
    ("print-wff-in-context"   "(print-wff-in-context WIC)"
     "Display WIC as (wff-in-context FORMULA IN CONTEXT-NAME).")
    ;; ---- Arithmetic oracle ----
    ("vnb-do-arith"           "(vnb-do-arith FORMULA)"
     "Evaluate a closed arithmetic FORMULA; returns #t or #f.
  Use outside proofs to check ground numeric facts.")
    ;; ---- Proof state queries ----
    ("proof-done?"            "(proof-done? PS)"
     "Return #t if the proof PS is complete (root node grounded).")
    ("proof-open-goals"       "(proof-open-goals PS)"
     "Return the list of ungrounded (open) goal nodes in PS.")
    ;; ---- Theory / structure ----
    ("def-structure"          "(def-structure NAME CARRIERS OP-SPECS AXIOM-NAMES)"
     "Declare a mathematical structure; installs NTH accessor macetes and
  the IS-NAME predicate axiom.")
    ("declare-structure"      "(declare-structure NAME (carriers C1 ...) (op OP (D1 ...) RANGE) ...)"
     "User-facing syntax for def-structure; no quoting required.
  Clause kinds: (carriers C1 C2 ...), (op OPNAME (D1 D2 ...) RANGE),
  (constant CNAME SET).  Example:
    (declare-structure RING
      (carriers ELEMENTS)
      (op PLUS  (ELEMENTS ELEMENTS) ELEMENTS)
      (op TIMES (ELEMENTS ELEMENTS) ELEMENTS))")
    ("specialize-structure"   "(specialize-structure INSTANCE STRUCT IS-THM)"
     "Transport all generic STRUCT theorems to the certified instance INSTANCE.
  IS-THM must be a proved theorem of the form (IS-STRUCT INSTANCE).
  Every theorem of the form (FORALL s (IMPLIES (IS-STRUCT s) P[s]))
  becomes P[INSTANCE], installed as <thm-name>-<instance>.
  Soundness: forall-elim + modus-ponens on the certified IS-STRUCT witness;
  no new axioms.  The interactive shortcut is (spec INSTANCE STRUCT IS-THM).")
    ("spec"                   "(spec INSTANCE STRUCT IS-THM)"
     "Interactive shortcut for specialize-structure.  See specialize-structure."))
  "List of VNB commands.  Each entry: (short-name usage-signature description).")

(defvar vnb-commands-alist
  (mapcar (lambda (entry)
            (cons (car entry) (cadr entry)))
          vnb-commands)
  "Alist mapping VNB short command names to their usage signatures.")

(defun vnb-describe-command (name)
  "Display documentation for VNB command NAME in the echo area."
  (interactive
   (list (completing-read "VNB command: " vnb-commands-alist nil nil)))
  (let ((entry (assoc name vnb-commands)))
    (if entry
        (message "%s\n%s" (cadr entry) (caddr entry))
      (message "Unknown VNB command: %s" name))))

;;; -----------------------------------------------------------------------
;;; vnb-command-mode
;;;
;;; Like the *scratch* buffer (lisp-interaction-mode) but C-j sends the
;;; last S-expression to the VNB prover via vnb-eval-string and inserts
;;; the result below point.

(defun vnb-command-eval-print ()
  "Send the S-expression before point to the VNB prover; insert the result.
Finds the last complete S-expression ending at point (or before any trailing
whitespace), sends it to the running VNB process, then inserts a newline
followed by the result — exactly like eval-print-last-sexp but for VNB."
  (interactive)
  (let* ((end   (save-excursion (skip-chars-backward " \t\n") (point)))
         (start (save-excursion
                  (goto-char end)
                  (condition-case nil
                      (progn (backward-sexp 1) (point))
                    (error (point-min)))))
         (expr   (vnb--trim (buffer-substring-no-properties start end)))
         (result (condition-case err
                     (vnb-eval-string expr)
                   (error (format "(error: %s)" (error-message-string err))))))
    (goto-char (point-max))
    (unless (bolp) (insert "\n"))
    (insert result "\n")))

(defun vnb-command-send-buffer ()
  "Send the entire buffer content to the VNB prover."
  (interactive)
  (let* ((str    (buffer-substring-no-properties (point-min) (point-max)))
         (result (condition-case err
                     (vnb-eval-string str)
                   (error (format "(error: %s)" (error-message-string err))))))
    (goto-char (point-max))
    (unless (bolp) (insert "\n"))
    (insert ";; => " result "\n")))

(defun vnb-command-complete ()
  "Complete the symbol before point using VNB command names."
  (interactive)
  (let* ((end   (point))
         (start (save-excursion
                  (skip-chars-backward "[:alnum:]_-?!")
                  (point)))
         (prefix (buffer-substring-no-properties start end))
         (candidates (all-completions prefix vnb-commands-alist)))
    (cond
     ((null candidates)
      (message "No VNB commands matching '%s'" prefix))
     ((= 1 (length candidates))
      (delete-region start end)
      (insert (car candidates)))
     (t
      (let ((common (try-completion prefix vnb-commands-alist)))
        (when (and common (not (string= common prefix)))
          (delete-region start end)
          (insert common)))
      (with-output-to-temp-buffer "*VNB Completions*"
        (display-completion-list candidates))))))

(define-derived-mode vnb-command-mode scheme-mode "VNB-Cmd"
  "Major mode for a VNB proof command scratch buffer.
Like the Emacs *scratch* buffer (\\[eval-print-last-sexp]) but
\\[vnb-command-eval-print] sends the last S-expression to the VNB prover
and inserts its return value below point.

Key bindings:
  \\[vnb-command-eval-print]  send last sexp to VNB, insert result
  \\[vnb-command-send-buffer] send entire buffer to VNB
  \\[vnb-command-complete]    complete VNB command name at point
  \\[vnb-describe-command]    look up VNB command documentation
  \\[vnb-show-state]          refresh the *VNB State* proof-state buffer"
  (make-local-variable 'comment-start)
  (setq comment-start ";; ")
  (make-local-variable 'comment-end)
  (setq comment-end ""))

(define-key vnb-command-mode-map (kbd "C-j")     'vnb-command-eval-print)
(define-key vnb-command-mode-map (kbd "C-c C-c") 'vnb-command-send-buffer)
(define-key vnb-command-mode-map (kbd "TAB")     'vnb-command-complete)
(define-key vnb-command-mode-map (kbd "C-c C-d") 'vnb-describe-command)
(define-key vnb-command-mode-map (kbd "C-c C-s") 'vnb-show-state)

(defun vnb-command-buffer ()
  "Open (or switch to) the *VNB Commands* scratch buffer in vnb-command-mode.
If the prover is not running, offer to start it with M-x vnb."
  (interactive)
  (let ((buf (get-buffer-create "*VNB Commands*")))
    (with-current-buffer buf
      (unless (eq major-mode 'vnb-command-mode)
        (vnb-command-mode)
        (insert "\
;; VNB Commands buffer -- like *scratch* but C-j sends to the VNB prover.
;; Start the prover first with M-x vnb if it is not already running.
;;
;; C-j        send last S-expression to VNB, insert result here
;; C-c C-c    send entire buffer
;; TAB        complete command name
;; C-c C-d    describe command at point
;; C-c C-s    refresh *VNB State* proof-state buffer

")))
    (pop-to-buffer buf)
    (goto-char (point-max))))

(provide 'vnb)
