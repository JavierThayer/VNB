;;; vnb.el --- Emacs interface for the VNB proof checker
;;
;; Plain Elisp; no external package dependencies.
;; Load the source file directly (no need to byte-compile).
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

(defvar vnb-state-update-hook nil
  "Hook run after each new proof-state arrives from the prover.
Each hook function is called with one string argument: the full state
text (sentinel lines stripped).  Used by the Phase-2 launcher to
re-render its Proof Workspace on every state change.")

(defvar vnb-error-hook nil
  "Hook run when a `;; VNB error: MSG' line is detected in prover output.
Each hook function is called with one string argument: MSG (the text
after the prefix).  The Phase-2 launcher uses this to repaint its
workspaces with an error panel.")

(defvar vnb--last-error nil
  "Most recent VNB error message text (without the `;; VNB error: '
prefix), or nil if none current.  Set by the preoutput filter when
an error line streams in from the prover; cleared by the state-update
handler on the next successful proof-state update.")

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
;;; comint-preoutput-filter-functions.  vnb--preoutput-acc accumulates
;;; output across calls while waiting for a complete sentinel block.

(defvar vnb--preoutput-acc ""
  "Buffer-local accumulator for partial VNB state sentinel blocks.")

(defvar vnb--orig-filter nil
  "Buffer-local storage for the comint process filter we wrapped.")

(defvar vnb--error-line-buf ""
  "Buffer-local accumulator for partial `;; VNB error:' lines.
Holds the tail of process output that has not yet ended with a
newline, so error lines split across two filter chunks are still
recognised when the newline arrives.")

(make-variable-buffer-local 'vnb--preoutput-acc)
(make-variable-buffer-local 'vnb--orig-filter)
(make-variable-buffer-local 'vnb--error-line-buf)

(defun vnb--scan-for-errors (string)
  "Scan STRING for `;; VNB error: MSG' lines; fire `vnb-error-hook' for each.
Maintains `vnb--error-line-buf' so a line split across two filter
chunks is still recognised once the trailing newline arrives."
  (setq vnb--error-line-buf (concat vnb--error-line-buf string))
  (let* ((parts    (split-string vnb--error-line-buf "\n"))
         ;; Last element is text after the final newline (possibly empty
         ;; or a partial line); keep it for the next filter call.
         (complete (butlast parts))
         (tail     (car (last parts))))
    (setq vnb--error-line-buf tail)
    (dolist (line complete)
      (when (string-match "\\`;; VNB error: \\(.*\\)\\'" line)
        (let ((msg (match-string 1 line)))
          (setq vnb--last-error msg)
          (message "VNB error: %s" msg)
          (run-hook-with-args 'vnb-error-hook msg))))))

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
    (vnb--scan-for-errors result)
    result))

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
        (goto-char (point-min)))))
  (run-hook-with-args 'vnb-state-update-hook text))

;;; -----------------------------------------------------------------------
;;; Mode definitions

(define-derived-mode vnb-mode comint-mode "VNB"
  "Major mode for the VNB proof checker REPL.
Runs the prover as a subprocess via comint."
  (make-local-variable 'comint-prompt-regexp)
  (setq comint-prompt-regexp "^[0-9]+ \\]=> \\|^\\.\\.\\.> ")
  (setq vnb--preoutput-acc "")
  (setq vnb--orig-filter nil)
  (setq vnb--error-line-buf ""))

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

(defun vnb--ensure-process ()
  "Start the prover subprocess and its buffers WITHOUT touching the window
layout.  Returns the *VNB* REPL buffer.  Callers that want the REPL visible
arrange their own windows (see `vnb' for the two-pane layout); launcher
actions that only need the process running call this so merely starting the
prover never rearranges the user's frame."
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
    repl-buf))

(defun vnb ()
  "Start the VNB proof checker in a side-by-side two-buffer layout.
Left window: *VNB* REPL.  Right window: *VNB State* proof state."
  (interactive)
  (let ((repl-buf  (vnb--ensure-process))
        (state-buf (get-buffer vnb-state-buffer-name)))
    ;; Side-by-side layout: REPL on the left, state on the right.
    (delete-other-windows)
    (switch-to-buffer repl-buf)
    (split-window nil nil t)                    ; horizontal split
    (set-window-buffer (next-window) state-buf)
    (goto-char (point-max))))

;;; -----------------------------------------------------------------------
;;; Synchronous eval: send expression, wait for next REPL prompt

(defun vnb--trim (str)
  "Strip leading and trailing whitespace from STR.
Anchored with \\=\\` and \\=\\' (string start/end), NOT ^/$: in Emacs regexp
^ also matches after every newline, so on a MULTI-LINE form ^[ \t\n\r]+ would
match the indentation at the start of line 2 and substring away everything
before it -- truncating e.g. `(sp (make-wff '(FORALL R ...' down to the bare
inner `(FORALL f ...)', which then evaluates R and raises `Unbound variable:
r'.  That was the multi-line Scratch Workspace bug."
  (when (string-match "\\`[ \t\n\r]+" str)
    (setq str (substring str (match-end 0))))
  (when (string-match "[ \t\n\r]+\\'" str)
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
  "Return the prompt kind for the first Scheme REPL prompt after POS, or nil.
The value is `ok' for a normal `N ]=> ' top-level prompt or `error' for a
`N error> ' nested error-REPL prompt.  Recognising the error prompt is
essential: otherwise an evaluation error leaves `vnb-eval-string' spinning
for the full timeout while the prover sits wedged in the error REPL."
  (save-excursion
    (goto-char pos)
    (when (re-search-forward "[0-9]+ \\(\\]=>\\|error>\\) " nil t)
      (if (equal (match-string 1) "]=>") 'ok 'error))))

(defun vnb--last-prompt-type ()
  "Return `ok', `error', or nil for the LAST REPL prompt in the buffer."
  (save-excursion
    (goto-char (point-max))
    (when (re-search-backward "[0-9]+ \\(\\]=>\\|error>\\) ?" nil t)
      (if (equal (match-string 1) "]=>") 'ok 'error))))

(defun vnb--repl-recover (proc)
  "Climb PROC's MIT Scheme REPL out of any nested error level to top level.
Issues `(restart 1)' (\"return to read-eval-print level 1\") until the last
prompt is a normal top-level prompt again, so a stray erroring C-j cannot
brick the rest of the session."
  (with-current-buffer (process-buffer proc)
    (let ((tries 0))
      (while (and (< tries 6) (eq (vnb--last-prompt-type) 'error))
        (let ((mark (point-max)) (n 0))
          (process-send-string proc "(restart 1)\n")
          (while (and (< n 20) (not (vnb--prompt-past-p mark)))
            (accept-process-output proc 0.5)
            (setq n (1+ n))))
        (setq tries (1+ tries))))))

(defun vnb--extract-error (raw)
  "Extract a one-line `;; error: MSG' summary from RAW error-REPL output."
  (let ((msg nil))
    (dolist (line (split-string raw "\n"))
      (when (and (null msg)
                 (string-match "\\`;\\([^;].*\\)\\'" line)
                 (not (string-prefix-p ";Value" line)))
        (setq msg (vnb--trim (match-string 1 line)))))
    (concat ";; error: " (or msg "evaluation error"))))

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
            (n 0)
            (kind nil))
        (process-send-string proc (concat str "\n"))
        (while (and (< n (* 2 timeout))
                    (not (setq kind (vnb--prompt-past-p start))))
          (accept-process-output proc 0.5)
          (setq n (1+ n)))
        (let ((raw (buffer-substring-no-properties start (point-max))))
          (if (eq kind 'error)
              ;; The form errored and dropped the prover into a nested error
              ;; REPL.  Climb back to top level so the session stays usable,
              ;; and return a readable one-line error instead of hanging.
              (progn (vnb--repl-recover proc)
                     (vnb--extract-error raw))
            (vnb--extract-value raw)))))))

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
    ("bc*"     "(bc* 'NAME (BINDINGS) h1 h2 ...)"
     "Matching backchain on a NAMED theorem/axiom (the workhorse for citing a
  lemma).  Peels NAME's leading FORALL/IMPLIES and matches its CONCLUSION
  against the goal, then spawns one subgoal per lemma hypothesis.
    (bc* 'thm)                  -- conclusion fully determines the instance
    (bc* 'thm ((v val) ...))    -- supply schema vars the conclusion omits
    (bc* 'thm () h1 h2 ...)     -- hk discharges the k-th hypothesis; (ass)
                                   closes one already in the assumptions.
  Orchestrates ta/inst/cut/bc/assumption -- not a primitive.  Cannot match a
  conclusion whose head is a structure accessor like ((MUL s) x y).")
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
    ("bu-set"  "(bu-set)"
     "Big-union sethood: prove (IN (BIG-UNION z A body) SET) via subgoals (IN A SET) and (FORALL z (IMPLIES (IN z A) (IN body SET))).")
    ("bu-mi"   "(bu-mi TERM)"
     "Big-union mem-intro: prove (IN x (BIG-UNION z A body)) via witness TERM, with subgoals (IN TERM A) and (IN x body[z:=TERM]).")
    ("bu-me"   "(bu-me FORMULA)"
     "Big-union mem-elim: from (IN x (BIG-UNION z A body)) = FORMULA in assumptions, introduce fresh eigenvariable e with (IN e A) and (IN x body[z:=e]).")
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

(defun vnb--no-value-p (result)
  "Non-nil if RESULT from `vnb-eval-string' carries no meaningful value.
Proof commands return unspecified / no value (\";Unspecified return value\",
\"No return value\"); the side effect on the proof state is what matters, so
these get a state-summary comment instead of a raw value."
  (let ((r (vnb--trim (or result ""))))
    (or (string= r "")
        (string= r "No return value")
        (string-prefix-p ";" r))))

(defun vnb--unquote (s)
  "Strip one leading and trailing double quote from Scheme string literal S."
  (let ((s (vnb--trim (or s ""))))
    (if (and (>= (length s) 2)
             (eq (aref s 0) ?\")
             (eq (aref s (1- (length s))) ?\"))
        (substring s 1 (1- (length s)))
      s)))

(defun vnb--toplevel-sexp-bounds (pos)
  "Return (START . END) for the S-expression to send for a C-j at POS.
If POS is inside one or more lists, the OUTERMOST enclosing top-level form
is returned -- so a C-j anywhere inside a multi-line `(sp (make-wff '...))'
sends the whole quoted goal, never a bare inner sub-form (which would
evaluate symbols like R and raise `Unbound variable: r').  If POS is between
forms, the sexp ending at POS (skipping trailing whitespace) is used, so a
plain `(di)' on its own still works.  Returns nil inside a string/comment."
  (save-excursion
    ;; Force lazy syntax-propertize to run first: on a freshly-typed buffer the
    ;; FIRST parse-partial-sexp otherwise mis-parses (quote/paren syntax not yet
    ;; applied), mis-locating the enclosing form and grabbing a bare inner
    ;; sub-form -> `Unbound variable: r'.  Parse from BOB uncached so an edited
    ;; or rebuilt buffer cannot return a stale syntax-ppss result either.
    (syntax-propertize (point-max))
    (let* ((ppss  (parse-partial-sexp (point-min) pos))
           (opens (nth 9 ppss)))
      (cond
        ((nth 8 ppss) nil)                       ; inside string or comment
        (opens                                   ; inside a list: outermost form
         (let ((start (apply #'min opens)))      ; smallest pos = outermost paren
           (goto-char start)
           (condition-case nil
               (progn (forward-sexp 1) (cons start (point)))
             (error nil))))
        (t                                       ; between forms: sexp before POS
         (let* ((end   (progn (goto-char pos) (skip-chars-backward " \t\n") (point)))
                (start (condition-case nil
                           (progn (goto-char end) (backward-sexp 1) (point))
                         (error nil))))
           (and start (cons start end))))))))

(defun vnb--reserved-warning-since (buf start)
  "Return the loud reserved-name (!!!!!) banner emitted in BUF since START, or nil.
`warn-constant-binders!' (fired by `make-wff' when a bound variable is named
like a registered constant) prints its banner to the process buffer BEFORE the
`;Value:' line, so `vnb--extract-value' discards it and the warning never reaches
the *VNB Commands* sheet.  This recovers the banner lines verbatim so the caller
can surface them.  Banner lines begin with a run of `!' (the `!!!!!' rows and the
`bang-line' rules); nothing else the REPL echoes does."
  (and buf
       (with-current-buffer buf
         (let ((raw (buffer-substring-no-properties start (point-max)))
               (out '()))
           (dolist (ln (split-string raw "\n"))
             (when (string-match-p "\\`\\s-*!!" ln)
               (push ln out)))
           (when out (mapconcat #'identity (nreverse out) "\n"))))))

(defun vnb-command-eval-print ()
  "Evaluate VNB code and insert the result, like \\[eval-print-last-sexp].
With an active region, send the region as a block: it is wrapped in
\(begin ...) so it yields the value of its last expression (begin is
Scheme's progn) -- use this for multi-command tactical blocks such as
\(di)(di)(di).  Otherwise send the whole top-level S-expression that point
is in (or the one ending at point), so a C-j anywhere inside a multi-line
goal sends the entire quoted form.

The block runs with prover state output suppressed (so command state dumps
do not pollute the captured value), then the result is inserted on a fresh
line just after the evaluated text — never at the end of the buffer:
 * a real value (formula, number, …) is inserted raw;
 * a side-effecting proof command (no useful value) gets a one-line state
   summary as a ;; comment, e.g. `;; => 2 open goals' or `;; => done',
   and the *VNB State* pane is refreshed once.
Point is left after the inserted text."
  (interactive)
  (let (expr insert-at)
    (if (use-region-p)
        (let ((beg (region-beginning))
              (end (region-end)))
          (setq expr (concat "(begin "
                             (vnb--trim (buffer-substring-no-properties beg end))
                             ")")
                insert-at end)
          (deactivate-mark))
      (let ((b (vnb--toplevel-sexp-bounds (point))))
        (unless b
          (error "Nothing to send: place point in or after a VNB expression"))
        (setq expr (vnb--trim (buffer-substring-no-properties (car b) (cdr b)))
              insert-at (cdr b))))
    ;; Suppress show output so a command's state dump does not get captured as
    ;; its "value"; capture the clean value; restore.  Also recover any loud
    ;; reserved-name (!!!!!) warning make-wff emits during the eval -- it prints
    ;; to the process buffer before the ;Value: line, so vnb--extract-value drops
    ;; it; read it straight from the *VNB* buffer and surface it above the result.
    (vnb-eval-string "(set! *vnb-quiet* #t)")
    (let* ((vbuf   (get-buffer vnb-buffer-name))
           (vstart (and vbuf (with-current-buffer vbuf (point-max))))
           (result (condition-case err
                       (vnb-eval-string expr)
                     (error (format "(error: %s)" (error-message-string err)))))
           (warn   (vnb--reserved-warning-since vbuf vstart)))
      (vnb-eval-string "(set! *vnb-quiet* #f)")
      (goto-char insert-at)
      (unless (bolp) (insert "\n"))
      (when warn (insert warn "\n"))
      (cond
        ;; The form errored: the prover has already been climbed back to top
        ;; level by `vnb-eval-string'; just show the error, do not touch state.
        ((and (stringp result) (string-prefix-p ";; error:" result))
         (insert result "\n"))
        ;; Side-effecting command: refresh the State pane and annotate with a
        ;; one-line summary instead of the irrelevant Scheme value.
        ((vnb--no-value-p result)
         (insert ";; ⇒ "
                 (condition-case nil
                     (vnb--unquote (vnb-eval-string "(refresh-status)"))
                   (error "done"))
                 "\n"))
        (t (insert result "\n"))))))

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
                  (skip-chars-backward "[:alnum:]_-?!*")
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
;; VNB Scratch Workspace -- like *scratch* but C-j sends to the VNB prover.
;; Start the prover first with M-x vnb if it is not already running.
;;
;; C-j        send the S-expression before point to VNB, insert result below;
;;            with a region active, send the region as a (begin ...) block
;;            (begin is Scheme's progn).  A real value (formula, number) is
;;            inserted raw; a side-effecting command gets a ;; state summary,
;;            e.g.  ;; => 2 open goals.  Tacticals: (repeat di), (orelse di ass)
;; C-c C-c    send the entire buffer as one block
;; TAB        complete at point: a command name, or -- inside (mac '… / (bc* '…
;;            / (ta '… -- a rule/lemma name from the live index (★ = goal-relevant)
;; C-c C-d    describe command at point
;; C-c C-s    refresh *VNB State* proof-state buffer

")))
    ;; switch-to-buffer (reuse the selected window), not pop-to-buffer: the
    ;; launcher navigates every workspace this way, so the Scratch Workspace
    ;; replaces the *VNB Lobby* window instead of splitting alongside it.
    (switch-to-buffer buf)
    (goto-char (point-max))))

(provide 'vnb)
