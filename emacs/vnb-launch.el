;;; vnb-launch.el --- VNB workspace launcher (Phase 1)  -*- lexical-binding: t; -*-
;;
;; Loaded by the ~/prover/VNB shell launcher.  Sets up a styled
;; Initial Workspace buffer with a menu-bar and tool-bar wired to the
;; existing vnb.el REPL commands.
;;
;; GNU Emacs only.  Plain Elisp; no external packages.

(require 'cl-lib)
(require 'subr-x)   ; string-trim, string-empty-p, string-join (void pre-Emacs 28)

;;; -----------------------------------------------------------------------
;;; Where am I

(defconst vnb-launch--el-dir
  (file-name-directory (or load-file-name buffer-file-name "."))
  "Directory holding the VNB elisp bundle (this file, vnb.el, vnb-commands.lisp).")

(defconst vnb-launch--dir
  (file-name-directory (directory-file-name vnb-launch--el-dir))
  "The prover root: the parent of the elisp dir.  Used for prover
resources (structure-notes, examples, user-additions, file-picker defaults).")

(defconst vnb-launch--ref-dir
  (file-name-as-directory (expand-file-name "reference" vnb-launch--dir))
  "Generated-index directory (THEOREMS.md, STRUCTURE-INDEX.md, ...).")

(load (expand-file-name "vnb.el" vnb-launch--el-dir) nil t)

;;; -----------------------------------------------------------------------
;;; Faces -- white-on-black with highlights.
;;;
;;; Defined as named faces so the user can later customize them with
;;; M-x customize-face.  Buffer-local face-remapping in vnb-workspace-mode
;;; applies the black background only inside workspace buffers, leaving
;;; the rest of Emacs untouched if other modes are visited.

(defgroup vnb-faces nil
  "Faces for VNB workspace buffers."
  :group 'vnb)

(defface vnb-default
  '((t :background "black" :foreground "#e0e0e0"))
  "Default text in VNB workspace buffers."
  :group 'vnb-faces)

(defface vnb-title
  '((t :inherit vnb-default :foreground "#ffcc66" :weight bold :height 1.6))
  "Workspace title."
  :group 'vnb-faces)

(defface vnb-heading
  '((t :inherit vnb-default :foreground "#66ccff" :weight bold :height 1.1))
  "Section headings inside a workspace."
  :group 'vnb-faces)

(defface vnb-button
  '((t :background "#264f78" :foreground "#ffffff" :weight bold
       :box (:line-width 2 :color "#3a7cb8" :style released-button)))
  "Clickable action buttons."
  :group 'vnb-faces)

(defface vnb-button-mouse
  '((t :background "#3a7cb8" :foreground "#ffffff" :weight bold
       :box (:line-width 2 :color "#66ccff" :style released-button)))
  "Mouseover state for action buttons."
  :group 'vnb-faces)

(defface vnb-body
  '((t :inherit vnb-default))
  "Body text."
  :group 'vnb-faces)

(defface vnb-accent
  '((t :inherit vnb-default :foreground "#ff66cc"))
  "Accent (sequent arrows, separators, status markers)."
  :group 'vnb-faces)

(defface vnb-goal
  '((t :inherit vnb-default :foreground "#ffff66" :weight bold))
  "Active goal text."
  :group 'vnb-faces)

(defface vnb-assumption
  '((t :inherit vnb-default :foreground "#99dd99"))
  "Assumption text."
  :group 'vnb-faces)

(defface vnb-error
  '((t :background "#5a1010" :foreground "#ff8080" :weight bold))
  "Error text."
  :group 'vnb-faces)

(defface vnb-dim
  '((t :inherit vnb-default :foreground "#888888"))
  "Dim/secondary text."
  :group 'vnb-faces)

;;; Faces for the library browser (vnb-library-mode).
(defface vnb-library-section
  '((t :inherit vnb-heading :foreground "#66ccff" :weight bold :height 1.15))
  "Section heading (`### name') in the library browser."
  :group 'vnb-faces)

(defface vnb-library-toc
  '((t :inherit vnb-heading :foreground "#ffcc66" :weight bold :height 1.10))
  "Top-level heading (`## ...') and ToC line numbers."
  :group 'vnb-faces)

(defface vnb-library-emphasis
  '((t :inherit vnb-default :foreground "#bbcdda" :slant italic))
  "Italic / *emphasis* spans like `*Declared in*`."
  :group 'vnb-faces)

(defface vnb-library-code
  '((t :inherit vnb-default :foreground "#c8d364"))
  "Inline `code` spans."
  :group 'vnb-faces)

(defface vnb-library-link
  '((t :inherit vnb-default :foreground "#9ec1ff" :underline t))
  "Markdown `[label](target)` links."
  :group 'vnb-faces)

;;; Apply the dark background buffer-locally (face-remapping).
(defun vnb-launch--apply-faces ()
  "Remap the buffer's default face to vnb-default."
  (face-remap-add-relative 'default 'vnb-default))

;;; -----------------------------------------------------------------------
;;; Workspace mode and buffer

(defvar vnb-workspace-buffer-name "*VNB Workspace*"
  "Name of the Home Workspace buffer.")

(defvar vnb-workspace-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m "g" 'vnb-ws-refresh)
    (define-key m "q" 'vnb-ws-quit)
    (define-key m "s" 'vnb-ws-start-proof)
    (define-key m "f" 'vnb-ws-build-formula)
    (define-key m "b" 'vnb-ws-build-structure)
    (define-key m "t" 'vnb-ws-show-theorems)
    (define-key m "p" 'vnb-ws-show-pss)
    (define-key m "l" 'vnb-ws-browse-library)
    (define-key m "F" 'vnb-ws-show-fingerprints)
    (define-key m "d" 'vnb-describe-structure)
    (define-key m "D" 'vnb-ws-show-definitions)
    (define-key m "m" 'vnb-structure-manual)
    (define-key m "G" 'vnb-structure-graph-html)
    (define-key m "e" 'vnb-ws-examples)
    (define-key m "S" 'vnb-ws-scratch-workspace)
    (define-key m "W" 'vnb-ws-save-session)
    m)
  "Keymap for the VNB workspace buffer.")

;;; -----------------------------------------------------------------------
;;; Slim mode line for VNB workspaces.
;;;
;;; The default mode line carries the coding system, a modified/read-only
;;; flag, line/scroll position, and the minor-mode list -- none of which a
;;; VNB workspace user needs.  (Workspaces are read-only unless they need
;;; input; either way that status is not the user's concern.)  Show only the
;;; workspace name: the buffer name with its surrounding asterisks stripped.

(defun vnb-launch--mode-line-name ()
  "The workspace name for the slim mode line: buffer name sans asterisks."
  (replace-regexp-in-string "\\`\\*+\\|\\*+\\'" "" (buffer-name)))

(defvar vnb-launch--mode-line-format
  '("  " (:eval (vnb-launch--mode-line-name)))
  "Mode-line format for VNB workspace buffers: workspace name only.")

(dolist (hook '(vnb-workspace-mode-hook
                vnb-structure-card-mode-hook
                vnb-structure-graph-mode-hook
                vnb-library-mode-hook
                vnb-proof-mode-hook
                vnb-overview-mode-hook
                vnb-structure-mode-hook
                vnb-examples-mode-hook
                vnb-example-script-mode-hook))
  (add-hook hook
            (lambda () (setq-local mode-line-format vnb-launch--mode-line-format))))

(define-derived-mode vnb-workspace-mode special-mode "VNB-Workspace"
  "Major mode for the VNB Home Workspace buffer."
  (setq buffer-read-only t)
  (setq truncate-lines nil)
  (vnb-launch--apply-faces))

;;; -----------------------------------------------------------------------
;;; Workspace painters

(defun vnb-launch--insert-button (label action help)
  "Insert a clickable button labelled LABEL that invokes ACTION."
  (insert-text-button
   (concat "  " label "  ")
   'face 'vnb-button
   'mouse-face 'vnb-button-mouse
   'follow-link t
   'help-echo help
   'action (lambda (_) (call-interactively action))))

(defun vnb-launch--prover-running-p ()
  "Non-nil if a VNB prover subprocess is alive."
  (vnb--process-live-p (get-buffer vnb-buffer-name)))

(defun vnb-launch--paint-workspace ()
  "Render the workspace contents into the current buffer."
  (let ((inhibit-read-only t))
    (erase-buffer)
    (insert "\n")
    (insert (propertize "  VNB Math Assistant" 'face 'vnb-title))
    (insert "\n")
    (insert (propertize "  Home Workspace"  'face 'vnb-heading))
    (insert "\n\n")
    (insert (propertize
             (make-string 60 ?─)
             'face 'vnb-accent))
    (insert "\n\n")
    (insert (propertize "  What would you like to do?\n\n" 'face 'vnb-body))
    (vnb-launch--insert-button "Start Proof"
                               'vnb-ws-start-proof
                               "Begin a new proof from a formula")
    (insert (propertize "   begin a new proof\n\n" 'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Calculator"
                               'vnb-ws-calculator
                               "Work out an arithmetic expression like 2 + 3 + 5")
    (insert (propertize "    add, multiply, subtract — see the answer\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Build Formula"
                               'vnb-ws-build-formula
                               "Parse and validate a formula")
    (insert (propertize "   parse and validate a formula\n\n" 'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Build Structure"
                               'vnb-ws-build-structure
                               "Define a new structure and save to structure-library/")
    (insert (propertize " define a new structure (saved to file)\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Show Theorems"
                               'vnb-ws-show-theorems
                               "List theorems in the current theory")
    (insert (propertize "   list installed theorems\n\n" 'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Show PSS"
                               'vnb-ws-show-pss
                               "List Proof Support Set entries (accepted without machine proof)")
    (insert (propertize "        list Proof Support Set entries\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Browse Library"
                               'vnb-ws-browse-library
                               "Open STRUCTURE-INDEX.md (structures, views, theorems)")
    (insert (propertize " navigate the structure & view-as library\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Fingerprint Index"
                               'vnb-ws-show-fingerprints
                               "Open FINGERPRINT-INDEX.md: results bucketed by conclusion skeleton (engine/retrieval view)")
    (insert (propertize " results by conclusion fingerprint (retrieval)\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Describe Structure"
                               'vnb-describe-structure
                               "Rendered card: operations, the defining law, view-as, your notes")
    (insert (propertize " a structure's ops, law & views (rendered)\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Definitions"
                               'vnb-ws-show-definitions
                               "Term & predicate definitions: Cauchy, convergence, completeness, …")
    (insert (propertize "        term & predicate definitions (Cauchy, …)\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Structure Manual"
                               'vnb-structure-manual
                               "Render every structure into one reference document")
    (insert (propertize " all structures, one rendered reference\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Structure Graph"
                               'vnb-structure-graph-html
                               "Open the clickable structure graph (refines + view-as) in a browser")
    (insert (propertize "  refines & view-as relations as a clickable diagram\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Examples"
                               'vnb-ws-examples
                               "Browse worked example proofs (step-through)")
    (insert (propertize "       worked example proofs (step-through)\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Scratch Workspace"
                               'vnb-ws-scratch-workspace
                               "Lisp-interaction sheet: C-j sends the sexp (or region as a block) to the prover and inserts the result")
    (insert (propertize " C-j evaluates a sexp / region into the prover\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Save Session"
                               'vnb-ws-save-session
                               "Write every proof completed this session to one re-loadable script file")
    (insert (propertize "     this session's proofs as one script file\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Quit"
                               'vnb-ws-quit
                               "Exit VNB")
    (insert (propertize "            exit VNB\n\n" 'face 'vnb-body))
    (insert (propertize
             (make-string 60 ?─)
             'face 'vnb-accent))
    (insert "\n\n")
    (insert (propertize
             (concat "  Keys: s start proof  |  f build formula  |  "
                     "b build structure  |  t show theorems\n"
                     "        p show PSS  |  l browse library  |  "
                     "F fingerprint index\n"
                     "        d describe structure  |  D definitions  |  "
                     "m manual\n"
                     "        G structure graph  |  e examples  |  "
                     "S scratch workspace\n"
                     "        W save session  |  g refresh  |  q quit\n")
             'face 'vnb-dim))
    (insert "\n")
    (insert (propertize "  Status: " 'face 'vnb-body))
    (insert (propertize
             (if (vnb-launch--prover-running-p)
                 "prover running"
               "prover not started")
             'face (if (vnb-launch--prover-running-p) 'vnb-goal 'vnb-dim)))
    (insert "\n\n")
    (insert (propertize "  --- diagnostics ---\n" 'face 'vnb-dim))
    (insert (propertize (format "  prefs:     %s\n" vnb-launch--prefs-status)
                        'face 'vnb-dim))
    (insert (propertize (format "  defvars:   height=%S width=%S font=%S %spt\n"
                                (cdr (assq 'height vnb-launch-frame-params))
                                (cdr (assq 'width  vnb-launch-frame-params))
                                vnb-launch-default-font-family
                                vnb-launch-default-font-size)
                        'face 'vnb-dim))
    (insert (propertize "             (above are launcher defaults; prefs file may override directly)\n"
                        'face 'vnb-dim))
    (insert (propertize (format "  actual:    %d lines × %d cols, font=%S height %s\n"
                                (frame-height)
                                (frame-width)
                                (face-attribute 'default :family)
                                (face-attribute 'default :height))
                        'face 'vnb-dim))
    (insert (propertize (format "  pixels:    %dw × %dh, pos (%S,%S)\n"
                                (frame-pixel-width)
                                (frame-pixel-height)
                                (frame-parameter nil 'left)
                                (frame-parameter nil 'top))
                        'face 'vnb-dim))
    (insert (propertize (format "  frames:    %d total %S\n"
                                (length (frame-list))
                                (mapcar (lambda (f)
                                          (list (frame-parameter f 'name)
                                                (frame-width f)
                                                (frame-height f)
                                                (frame-visible-p f)))
                                        (frame-list)))
                        'face 'vnb-dim))
    (insert (propertize (format "  graphic?   %S\n" (display-graphic-p))
                        'face 'vnb-dim))
    (insert (propertize (format "  colors:    %S\n" vnb-launch-colors)
                        'face 'vnb-dim))
    (goto-char (point-min))))

(defun vnb-ws-refresh ()
  "Repaint the workspace buffer."
  (interactive)
  (when (get-buffer vnb-workspace-buffer-name)
    (with-current-buffer vnb-workspace-buffer-name
      (vnb-launch--paint-workspace))))

;;; -----------------------------------------------------------------------
;;; Helpers for sending strings to the running (or to-be-started) prover

(defun vnb-launch--wait-for-prompt (&optional timeout)
  "Block until the *VNB* buffer shows a Scheme REPL prompt.
TIMEOUT is seconds to wait (default 180 -- cold load is ~5s with
VNB_SKIP_PROOFS=1, ~160s with full verification).  Returns non-nil if a
prompt appeared, nil on timeout.  Without this, callers race the
load.scm phase and their input either disappears or gets buried under
the load output."
  (let* ((timeout (or timeout 180))
         (buf     (get-buffer vnb-buffer-name))
         (proc    (and buf (get-buffer-process buf))))
    (when (and buf proc (eq (process-status proc) 'run))
      (with-current-buffer buf
        (let ((n 0)
              (seen nil))
          (while (and (< n timeout)
                      (not (setq seen
                                 (save-excursion
                                   (goto-char (point-max))
                                   (forward-line -1)
                                   (re-search-forward "[0-9]+ \\]=> "
                                                      nil t)))))
            (accept-process-output proc 1)
            (setq n (1+ n)))
          seen)))))

(defun vnb-launch--ensure-prover ()
  "Start the prover subprocess if not already running, WITHOUT changing the
window layout (use `vnb' or the explicit show-* helpers to make the REPL
visible).  On cold start, block until the prover's first REPL prompt appears
so callers can safely send input without racing the load.scm phase."
  (let ((cold-start (not (vnb-launch--prover-running-p))))
    (when cold-start
      (vnb--ensure-process)
      (vnb-launch--wait-for-prompt))))

(defun vnb-launch--send (str)
  "Send STR followed by a newline to the prover REPL."
  (vnb-launch--ensure-prover)
  (let ((buf (get-buffer vnb-buffer-name)))
    (when buf
      (comint-send-string buf (concat str "\n")))))

(defun vnb-launch--show-prover ()
  "Pop to the REPL/State two-pane layout."
  (let ((repl  (get-buffer vnb-buffer-name))
        (state (get-buffer vnb-state-buffer-name)))
    (when repl
      (delete-other-windows)
      (switch-to-buffer repl)
      (when state
        (split-window nil nil t)
        (set-window-buffer (next-window) state))
      (goto-char (point-max)))))

;;; -----------------------------------------------------------------------
;;; Action commands

(defun vnb-ws-start-proof (formula)
  "Start a new proof.  FORMULA is the goal string in VNB string syntax.
Switches to the Proof Workspace; the prover's state output triggers an
auto-repaint there via `vnb-state-update-hook'."
  (interactive "sFormula (string syntax): ")
  (when (string-match-p "\\`[ \t]*\\'" formula)
    (user-error "No formula given"))
  (vnb-launch--ensure-prover)
  (vnb-launch--show-proof-workspace)
  (vnb-launch--send
   (format "(sp (make-wff-from-string %S))" formula)))

(defun vnb-ws-build-formula (formula)
  "Parse FORMULA and display the result."
  (interactive "sFormula (string syntax): ")
  (when (string-match-p "\\`[ \t]*\\'" formula)
    (user-error "No formula given"))
  (vnb-launch--ensure-prover)
  (vnb-launch--send
   (format "(pp (make-wff-from-string %S))" formula))
  (vnb-launch--show-prover)
  (vnb-ws-refresh))

(defvar vnb-theorems-buffer-name "*VNB Theorems*"
  "Buffer name for the theorem/axiom catalog viewer.")

(defun vnb-ws-show-theorems ()
  "Display the theorem & axiom catalog in its own buffer.
Asks the prover to regenerate THEOREMS.md (pretty-printed formulas,
grouped proven / PSS / axioms) and opens it in `vnb-library-mode' so
section jumping and `v' (view as PDF) work the same as Browse Library
and Show PSS.  No window split, no raw s-expressions in the REPL."
  (interactive)
  (vnb-launch--ensure-prover)
  (vnb-eval-string "(catalog)")
  (let* ((path (expand-file-name "THEOREMS.md" vnb-launch--ref-dir))
         (buf  (get-buffer-create vnb-theorems-buffer-name)))
    (unless (file-exists-p path)
      (user-error "THEOREMS.md was not created -- check the Scratch Pad for errors"))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert-file-contents path))
      (goto-char (point-min))
      (setq-local default-directory vnb-launch--dir)
      (vnb-library-mode)
      (vnb-library--decorate-buffer))
    (switch-to-buffer buf)))

(defvar vnb-definitions-buffer-name "*VNB Definitions*"
  "Buffer name for the term/predicate definitions viewer.")

(defun vnb-ws-show-definitions ()
  "Display the term & predicate definitions catalog in its own buffer.
Asks the prover to regenerate DEFINITIONS.md (every constant introduced
by `def-constant' -- e.g. Cauchy sequence, convergence, completeness,
with its defining axiom pretty-printed) and opens it in
`vnb-library-mode'.  Structure predicates (`is-ring' etc.) live in
Browse Library / `d'.  No window split, no raw s-expressions."
  (interactive)
  (vnb-launch--ensure-prover)
  (vnb-eval-string "(write-definitions-md)")
  (let* ((path (expand-file-name "DEFINITIONS.md" vnb-launch--ref-dir))
         (buf  (get-buffer-create vnb-definitions-buffer-name)))
    (unless (file-exists-p path)
      (user-error "DEFINITIONS.md was not created -- check the Scratch Pad for errors"))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert-file-contents path))
      (goto-char (point-min))
      (setq-local default-directory vnb-launch--dir)
      (vnb-library-mode)
      (vnb-library--decorate-buffer))
    (switch-to-buffer buf)))

(defun vnb-pf-save-proof-script ()
  "Write the current proof's command script to a file you choose.
Emits a standalone, re-loadable block
  (sp (make-wff '<goal>))  <commands>  [ (qed 'NAME) ]
Prompts for a filename and an optional theorem name (empty omits the
trailing qed).  Works mid-proof or just after qed -- the script persists
until the next (sp)."
  (interactive)
  (vnb-launch--ensure-prover)
  (let* ((file  (expand-file-name
                 (read-file-name "Save proof script to: "
                                 (file-name-as-directory vnb-launch--dir))))
         (name  (read-string "Install-as theorem name (RET to omit qed): "))
         (named (not (string-match-p "\\`[ \t]*\\'" name)))
         (form  (if named
                    (format "(write-proof-script %S '%s)" file name)
                  (format "(write-proof-script %S)" file))))
    (vnb-eval-string form)
    (if (file-exists-p file)
        (message "Wrote proof script to %s" file)
      (user-error "Proof script not written -- is a proof in progress?  Check the Scratch Pad"))))

(defun vnb-ws-save-session ()
  "Write every proof completed this session to a file you choose.
Emits one (sp ...) <commands> (qed 'name) block per proof, in order --
the whole session as one re-loadable script."
  (interactive)
  (vnb-launch--ensure-prover)
  (let ((file (expand-file-name
               (read-file-name "Save session script to: "
                               (file-name-as-directory vnb-launch--dir)))))
    (vnb-eval-string (format "(write-session %S)" file))
    (if (file-exists-p file)
        (message "Wrote session script to %s" file)
      (user-error "Session script not written -- no proofs completed yet?  Check the Scratch Pad"))))

(defvar vnb-fingerprints-buffer-name "*VNB Fingerprints*"
  "Buffer name for the conclusion-fingerprint retrieval index viewer.")

(defun vnb-ws-show-fingerprints ()
  "Display the conclusion-fingerprint index in its own buffer.
Asks the prover to regenerate FINGERPRINT-INDEX.md (every installed result
bucketed by the depth-3 structural fingerprint of its conclusion -- the
redex skeleton the matcher fires on) and opens it in `vnb-library-mode'.
This is the ENGINE / retrieval view -- complements Browse Library (`l',
indexing by structure).  No window split, no raw s-expressions."
  (interactive)
  (vnb-launch--ensure-prover)
  (vnb-eval-string "(fingerprint-index)")
  (let* ((path (expand-file-name "FINGERPRINT-INDEX.md" vnb-launch--ref-dir))
         (buf  (get-buffer-create vnb-fingerprints-buffer-name)))
    (unless (file-exists-p path)
      (user-error "FINGERPRINT-INDEX.md was not created -- check the Scratch Pad for errors"))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert-file-contents path))
      (goto-char (point-min))
      (setq-local default-directory vnb-launch--dir)
      (vnb-library-mode)
      (vnb-library--decorate-buffer))
    (switch-to-buffer buf)))

(defvar vnb-calculator-buffer-name "*VNB Calculator*"
  "Buffer name for the kid-facing arithmetic calculator tape.")

(defun vnb-ws-calculator (expr)
  "Evaluate a plain arithmetic expression and append it to a calculator tape.
Kid-facing front end to the prover's (calc ...) evaluator: type something
like 2 + 3 + 5 (also 10 - 4, 2 * 3 * 5) and the answer is recorded in the
*VNB Calculator* buffer as `expr = answer'.  Only ground arithmetic;
(calc ...) is vnb-guarded, so a nonsense entry can't wedge the prover."
  (interactive "sCalculate (e.g. 2 + 3 + 5): ")
  (when (string-match-p "\\`[ \t]*\\'" expr)
    (user-error "Nothing to calculate"))
  (vnb-launch--ensure-prover)
  (let* ((e    (vnb-launch--dequote (string-trim expr)))
         (raw  (vnb-eval-string (format "(calc %S)" e)))
         (ans  (and raw (string-trim raw)))
         (ok   (and ans (string-match-p "\\`-?[0-9][0-9/.eE+-]*\\'" ans)))
         (line (if ok
                   (format "  %s  =  %s\n" e ans)
                 (format "  %s  =  ?   (use numbers with  +  -  *)\n" e)))
         (buf  (get-buffer-create vnb-calculator-buffer-name)))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (when (= (point-min) (point-max))
          (setq-local mode-line-format vnb-launch--mode-line-format)
          (insert (propertize "  VNB Calculator\n" 'face 'vnb-title))
          (insert (propertize (concat "  " (make-string 30 ?─) "\n\n")
                              'face 'vnb-accent)))
        (goto-char (point-max))
        (insert (propertize line 'face (if ok 'vnb-goal 'vnb-dim)))
        (goto-char (point-max)))
      (unless buffer-read-only (setq buffer-read-only t)))
    (display-buffer buf)
    (when ok (message "%s = %s" e ans))))

(defvar vnb-pss-buffer-name "*VNB PSS*"
  "Buffer name for the Proof Support Set viewer.")

(defun vnb-ws-show-pss ()
  "Display Proof Support Set entries in a dedicated buffer.
Asks the prover to regenerate PSS.md with pretty-printed formulas,
then opens it in `vnb-library-mode' so section jumping works the same
way as Browse Library."
  (interactive)
  (vnb-launch--ensure-prover)
  (vnb-eval-string "(write-pss-md)")
  (let* ((path (expand-file-name "PSS.md" vnb-launch--ref-dir))
         (buf  (get-buffer-create vnb-pss-buffer-name)))
    (unless (file-exists-p path)
      (user-error "PSS.md was not created -- check the Scratch Pad for errors"))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert-file-contents path))
      (goto-char (point-min))
      (setq-local default-directory vnb-launch--dir)
      (vnb-library-mode)
      (vnb-library--decorate-buffer))
    (switch-to-buffer buf)))

;;; -----------------------------------------------------------------------
;;; View formula at point as a PDF.  Asks the prover to render the named
;;; PSS / theorem entry as LaTeX, compiles via pdflatex, and opens the
;;; resulting (auto-cropped) PDF in `doc-view-mode' for inline display.

(defconst vnb-tex-cache-dir
  (expand-file-name "vnb/tex/"
                    (or (getenv "XDG_CACHE_HOME") "~/.cache/"))
  "Directory where rendered .tex / .pdf files for VNB formulas live.")

(defun vnb-tex--ensure-cache-dir ()
  (unless (file-directory-p vnb-tex-cache-dir)
    (make-directory vnb-tex-cache-dir t)))

(defun vnb-tex--name-at-point ()
  "Return the PSS/theorem name of the markdown section enclosing point.
Scans back for the nearest `^### NAME' line and returns NAME (trimmed),
or nil if none is found."
  (save-excursion
    (end-of-line)
    (when (re-search-backward "^### \\(.+?\\)\\s-*$" nil t)
      (let ((s (match-string-no-properties 1)))
        (and s (replace-regexp-in-string "\\s-+\\'" "" s))))))

(defun vnb-view-as-pdf (&optional name)
  "Render the PSS / theorem at point as a PDF and display it.
With prefix arg, prompt for NAME instead of using point.  The .tex
source and .pdf output land in `vnb-tex-cache-dir'.

In a `vnb-library-mode' buffer (Browse Library or *VNB PSS*), the
default NAME is taken from the markdown `### name' header enclosing
point."
  (interactive
   (list (or (and (not current-prefix-arg) (vnb-tex--name-at-point))
             (read-string "VNB formula name: "
                          (vnb-tex--name-at-point)))))
  (vnb-launch--ensure-prover)
  (unless (and name (not (string-empty-p name)))
    (user-error "No formula name given"))
  (vnb-tex--ensure-cache-dir)
  (let* ((tex-path (expand-file-name (concat name ".tex") vnb-tex-cache-dir))
         (pdf-path (expand-file-name (concat name ".pdf") vnb-tex-cache-dir))
         (scheme   (format "(write-formula-tex '%s \"%s\")" name tex-path))
         (result   (vnb-eval-string scheme)))
    (unless (file-exists-p tex-path)
      (user-error
       "TeX file was not written for `%s' -- prover replied: %s"
       name (string-trim (or result ""))))
    (let* ((default-directory vnb-tex-cache-dir)
           (log-buf (get-buffer-create " *vnb-pdflatex*"))
           (status  (with-current-buffer log-buf
                      (erase-buffer)
                      (call-process "pdflatex" nil log-buf nil
                                    "-interaction=batchmode"
                                    "-halt-on-error"
                                    tex-path))))
      (unless (and (= status 0) (file-exists-p pdf-path))
        (pop-to-buffer log-buf)
        (user-error "pdflatex failed for `%s' (status %d); see log buffer"
                    name status))
      (let ((buf (find-file-other-window pdf-path)))
        (with-current-buffer buf
          (when (fboundp 'doc-view-fit-window-to-page)
            (ignore-errors (doc-view-fit-window-to-page))))
        (message "Rendered %s" name)))))

;;; -----------------------------------------------------------------------
;;; Inline TeX -> PNG rendering (latex -> dvipng), ported from the user's
;;; Maxima pipeline.  Replaces each $...$ span in a buffer with an inline
;;; image.  No pdflatex / doc-view: dvipng is fast and the PNGs are cached
;;; under vnb-tex-cache-dir/render keyed by (tex, fg colour, scale).

(defcustom vnb-tex-scale 0.7
  "Magnification for inline rendered formulas.  Higher = larger PNGs."
  :type 'number :group 'vnb)

(defun vnb-tex--dpi ()
  "Render resolution, scaled to the current default font size."
  (max 90 (round (* vnb-tex-scale
                    (/ (face-attribute 'default :height nil t) 10.0)
                    10))))

(defun vnb-tex--color (name)
  "Emacs colour NAME as a dvipng \"rgb r g b\" spec (0..1 components)."
  (let ((rgb (and name (color-name-to-rgb name))))
    (if rgb (apply #'format "rgb %.3f %.3f %.3f" rgb) "rgb 0 0 0")))

(defun vnb-tex--latex-document (tex)
  "A standalone LaTeX document rendering math string TEX."
  (concat
   "\\documentclass[border=2pt]{standalone}\n"
   "\\usepackage{amsmath,amssymb}\n"
   "\\begin{document}\n"
   "$\\displaystyle " tex "$\n"
   "\\end{document}\n"))

(defun vnb-tex--render-one (tex)
  "Render math string TEX to a cached PNG; return its path, or nil on failure."
  (vnb-tex--ensure-cache-dir)
  (let* ((fg  (vnb-tex--color (face-attribute 'default :foreground nil t)))
         (dpi (vnb-tex--dpi))
         (dir (expand-file-name "render" vnb-tex-cache-dir))
         (key (secure-hash 'md5 (format "%s|%s|%s" tex fg dpi)))
         (png (expand-file-name (concat key ".png") dir)))
    (unless (file-directory-p dir) (make-directory dir t))
    (if (file-exists-p png)
        png
      (let* ((base (expand-file-name key dir))
             (tex-file (concat base ".tex"))
             (dvi-file (concat base ".dvi"))
             (default-directory dir)
             (log (get-buffer-create " *vnb-tex*")))
        (with-temp-file tex-file (insert (vnb-tex--latex-document tex)))
        (with-current-buffer log (erase-buffer))
        (and (eq 0 (call-process "latex" nil log nil
                                 "-interaction=batchmode" "-halt-on-error"
                                 "-output-directory" dir tex-file))
             (file-exists-p dvi-file)
             (eq 0 (call-process "dvipng" nil log nil
                                 "-D" (number-to-string dpi)
                                 "-T" "tight" "-bg" "Transparent" "-fg" fg
                                 "-q" "-o" png dvi-file))
             (file-exists-p png)
             png)))))

(defvar-local vnb-tex--rendered nil
  "Non-nil when the current buffer's $...$ spans are showing as images.")

(defun vnb-tex-render-buffer ()
  "Replace every $...$ span in the current buffer with an inline image.
The TeX source is kept underneath the image (as the `vnb-tex' property)
so `vnb-tex-toggle-source' can reveal it."
  (when (display-images-p)
    (let ((inhibit-read-only t)
          (n 0))
      (save-excursion
        (goto-char (point-min))
        (while (re-search-forward "\\$\\([^$\n]+\\)\\$" nil t)
          (let* ((beg (match-beginning 0))
                 (end (match-end 0))
                 (tex (match-string-no-properties 1))
                 (png (ignore-errors (vnb-tex--render-one tex))))
            (when (and png (file-exists-p png))
              (add-text-properties
               beg end
               (list 'display (create-image png 'png nil :ascent 'center)
                     'vnb-tex tex 'help-echo tex 'rear-nonsticky t))
              (setq n (1+ n))))))
      (setq vnb-tex--rendered t)
      n)))

(defun vnb-tex--remove-images ()
  "Strip image display properties added by `vnb-tex-render-buffer'."
  (let ((inhibit-read-only t) (pos (point-min)) nxt)
    (while (< pos (point-max))
      (setq nxt (or (next-single-property-change pos 'vnb-tex) (point-max)))
      (when (get-text-property pos 'vnb-tex)
        (remove-text-properties pos nxt '(display nil)))
      (setq pos nxt))))

(defun vnb-tex-toggle-source ()
  "Toggle between rendered formulas and their raw TeX source."
  (interactive)
  (if vnb-tex--rendered
      (progn (vnb-tex--remove-images)
             (setq vnb-tex--rendered nil)
             (message "Showing TeX source (press r to re-render)"))
    (vnb-tex-render-buffer)
    (message "Showing rendered formulas")))

;;; -----------------------------------------------------------------------
;;; Structure cards: a rendered "card" per structure (operations, the
;;; characteristic law, view-as relations) plus an editable notes file.
;;; The generated half comes from the prover (`write-structure-card-md');
;;; the notes half lives in `vnb-structure-notes-dir' and is the user's.

(defcustom vnb-structure-notes-dir
  (expand-file-name "structure-notes" vnb-launch--dir)
  "Directory of user-editable per-structure note files (NAME.md)."
  :type 'directory :group 'vnb)

(defvar-local vnb-structure--name nil
  "The structure name shown in this card buffer.")

(defface vnb-card-h1 '((t :inherit vnb-title))
  "Face for a structure card's top heading." :group 'vnb)
(defface vnb-card-h2 '((t :inherit vnb-heading :weight bold))
  "Face for a structure card's section headings." :group 'vnb)
(defface vnb-card-code '((t :inherit font-lock-constant-face))
  "Face for inline `code` in a structure card." :group 'vnb)

(defvar vnb-structure-card-font-lock-keywords
  '(("^\\(# \\)\\(.*\\)$"
     (1 '(face nil invisible vnb-md)) (2 'vnb-card-h1))
    ("^\\(##+ \\)\\(.*\\)$"
     (1 '(face nil invisible vnb-md)) (2 'vnb-card-h2))
    ("\\(\\*\\*\\)\\([^*\n]+?\\)\\(\\*\\*\\)"
     (1 '(face nil invisible vnb-md)) (2 'bold) (3 '(face nil invisible vnb-md)))
    ("\\(`\\)\\([^`\n]+?\\)\\(`\\)"
     (1 '(face nil invisible vnb-md)) (2 'vnb-card-code) (3 '(face nil invisible vnb-md))))
  "Light markdown fontification for VNB structure cards.")

(defvar vnb-structure-card-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m "e" 'vnb-structure-edit-notes)
    (define-key m "g" 'vnb-structure-refresh-card)
    (define-key m "r" 'vnb-tex-toggle-source)
    (define-key m "d" 'vnb-describe-structure)
    (define-key m "m" 'vnb-structure-manual)
    (define-key m "G" 'vnb-structure-graph-html)
    (define-key m "q" 'quit-window)
    (define-key m "?" 'describe-mode)
    m)
  "Keymap for `vnb-structure-card-mode'.")

(define-derived-mode vnb-structure-card-mode special-mode "VNB-Card"
  "Major mode for a rendered VNB structure card.
\\{vnb-structure-card-mode-map}"
  (setq buffer-read-only t truncate-lines nil)
  (setq-local font-lock-extra-managed-props '(invisible))
  (setq font-lock-defaults '(vnb-structure-card-font-lock-keywords t))
  (add-to-invisibility-spec 'vnb-md)
  (vnb-launch--apply-faces))

(defun vnb-structure--names ()
  "Known structure names (lower-case strings) fetched from the prover."
  (vnb-launch--ensure-prover)
  (let ((raw (vnb-eval-string "(known-structures)")))
    (when (and raw (string-match "(\\(.*\\))" raw))
      (condition-case nil
          (mapcar (lambda (s) (downcase (format "%s" s)))
                  (car (read-from-string raw)))
        (error nil)))))

(defun vnb-structure--notes-path (name)
  (expand-file-name (concat (downcase name) ".md") vnb-structure-notes-dir))

(defun vnb-structure--insert-notes (name)
  "Insert the Notes section for NAME at point (file contents or a stub)."
  (let ((path (vnb-structure--notes-path name)))
    (insert "\n## Notes\n\n")
    (if (file-exists-p path)
        (insert (with-temp-buffer (insert-file-contents path) (buffer-string)))
      (insert (format
               (concat "None yet.  Press `e` to add usage hints, gotchas, or\n"
                       "when to reach for this structure.\n\n"
                       "They live in `%s` and are yours to edit.\n")
               (file-relative-name path vnb-launch--dir))))))

(defun vnb-describe-structure (name)
  "Show a rendered reference card for structure NAME.
Operations, the characteristic law, and view-as relations are rendered
from the live theory; your notes from `vnb-structure-notes-dir' are
spliced underneath.  Press `e' to edit the notes, `g' to refresh, `r'
to toggle TeX source."
  (interactive
   (list (completing-read
          "Describe structure: " (or (vnb-structure--names) '()) nil nil
          (and (derived-mode-p 'vnb-library-mode 'vnb-structure-card-mode)
               (ignore-errors (vnb-tex--name-at-point))))))
  (setq name (downcase (string-trim name)))
  (when (string-empty-p name) (user-error "No structure name given"))
  (vnb-launch--ensure-prover)
  (vnb-tex--ensure-cache-dir)
  (let ((card-path (expand-file-name (concat "card-" name ".md") vnb-tex-cache-dir)))
    (vnb-eval-string (format "(write-structure-card-md '%s \"%s\")" name card-path))
    (unless (file-exists-p card-path)
      (user-error "No card generated for `%s' (unknown structure?)" name))
    (let ((buf (get-buffer-create (format "*VNB Structure: %s*" name))))
      (with-current-buffer buf
        (let ((inhibit-read-only t))
          (vnb-structure-card-mode)
          (setq-local vnb-structure--name name)
          (setq-local default-directory vnb-launch--dir)
          (erase-buffer)
          (insert-file-contents card-path)
          (goto-char (point-max))
          (vnb-structure--insert-notes name)
          (font-lock-ensure)
          (vnb-tex-render-buffer)
          (goto-char (point-min))))
      (switch-to-buffer buf)
      (delete-other-windows))))

(defun vnb-structure-edit-notes ()
  "Open (creating if needed) the editable notes file for this card."
  (interactive)
  (let ((name (or vnb-structure--name (ignore-errors (vnb-tex--name-at-point)))))
    (unless name (user-error "No structure in this buffer"))
    (unless (file-directory-p vnb-structure-notes-dir)
      (make-directory vnb-structure-notes-dir t))
    (let* ((path (vnb-structure--notes-path name))
           (new  (not (file-exists-p path))))
      (find-file-other-window path)
      (when (and new (= (point-min) (point-max)))
        (insert (format (concat "<!-- Notes for %s.  Plain prose / markdown, 2-3 short paragraphs.\n"
                                "     Usage hints, gotchas, when to reach for this structure. -->\n\n")
                        name)))
      (message "Edit and save, then press g in the card buffer to refresh"))))

(defun vnb-structure-refresh-card ()
  "Regenerate and re-render the current structure card."
  (interactive)
  (if vnb-structure--name
      (vnb-describe-structure vnb-structure--name)
    (user-error "Not in a structure card")))

(defun vnb-structure-manual ()
  "Render the whole structure library into one reference buffer."
  (interactive)
  (vnb-launch--ensure-prover)
  (vnb-tex--ensure-cache-dir)
  (let ((path (expand-file-name "structure-manual.md" vnb-tex-cache-dir)))
    (message "Generating structure manual...")
    (vnb-eval-string (format "(write-structure-manual-md \"%s\")" path) 60)
    (unless (file-exists-p path) (user-error "Manual was not generated"))
    (let ((buf (get-buffer-create "*VNB Structure Manual*")))
      (with-current-buffer buf
        (let ((inhibit-read-only t))
          (vnb-structure-card-mode)
          (setq-local default-directory vnb-launch--dir)
          (erase-buffer)
          (insert-file-contents path)
          (font-lock-ensure)
          (message "Rendering formulas (first run is slow; cached after)...")
          (vnb-tex-render-buffer)
          (goto-char (point-min))))
      (switch-to-buffer buf)
      (delete-other-windows)
      (message "Structure manual ready"))))

;;; -----------------------------------------------------------------------
;;; Structure-relationship graph: a Graphviz figure of refines (solid) and
;;; view-as (dashed) edges among structures.  The prover writes the .dot
;;; (`write-structure-graph-dot'); `dot -Tpng' renders it; we show the PNG
;;; inline, scaled to the window.

(defvar vnb-structure-graph-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m "g" 'vnb-structure-graph)
    (define-key m "d" 'vnb-describe-structure)
    (define-key m "m" 'vnb-structure-manual)
    (define-key m "q" 'quit-window)
    (define-key m "?" 'describe-mode)
    m)
  "Keymap for `vnb-structure-graph-mode'.")

(define-derived-mode vnb-structure-graph-mode special-mode "VNB-Graph"
  "Major mode for the rendered VNB structure-relationship graph.
\\{vnb-structure-graph-mode-map}"
  (setq buffer-read-only t truncate-lines nil)
  (vnb-launch--apply-faces))

(defun vnb-structure--graph-png ()
  "Generate the structure-relationship graph PNG (prover .dot + `dot').
Return the PNG path, or signal a `user-error'."
  (vnb-launch--ensure-prover)
  (vnb-tex--ensure-cache-dir)
  (unless (executable-find "dot")
    (user-error "Graphviz `dot' not found on PATH -- install graphviz"))
  (let ((dot (expand-file-name "structure-graph.dot" vnb-tex-cache-dir))
        (png (expand-file-name "structure-graph.png" vnb-tex-cache-dir))
        (log (get-buffer-create " *vnb-dot*")))
    (vnb-eval-string (format "(write-structure-graph-dot \"%s\")" dot))
    (unless (file-exists-p dot)
      (user-error "Graph .dot was not generated by the prover"))
    (with-current-buffer log (erase-buffer))
    (unless (eq 0 (call-process "dot" nil log nil "-Tpng" "-o" png dot))
      (user-error "dot failed to render the graph (see ` *vnb-dot*')"))
    (unless (file-exists-p png)
      (user-error "Graph PNG was not produced"))
    png))

(defun vnb-structure-graph ()
  "Render the structure-relationship graph (refines + view-as) inline.
Solid arrows are `refines' (specialisation -> parent); dashed amber
arrows are `view-as' component maps, labelled with the view name.
Press `g' to refresh, `q' to quit."
  (interactive)
  (let ((png (vnb-structure--graph-png))
        (buf (get-buffer-create "*VNB Structure Graph*")))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (vnb-structure-graph-mode)
        (setq-local default-directory vnb-launch--dir)
        (erase-buffer)
        (insert (propertize "  Structure relationships\n" 'face 'vnb-card-h1))
        (insert (propertize
                 (concat "  solid = refines (child -> parent)    "
                         "dashed amber = view-as (labelled)\n\n")
                 'face 'vnb-dim))))
    (switch-to-buffer buf)
    (delete-other-windows)
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (goto-char (point-max))
        (if (display-images-p)
            (progn
              (insert-image
               (create-image png 'png nil
                             :max-width  (max 200 (- (window-body-width nil t) 24))
                             :max-height (max 200 (- (window-body-height nil t) 72))
                             :ascent 'center))
              (insert "\n"))
          (insert (propertize (format "  (no image display here; PNG at %s)\n" png)
                              'face 'vnb-dim)))
        (goto-char (point-min))))))

(defcustom vnb-graph-browser nil
  "Which browser opens the clickable structure graph.
Affects only `vnb-structure-graph-html'; your global browsing is untouched.
  nil      -- the `browse-url' default (your system default browser).
  string   -- an executable name or path, opened via `browse-url-generic'
              (e.g. \"chromium\", \"epiphany\", \"surf\", \"qutebrowser\").
  function -- used as `browse-url-browser-function' (e.g. #\\='eww-browse-url
              to view inside Emacs -- note: EWW renders the SVG as a static
              image, so graph NODES aren't clickable there; the text reference
              links and #anchors still work)."
  :type '(choice (const :tag "System default" nil)
                 (string :tag "Browser executable")
                 (function :tag "browse-url function"))
  :group 'vnb)

(defun vnb--browse-graph (url)
  "Open URL according to `vnb-graph-browser'."
  (cond
   ((functionp vnb-graph-browser) (funcall vnb-graph-browser url))
   ((and (stringp vnb-graph-browser) (> (length vnb-graph-browser) 0))
    (let ((browse-url-generic-program    vnb-graph-browser)
          (browse-url-browser-function   #'browse-url-generic))
      (browse-url url)))
   (t (browse-url url))))

;;; The inline PNG above is a flat raster -- nodes aren't clickable.  The
;;; mouse-sensitive graph is a self-contained HTML page (one inlined SVG plus a
;;; per-structure reference section): click a node/arrow and the page scrolls to
;;; that entry.  reference/build-graph-html.py builds it from the prover's .dot
;;; (it runs `dot -Tsvg' itself).  We regenerate both, then open in a browser
;;; (the one chosen by `vnb-graph-browser').
(defun vnb-structure-graph-html ()
  "Open the mouse-sensitive structure graph in a web browser.
Regenerates reference/structure-graph.{dot,html} from the live prover,
then `browse-url's the HTML.  Click a node or arrow to scroll to that
structure's entry (slots, views-out, refines) or the all-views table."
  (interactive)
  (vnb-launch--ensure-prover)
  (unless (executable-find "dot")
    (user-error "Graphviz `dot' not found on PATH -- install graphviz"))
  (unless (executable-find "python3")
    (user-error "`python3' not found on PATH -- needed to build the graph HTML"))
  (let ((py   (expand-file-name "build-graph-html.py" vnb-launch--ref-dir))
        (html (expand-file-name "structure-graph.html" vnb-launch--ref-dir))
        (log  (get-buffer-create " *vnb-graph-html*")))
    ;; 1. rewrite the .dot from the live prover (slots/views/refines current)
    (vnb-eval-string "(structure-graph-dot-file)")
    ;; 2. build the self-contained HTML (the script runs `dot -Tsvg' internally)
    (with-current-buffer log (erase-buffer))
    (let ((default-directory vnb-launch--ref-dir))
      (unless (eq 0 (call-process "python3" nil log nil py))
        (user-error "build-graph-html.py failed (see ` *vnb-graph-html*')")))
    (unless (file-exists-p html)
      (user-error "structure-graph.html was not produced"))
    ;; 3. hand off to the chosen browser, where the SVG's clicks are live
    (vnb--browse-graph (concat "file://" html))
    (message "Opened clickable structure graph in %s: %s"
             (or vnb-graph-browser "default browser") html)))

;;; -----------------------------------------------------------------------
;;; Suggest Forward Moves: scan the current proof state's assumptions
;;; for patterns that license a forward derivation (e.g. pointwise
;;; equality → fun-domain-extensionality).  Result is a markdown report
;;; in a dedicated buffer.

(defvar vnb-suggestions-buffer-name "*VNB Suggestions*"
  "Buffer name for the forward-move suggestions report.")

(defun vnb-suggest-forward-moves ()
  "Scan current proof state's assumptions for applicable forward moves.
Asks the prover to (re)generate the suggestions report, then displays
it in `vnb-suggestions-buffer-name'.  Each suggestion names the
assumption, the matched pattern, and the foundational axiom that the
shape licenses (currently: `fun-domain-extensionality')."
  (interactive)
  (vnb-launch--ensure-prover)
  (let* ((path (expand-file-name "vnb/tex/suggestions.md"
                                  (or (getenv "XDG_CACHE_HOME") "~/.cache/")))
         (scheme (format "(write-suggestions-md \"%s\")" path))
         (_ (vnb-tex--ensure-cache-dir))
         (result (vnb-eval-string scheme))
         (buf (get-buffer-create vnb-suggestions-buffer-name)))
    (unless (file-exists-p path)
      (user-error "Suggestions file was not written -- prover replied: %s"
                  (string-trim (or result ""))))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert-file-contents path))
      (goto-char (point-min))
      (setq-local default-directory vnb-launch--dir)
      (vnb-library-mode)
      (vnb-library--decorate-buffer))
    (display-buffer buf)))

;;; -----------------------------------------------------------------------
;;; Browse Library: open STRUCTURE-INDEX.md in a side window with simple
;;; markdown-aware navigation.  No external package dependency.

(defvar vnb-library-buffer-name "*VNB Library*"
  "Buffer holding the structure-grouped library index for browsing.")

;;; Match-list state for step-through navigation when a search returned
;;; multiple sections.  Buffer-local in the library buffer.
(defvar-local vnb-library--matches nil
  "List of (NAME . POSITION) for the current narrowed search, or nil.")
(defvar-local vnb-library--match-index 0
  "Index into `vnb-library--matches'.")

(defvar vnb-library-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m (kbd "RET")       'vnb-library-follow)
    (define-key m (kbd "TAB")       'vnb-library-next-link)
    (define-key m (kbd "<backtab>") 'vnb-library-prev-link)
    (define-key m "j"               'vnb-library-jump)
    (define-key m (kbd "<right>")   'vnb-library-next-match)
    (define-key m (kbd "<left>")    'vnb-library-prev-match)
    (define-key m (kbd "M-n")       'vnb-library-next-match)
    (define-key m (kbd "M-p")       'vnb-library-prev-match)
    (define-key m "n"               'vnb-library-next-section)
    (define-key m "p"               'vnb-library-prev-section)
    (define-key m "w"               'vnb-library-widen)
    (define-key m "g"               'vnb-library-refresh)
    (define-key m "v"               'vnb-view-as-pdf)
    (define-key m "d"               'vnb-describe-structure)
    (define-key m "q"               'quit-window)
    (define-key m "?"               'describe-mode)
    m)
  "Keymap for `vnb-library-mode'.")

;;; Font-lock keywords give the otherwise-plain markdown a coloured,
;;; structured look.  Order matters (earlier rules win).
(defvar vnb-library-font-lock-keywords
  `(
    ;; `### name`  section headings (matched first, so the line is fully styled)
    ("^### \\(.+\\)$"
     (0 'vnb-library-section)
     (1 'vnb-library-section))
    ;; `## name`   top-level headings (Table of contents, View-as block, etc.)
    ("^## \\(.+\\)$"
     (0 'vnb-library-toc))
    ;; Markdown links: `[label](target)`
    ("\\(\\[\\)\\([^]]+\\)\\(\\](\\)\\([^)]+\\)\\()\\)"
     (1 'vnb-dim)
     (2 'vnb-library-link)
     (3 'vnb-dim)
     (4 'vnb-dim)
     (5 'vnb-dim))
    ;; Inline backtick code spans
    ("`[^`\n]+`"
     0 'vnb-library-code)
    ;; *emphasis* (not `**bold**`, plain markdown italic)
    ("\\(\\*[^*\n][^*\n]*\\*\\)"
     1 'vnb-library-emphasis))
  "Font-lock keywords for `vnb-library-mode'.")

(define-derived-mode vnb-library-mode special-mode "VNB-Library"
  "Major mode for browsing STRUCTURE-INDEX.md.
\\<vnb-library-mode-map>
\\[vnb-library-jump]      prompt (completing-read) for a section, narrow to all matches.
\\[vnb-library-follow]      follow the link at point (anchor jump or open source file).
\\[vnb-library-next-link] / \\[vnb-library-prev-link]   next / previous link.
\\[vnb-library-next-match] / \\[vnb-library-prev-match]   next / previous *search match*
       (active after \\[vnb-library-jump] returned more than one section).
\\[vnb-library-next-section] / \\[vnb-library-prev-section]   next / previous `### ' section
       (operates on the unnarrowed buffer).
\\[vnb-library-widen]      widen: drop the narrowing, return to the full index.
\\[vnb-library-refresh]      regenerate from the live prover (catalog) and re-read.
\\[quit-window]      bury the buffer."
  (setq buffer-read-only t)
  (setq truncate-lines nil)
  (vnb-launch--apply-faces)
  (setq-local font-lock-defaults
              '(vnb-library-font-lock-keywords nil nil nil nil))
  (font-lock-mode 1))

(defun vnb-library--index-path ()
  "Absolute path to the STRUCTURE-INDEX.md file."
  (expand-file-name "STRUCTURE-INDEX.md" vnb-launch--ref-dir))

(defvar vnb-library--link-keymap
  (let ((m (make-sparse-keymap)))
    (define-key m [mouse-1]   'vnb-library-follow-mouse)
    (define-key m [mouse-2]   'vnb-library-follow-mouse)
    (define-key m (kbd "RET") 'vnb-library-follow)
    m)
  "Keymap attached to markdown-link text spans in the library buffer.")

(defun vnb-library-follow-mouse (event)
  "Mouse-clicked variant of `vnb-library-follow' — sets point, then follows."
  (interactive "e")
  (mouse-set-point event)
  (vnb-library-follow))

(defun vnb-library--decorate-buffer ()
  "Make the markdown buffer interactive: hide `<a id=...>` anchors,
turn each `[label](target)` into a clickable region.  Idempotent."
  (let ((inhibit-read-only t))
    (save-excursion
      ;; (1) Hide the inline <a id="..."></a> anchors -- they're invisible in
      ;; rendered markdown but visible as ASCII clutter here.  Use the
      ;; `invisible' text property; Emacs honours it for display.
      (goto-char (point-min))
      (while (re-search-forward "<a id=\"[^\"]*\"></a>\n?" nil t)
        (add-text-properties (match-beginning 0) (match-end 0)
                             '(invisible t intangible t)))
      ;; (2) Make every [label](target) a clickable link.
      (goto-char (point-min))
      (while (re-search-forward "\\[\\([^]]+\\)\\](\\([^)]+\\))" nil t)
        (let ((beg    (match-beginning 0))
              (end    (match-end 0))
              (target (match-string-no-properties 2)))
          (add-text-properties beg end
            `(mouse-face highlight
              help-echo ,(format "Follow link: %s" target)
              keymap ,vnb-library--link-keymap
              follow-link t
              vnb-link-target ,target)))))
    (set-buffer-modified-p nil)))

(defun vnb-library--update-header-line ()
  "Set `header-line-format' to a visible navigation strip when a match
list is active, or clear it otherwise."
  (setq header-line-format
        (cond
         ((null vnb-library--matches) nil)
         (t (let ((n (length vnb-library--matches))
                  (i (1+ vnb-library--match-index)))
              (format
               "  ◀ Prev (M-p / ←)    [%d/%d]  %s    Next (M-n / →) ▶    [w] widen    [q] bury"
               i n (car (nth (1- i) vnb-library--matches))))))))

(defun vnb-library--collect-sections ()
  "Return list of (NAME . POSITION) for every `### ' heading.  Widens first."
  (save-excursion
    (save-restriction
      (widen)
      (goto-char (point-min))
      (let ((sections '()))
        (while (re-search-forward "^### \\(.+\\)$" nil t)
          (push (cons (match-string-no-properties 1)
                      (line-beginning-position))
                sections))
        (nreverse sections)))))

(defun vnb-library--narrow-to-section (pos)
  "Narrow to the `### ' section starting at POS, ending at the next
`### ', `## ', or end of buffer.  POS may sit before the heading line."
  (widen)
  (goto-char pos)
  (beginning-of-line)
  (let ((start (point))
        (end (save-excursion
               (forward-line 1)
               (if (re-search-forward "^\\(?:### \\|## \\)" nil t)
                   (line-beginning-position)
                 (point-max)))))
    (narrow-to-region start end)
    (goto-char start)
    (recenter 0)))

(defun vnb-library--show-current-match ()
  "Narrow to the section indexed by `vnb-library--match-index' and update
the header-line nav strip."
  (when (and vnb-library--matches
             (>= vnb-library--match-index 0)
             (< vnb-library--match-index (length vnb-library--matches)))
    (let* ((entry (nth vnb-library--match-index vnb-library--matches))
           (pos   (cdr entry)))
      (vnb-library--narrow-to-section pos)
      (vnb-library--update-header-line)
      (force-mode-line-update))))

(defun vnb-library-jump (&optional initial)
  "Prompt for a section in the library and narrow to all matching sections.

Completion is substring/flex against section headings.  If the typed
input is the exact name of a section, that one section is shown.
Otherwise every section whose name contains the input (case-insensitive)
is collected into a match list; the first is shown narrowed and \\[vnb-library-next-match] /
\\[vnb-library-prev-match] step through the rest.  \\[vnb-library-widen] returns to the full index.

INITIAL is an optional starting input for the prompt."
  (interactive)
  (let* ((sections (vnb-library--collect-sections))
         (names    (mapcar #'car sections))
         (completion-ignore-case t)
         (input (completing-read
                 (format "Library section (%d): " (length names))
                 names nil nil initial))
         (exact (assoc input sections))
         (matches
          (cond
           (exact (list exact))
           (t
            (let ((case-fold-search t)
                  (re (regexp-quote input)))
              (cl-remove-if-not
               (lambda (e) (string-match-p re (car e)))
               sections))))))
    (cond
     ((null matches)
      (message "No section matches \"%s\"" input))
     (t
      (setq vnb-library--matches matches
            vnb-library--match-index 0)
      (vnb-library--show-current-match)))))

(defun vnb-library-next-match ()
  "Move to the next match in the active library search."
  (interactive)
  (cond
   ((null vnb-library--matches)
    (message "No active library-search match list."))
   ((= 1 (length vnb-library--matches))
    (message "Only one match."))
   (t
    (setq vnb-library--match-index
          (mod (1+ vnb-library--match-index)
               (length vnb-library--matches)))
    (vnb-library--show-current-match))))

(defun vnb-library-prev-match ()
  "Move to the previous match in the active library search."
  (interactive)
  (cond
   ((null vnb-library--matches)
    (message "No active library-search match list."))
   ((= 1 (length vnb-library--matches))
    (message "Only one match."))
   (t
    (setq vnb-library--match-index
          (mod (1- vnb-library--match-index)
               (length vnb-library--matches)))
    (vnb-library--show-current-match))))

(defun vnb-library-widen ()
  "Remove narrowing, drop the current match list, show the full index."
  (interactive)
  (widen)
  (setq vnb-library--matches nil
        vnb-library--match-index 0)
  (vnb-library--update-header-line)
  (goto-char (point-min))
  (message "Widened.  Full index visible."))

(defun vnb-ws-browse-library ()
  "Open STRUCTURE-INDEX.md and prompt for a section to view.

If the file doesn't exist yet, asks to ensure a prover is running and call
catalog once so it gets written.  After opening, immediately calls
`vnb-library-jump' for a completing-read prompt on section headings.
Type a substring (e.g. `metric'); multiple matches are step-throughable
with `M-n' / `M-p' (or → / ←).  Press `w' inside the buffer to widen."
  (interactive)
  (let ((path (vnb-library--index-path)))
    (unless (file-exists-p path)
      (if (y-or-n-p "STRUCTURE-INDEX.md not found.  Start the prover and run (catalog)? ")
          (progn (vnb-launch--ensure-prover)
                 (vnb-launch--send "(catalog)")
                 (message "Wait a few seconds, then press l again."))
        (user-error "STRUCTURE-INDEX.md not found at %s" path)))
    (when (file-exists-p path)
      (let ((buf (get-buffer-create vnb-library-buffer-name)))
        (with-current-buffer buf
          (let ((inhibit-read-only t))
            (erase-buffer)
            (insert-file-contents path))
          (goto-char (point-min))
          (setq-local default-directory vnb-launch--dir)
          (vnb-library-mode)
          (vnb-library--decorate-buffer))
        ;; Reuse the current window; user asked not to split.
        (switch-to-buffer buf)
        (with-current-buffer buf
          (call-interactively 'vnb-library-jump))))))

(defun vnb-library-refresh ()
  "Ask the running prover to regenerate STRUCTURE-INDEX.md, then re-read it."
  (interactive)
  (vnb-launch--ensure-prover)
  (vnb-launch--send "(catalog)")
  (message "Regenerating STRUCTURE-INDEX.md — press g again in a few seconds to reload.")
  (let ((path (vnb-library--index-path)))
    (when (file-exists-p path)
      (let ((pos (point))
            (inhibit-read-only t))
        (widen)
        (erase-buffer)
        (insert-file-contents path)
        (goto-char (min pos (point-max))))
      (vnb-library--decorate-buffer)
      (setq vnb-library--loaded-mtime (vnb-library--file-mtime path)))))

(defun vnb-library--link-at-point ()
  "If point is on a markdown link `[label](target)`, return target.
Target is either `#anchor` (in-file jump) or a relative pathname.
Returns nil when no link is at point."
  (save-excursion
    (let ((p (point))
          (line-start (line-beginning-position))
          (line-end   (line-end-position)))
      (goto-char line-start)
      (let (target)
        (while (and (not target)
                    (re-search-forward "\\[\\([^]]+\\)\\](\\([^)]+\\))" line-end t))
          (when (and (>= p (match-beginning 0))
                     (<= p (match-end 0)))
            (setq target (match-string 2))))
        target))))

(defun vnb-library-follow ()
  "Follow the link at point.
Anchor links (`#name`) narrow this buffer to the matching `### ' section
(reusing the current window).  A relative path opens the source file in
the current window."
  (interactive)
  (let ((target (or (get-text-property (point) 'vnb-link-target)
                    (vnb-library--link-at-point))))
    (cond
     ((null target)
      (message "No link at point"))
     ((string-prefix-p "#" target)
      ;; Anchor link → narrow to the named section, reusing this buffer.
      (let ((anchor (substring target 1)))
        (if (vnb-library--narrow-to-named-section anchor)
            (vnb-library--update-header-line)
          (message "Section `%s' not found" anchor))))
     (t
      ;; Resolve relative to the prover dir.  A link recorded under a
      ;; compiled (.com) load may lack the .scm extension, so fall back
      ;; to <target>.scm before giving up.
      (let* ((raw  (expand-file-name target vnb-launch--dir))
             (path (cond ((file-exists-p raw) raw)
                         ((file-exists-p (concat raw ".scm")) (concat raw ".scm"))
                         (t raw))))
        (if (file-exists-p path)
            (find-file path)
          (message "File not found: %s" path)))))))

(defun vnb-library-next-link ()
  "Move point to the next markdown link in the buffer."
  (interactive)
  (let ((case-fold-search nil))
    (if (re-search-forward "\\[[^]]+\\]([^)]+)" nil t)
        (goto-char (match-beginning 0))
      (message "No more links"))))

(defun vnb-library-prev-link ()
  "Move point to the previous markdown link in the buffer."
  (interactive)
  (let ((case-fold-search nil))
    (if (re-search-backward "\\[[^]]+\\]([^)]+)" nil t)
        (goto-char (match-beginning 0))
      (message "No previous links"))))

(defun vnb-library-next-section ()
  "Move point to the next `### ` heading."
  (interactive)
  (forward-line 1)
  (if (re-search-forward "^### " nil t)
      (progn (beginning-of-line) (recenter 2))
    (forward-line -1)
    (message "No more sections")))

(defun vnb-library-prev-section ()
  "Move point to the previous `### ` heading."
  (interactive)
  (if (re-search-backward "^### " nil t)
      (recenter 2)
    (message "No previous sections")))

;;; -----------------------------------------------------------------------
;;; Layer 3: Proof-context-aware library navigation
;;;
;;; From the *VNB State* buffer (and the REPL), `C-c C-b' scans the visible
;;; proof state for structure references (occurrences of `is-NAME' for any
;;; structure registered in STRUCTURE-INDEX.md's table of contents) and
;;; jumps the library browser to the matching section.  Multiple matches:
;;; `completing-read' prompt; one match: direct jump; none: status message.

(defun vnb-library--known-structures ()
  "Return the list of structure names (lower-case strings) from STRUCTURE-INDEX.md.
The list is read from the file's table of contents, so it tracks whatever
the prover actually has registered (no hardcoded duplicate)."
  (let ((path (vnb-library--index-path)))
    (when (file-exists-p path)
      (with-temp-buffer
        (insert-file-contents path)
        (goto-char (point-min))
        (let ((names '()))
          (while (re-search-forward "^- \\[`\\([^`]+\\)`\\](#" nil t)
            (push (match-string 1) names))
          (nreverse names))))))

(defun vnb-library--structures-mentioned (text)
  "Return the subset of `vnb-library--known-structures' whose `is-NAME'
predicate appears in TEXT, ordered as in the index ToC."
  (let ((all (vnb-library--known-structures))
        (case-fold-search t)
        (found '()))
    (dolist (name all)
      (when (string-match-p
             (concat "\\bis-" (regexp-quote name) "\\b") text)
        (push name found)))
    (nreverse found)))

(defvar-local vnb-library--loaded-mtime nil
  "File mtime captured the last time this buffer was loaded from
STRUCTURE-INDEX.md.  Compared against the file's current mtime in
`vnb-library--ensure-buffer' to detect (catalog) regenerations and
re-read instead of serving stale contents.")

(defun vnb-library--file-mtime (path)
  "Return the modification time of PATH as a Lisp time value, or nil."
  (when (file-exists-p path)
    (file-attribute-modification-time (file-attributes path))))

(defun vnb-library--ensure-buffer ()
  "Make sure the *VNB Library* buffer exists with current contents.
Loads STRUCTURE-INDEX.md and puts the buffer in `vnb-library-mode'.
Re-reads from disk whenever the file's mtime is newer than the cached
copy, so a (catalog) regeneration shows up on the next visit."
  (let ((path (vnb-library--index-path)))
    (when (file-exists-p path)
      (let ((buf (get-buffer-create vnb-library-buffer-name))
            (disk-mtime (vnb-library--file-mtime path)))
        (with-current-buffer buf
          (when (or (not (eq major-mode 'vnb-library-mode))
                    (null vnb-library--loaded-mtime)
                    (time-less-p vnb-library--loaded-mtime disk-mtime))
            (let ((inhibit-read-only t))
              (widen)
              (erase-buffer)
              (insert-file-contents path))
            (goto-char (point-min))
            (setq-local default-directory vnb-launch--dir)
            (unless (eq major-mode 'vnb-library-mode)
              (vnb-library-mode))
            (vnb-library--decorate-buffer)
            (setq vnb-library--loaded-mtime disk-mtime)))
        buf))))

(defun vnb-library--narrow-to-named-section (name)
  "In the current buffer, narrow to the `### NAME' section.
Returns t on success, nil if NAME is not a section."
  (let ((entry (assoc name (vnb-library--collect-sections))))
    (when entry
      (setq vnb-library--matches (list entry)
            vnb-library--match-index 0)
      (vnb-library--narrow-to-section (cdr entry))
      t)))

(defun vnb-library-browse-relevant ()
  "Scan the *VNB State* buffer for structure references and jump to the
matching section in STRUCTURE-INDEX.md.  Multiple matches → prompt.

Bound to \\[vnb-library-browse-relevant] in `vnb-state-mode' and
`vnb-mode'.  Most useful from inside a proof: peek at which structure
predicates are in play, then jump straight to that structure's theorems."
  (interactive)
  (let* ((state-buf (get-buffer vnb-state-buffer-name))
         (text (cond
                (state-buf (with-current-buffer state-buf
                             (buffer-substring-no-properties
                              (point-min) (point-max))))
                (t "")))
         (mentioned (vnb-library--structures-mentioned text))
         (target (cond
                  ((null mentioned) nil)
                  ((= 1 (length mentioned)) (car mentioned))
                  (t (completing-read
                      (format "Structure (%d in state): " (length mentioned))
                      mentioned nil t nil nil (car mentioned)))))
         (buf (and target (vnb-library--ensure-buffer))))
    (cond
     ((null mentioned)
      (message "No structure references in proof state (looked for is-NAME)."))
     ((null buf)
      (message "STRUCTURE-INDEX.md not available; run (catalog) in the prover."))
     (t
      (switch-to-buffer buf)
      (with-current-buffer buf
        (unless (vnb-library--narrow-to-named-section target)
          (message "Section `%s' not found in index" target)))))))

;;; Bind `C-c C-b' wherever it's useful.  vnb-state-mode-map and
;;; vnb-mode-map are both defined in vnb.el; we patch them here after
;;; vnb.el has been loaded by the launcher.
(with-eval-after-load 'vnb
  (define-key vnb-state-mode-map (kbd "C-c C-b") 'vnb-library-browse-relevant)
  (define-key vnb-mode-map       (kbd "C-c C-b") 'vnb-library-browse-relevant))

;; The launcher loads vnb.el unconditionally near the top of this file,
;; so the with-eval-after-load form may have already missed its hook.
;; Patch the keymaps directly as well (idempotent — same binding both ways).
(when (boundp 'vnb-state-mode-map)
  (define-key vnb-state-mode-map (kbd "C-c C-b") 'vnb-library-browse-relevant))
(when (boundp 'vnb-mode-map)
  (define-key vnb-mode-map       (kbd "C-c C-b") 'vnb-library-browse-relevant))

(defun vnb-ws-quit ()
  "Shut down the prover process and exit Emacs."
  (interactive)
  (when (yes-or-no-p "Quit VNB (this also exits Emacs)? ")
    (let ((buf (get-buffer vnb-buffer-name)))
      (when (and buf (vnb--process-live-p buf))
        (let ((proc (get-buffer-process buf)))
          (when proc
            (set-process-query-on-exit-flag proc nil)
            (delete-process proc)))))
    (save-buffers-kill-emacs t)))

;;; -----------------------------------------------------------------------
;;; Display commands (frame size, position, font, reset, save)
;;;
;;; Each command takes an interactive prompt, applies the change to the
;;; current frame, and updates vnb-launch-frame-params so the change
;;; persists for the current session.  vnb-ws-save-display writes the
;;; current settings to ~/.vnb-display.el, which is loaded on next launch.

(defvar vnb-launch-prefs-file
  (expand-file-name "~/.vnb-display.el")
  "Per-user persistent display preferences for VNB.
Loaded at launch if it exists; written by vnb-ws-save-display.")

(defvar vnb-launch-default-font-size 12
  "Default font point size for the VNB frame.")

(defvar vnb-launch-default-font-family "Monospace"
  "Default font family for the VNB frame.  Must be a monospace face;
otherwise column arithmetic (frame width, alignment) breaks.
\"Monospace\" is a generic Fontconfig alias that resolves to whatever
monospace font is installed.")

(defun vnb-launch--update-param (key value)
  "Update KEY in vnb-launch-frame-params to VALUE (assq-replace)."
  (let ((cell (assq key vnb-launch-frame-params)))
    (if cell
        (setcdr cell value)
      (setq vnb-launch-frame-params
            (cons (cons key value) vnb-launch-frame-params)))))

(defun vnb-launch--update-color (key value)
  "Update KEY in vnb-launch-colors to VALUE."
  (let ((cell (assq key vnb-launch-colors)))
    (if cell
        (setcdr cell value)
      (setq vnb-launch-colors
            (cons (cons key value) vnb-launch-colors)))))

(defun vnb-ws-set-foreground (color)
  "Set the frame foreground color."
  (interactive (list (read-color "Foreground color: ")))
  (modify-frame-parameters (selected-frame) `((foreground-color . ,color)))
  (vnb-launch--update-color 'foreground-color color)
  (vnb-launch--autosave))

(defun vnb-ws-set-background (color)
  "Set the frame background color."
  (interactive (list (read-color "Background color: ")))
  (modify-frame-parameters (selected-frame) `((background-color . ,color)))
  (vnb-launch--update-color 'background-color color)
  (set-face-attribute 'fringe nil :background color)
  (vnb-launch--autosave))

(defun vnb-ws-set-cursor-color (color)
  "Set the frame cursor color."
  (interactive (list (read-color "Cursor color: ")))
  (modify-frame-parameters (selected-frame) `((cursor-color . ,color)))
  (vnb-launch--update-color 'cursor-color color)
  (vnb-launch--autosave))

(defun vnb-ws-set-frame-height (n)
  "Set the frame height to N lines."
  (interactive "nFrame height (lines): ")
  (set-frame-height (selected-frame) n)
  (vnb-launch--update-param 'height n)
  (vnb-launch--autosave))

(defun vnb-ws-set-frame-width (n)
  "Set the frame width to N columns."
  (interactive "nFrame width (columns): ")
  (set-frame-width (selected-frame) n)
  (vnb-launch--update-param 'width n)
  (vnb-launch--autosave))

(defun vnb-ws-set-frame-position (left top)
  "Move the frame to LEFT,TOP pixels."
  (interactive "nLeft (pixels): \nnTop (pixels): ")
  (set-frame-position (selected-frame) left top)
  (vnb-launch--update-param 'left left)
  (vnb-launch--update-param 'top  top)
  (vnb-launch--autosave))

(defun vnb-ws-set-font-size (pt)
  "Set the default face height to PT points (8..36)."
  (interactive "nFont size (points): ")
  (unless (and (integerp pt) (>= pt 6) (<= pt 48))
    (user-error "Font size out of range (6..48)"))
  (set-face-attribute 'default nil :height (* pt 10))
  (setq vnb-launch-default-font-size pt)
  (vnb-launch--autosave))

(defun vnb-ws-set-font-family (family)
  "Set the default font FAMILY (must be monospace for correct layout)."
  (interactive
   (list (completing-read
          "Font family: "
          ;; Best-effort completion list; user can also type freely.
          '("Monospace" "DejaVu Sans Mono" "Liberation Mono"
            "Courier 10 Pitch" "Courier" "Courier New" "Fixed"
            "Source Code Pro" "Hack" "Inconsolata" "Iosevka"
            "Ubuntu Mono" "Noto Mono")
          nil nil vnb-launch-default-font-family)))
  (when (or (null family) (string-empty-p family))
    (user-error "No family given"))
  (set-face-attribute 'default nil :family family)
  (setq vnb-launch-default-font-family family)
  (vnb-launch--autosave))

(defun vnb-ws-reset-display ()
  "Reset frame geometry, colors, and font to the built-in defaults."
  (interactive)
  (setq vnb-launch-frame-params
        '((height . 25) (width . 100) (left . 40) (top . 20)
          (border-width . 0) (internal-border-width . 8)))
  (setq vnb-launch-colors
        '((background-color . "black")
          (foreground-color . "#e0e0e0")
          (cursor-color     . "#ffcc66")))
  (setq vnb-launch-default-font-size 12)
  (setq vnb-launch-default-font-family "Monospace")
  (vnb-launch--apply-frame-params)
  (vnb-launch--apply-colors)
  (vnb-launch--apply-saved-font-size)
  (when (file-exists-p vnb-launch-prefs-file)
    (delete-file vnb-launch-prefs-file)))

(defun vnb-ws-save-display ()
  "Write current frame geometry, colors, and font size to vnb-launch-prefs-file."
  (interactive)
  (vnb-launch--write-prefs)
  (message "VNB display preferences saved to %s" vnb-launch-prefs-file))

(defun vnb-launch--write-prefs ()
  "Write prefs file without messaging.  Used by autosave."
  (with-temp-file vnb-launch-prefs-file
    (insert ";;; ~/.vnb-display.el -- VNB display preferences (auto-saved)\n")
    (insert ";;; Loaded at the END of vnb-launch-workspace, so anything in\n")
    (insert ";;; this file overrides the built-in defaults.  You may also\n")
    (insert ";;; hand-edit this file with set-frame-parameter / set-face-\n")
    (insert ";;; attribute calls; they will take effect on startup.\n\n")
    (insert (format "(setq vnb-launch-frame-params\n      '%S)\n\n"
                    vnb-launch-frame-params))
    (insert (format "(setq vnb-launch-colors\n      '%S)\n\n"
                    vnb-launch-colors))
    (insert (format "(setq vnb-launch-default-font-family %S)\n\n"
                    vnb-launch-default-font-family))
    (insert (format "(setq vnb-launch-default-font-size %d)\n\n"
                    vnb-launch-default-font-size))
    (insert "(vnb-launch--apply-frame-params)\n")
    (insert "(vnb-launch--apply-colors)\n")
    (insert "(vnb-launch--apply-saved-font-size)\n")))

(defun vnb-launch--autosave ()
  "Silently persist current display settings."
  (condition-case err
      (vnb-launch--write-prefs)
    (error (message "VNB: could not save display prefs: %s"
                    (error-message-string err)))))

(defvar vnb-launch--prefs-status "not attempted yet"
  "Last result of trying to load the prefs file.")

(defun vnb-launch--load-prefs ()
  "Load saved display preferences if vnb-launch-prefs-file exists."
  (setq vnb-launch--prefs-status
        (cond
         ((not (file-exists-p vnb-launch-prefs-file))
          (format "no file at %s" vnb-launch-prefs-file))
         ((not (file-readable-p vnb-launch-prefs-file))
          (format "unreadable: %s" vnb-launch-prefs-file))
         (t
          (condition-case err
              (progn (load vnb-launch-prefs-file nil t)
                     (format "loaded %s" vnb-launch-prefs-file))
            (error (format "load failed: %s" (error-message-string err))))))))

(defun vnb-launch--apply-saved-font-size ()
  "Apply font family AND size from defvars."
  (when (display-graphic-p)
    (when vnb-launch-default-font-family
      (set-face-attribute 'default nil
                          :family vnb-launch-default-font-family))
    (when vnb-launch-default-font-size
      (set-face-attribute 'default nil
                          :height (* vnb-launch-default-font-size 10)))))

;;; -----------------------------------------------------------------------
;;; Menu bar

(require 'easymenu)

(defvar vnb-launch--menu
  '("VNB"
    ["Start Proof..."     vnb-ws-start-proof    t]
    ["Build Formula..."   vnb-ws-build-formula  t]
    ["Build Structure..." vnb-ws-build-structure t]
    ["Show Theorems"      vnb-ws-show-theorems  t]
    ["Show PSS"           vnb-ws-show-pss       t]
    ["Describe Structure..." vnb-describe-structure t]
    ["Definitions"        vnb-ws-show-definitions t]
    ["Structure Manual"   vnb-structure-manual  t]
    ["Structure Graph"    vnb-structure-graph-html   t]
    ["View as PDF"        vnb-view-as-pdf       t]
    ["Suggest Forward Moves" vnb-suggest-forward-moves t]
    "---"
    ["Home Workspace"     vnb-launch-workspace             t]
    ["Focus Workspace"    vnb-launch--show-proof-workspace t]
    ["Proof Overview"     vnb-launch--show-overview-workspace t]
    ["Refresh"            vnb-ws-refresh                   t]
    "---"
    ("Proof"
      ["Direct Inference"     vnb-pf-direct-inference t]
      ["Assume"               vnb-pf-assumption       t]
      ["Theorem..."           vnb-pf-theorem          t]
      ["Univ. Instantiate..." vnb-pf-instantiate      t]
      ["Exist. Witness..."    vnb-pf-exists-witness   t]
      ["Backchain..."         vnb-pf-backchain        t]
      ["Focus..."             vnb-pf-focus            t]
      ["QED..."               vnb-pf-qed              t])
    ["Show Scratch Pad (advanced)" vnb-pf-show-repl t]
    "---"
    ("Display"
      ["Frame Height..."       vnb-ws-set-frame-height   t]
      ["Frame Width..."        vnb-ws-set-frame-width    t]
      ["Frame Position..."     vnb-ws-set-frame-position t]
      ["Font Family..."        vnb-ws-set-font-family    t]
      ["Font Size..."          vnb-ws-set-font-size      t]
      "---"
      ["Foreground Color..."   vnb-ws-set-foreground     t]
      ["Background Color..."   vnb-ws-set-background     t]
      ["Cursor Color..."       vnb-ws-set-cursor-color   t]
      "---"
      ["Reset to Defaults"     vnb-ws-reset-display      t]
      ["Save Current Settings" vnb-ws-save-display       t])
    "---"
    ["Quit VNB"          vnb-ws-quit           t]))

(defun vnb-launch--install-menu ()
  "Add the VNB menu to the GLOBAL menu bar so it appears in every buffer."
  (easy-menu-define vnb-launch-menu global-map
    "VNB menu"
    vnb-launch--menu)
  ;; Relabel Emacs's built-in "Buffer" menu as "Workspaces".  We use
  ;; after-advice on `menu-bar-update-buffers' because it rebuilds the
  ;; menu entry on every buffer change and would otherwise reset the
  ;; label back to "Buffer".
  (advice-add 'menu-bar-update-buffers :after
              #'vnb-launch--rename-buffer-menu)
  ;; Apply once now so the relabel takes effect before the next update.
  (vnb-launch--rename-buffer-menu))

(defun vnb-launch--rename-buffer-menu (&rest _)
  "Rename the global \"Buffer\" menu entry to \"Workspaces\".
The label lives in two cells of the menu-bar's buffer entry; both must
be set or the menu bar will display the old name.  (Courtesy of the
user's Lisp Machine vintage Elisp instincts.)"
  (let ((entry (assoc 'buffer
                      (lookup-key (current-global-map) [menu-bar]))))
    (when (and (listp entry) (> (length entry) 3))
      (setf (nth 1 entry) "Workspaces")
      (setf (nth 3 entry) "Workspaces"))))

;;; -----------------------------------------------------------------------
;;; Tool bar
;;;
;;; One shared toolbar map installed as the default tool-bar-map.  Every
;;; buffer that doesn't override gets it -- the workspace, the *VNB* REPL,
;;; *VNB State*, and any incidental buffers.

(defvar vnb-launch--toolbar-map nil
  "Shared tool-bar keymap with the VNB action icons.")

(defun vnb-launch--install-toolbar ()
  "Build the VNB toolbar and set it as the default tool-bar-map."
  (setq vnb-launch--toolbar-map (make-sparse-keymap))
  (tool-bar-local-item "new"        'vnb-ws-start-proof
                       'vnb-tb-start-proof   vnb-launch--toolbar-map
                       :help "Start a new proof")
  (tool-bar-local-item "spell"      'vnb-ws-build-formula
                       'vnb-tb-build-formula vnb-launch--toolbar-map
                       :help "Build/parse a formula")
  (tool-bar-local-item "index"      'vnb-ws-show-theorems
                       'vnb-tb-show-theorems vnb-launch--toolbar-map
                       :help "Show installed theorems")
  (tool-bar-local-item "refresh"    'vnb-ws-refresh
                       'vnb-tb-refresh       vnb-launch--toolbar-map
                       :help "Refresh workspace")
  (tool-bar-local-item "exit"       'vnb-ws-quit
                       'vnb-tb-quit          vnb-launch--toolbar-map
                       :help "Quit VNB")
  (setq-default tool-bar-map vnb-launch--toolbar-map))

;;; -----------------------------------------------------------------------
;;; Frame geometry
;;;
;;; Applied to the selected frame when the workspace opens.  Tweak this
;;; defvar (in vnb-launch.el or your own init) to fit your screen.
;;; Height/width are in lines/columns; left/top are pixels.

(defvar vnb-launch-frame-params
  '((height            . 25)
    (width             . 100)
    (left              . 40)
    (top               . 20)
    (border-width      . 0)
    (internal-border-width . 8))
  "Frame parameters applied by vnb-launch-workspace.
Set to nil to leave the frame untouched.")

(defun vnb-launch--apply-frame-params ()
  "Resize and position the selected frame per vnb-launch-frame-params.
Uses explicit setters because modify-frame-parameters can race with the
window manager during startup on some systems."
  (when (and vnb-launch-frame-params
             (display-graphic-p))
    (let ((frame (selected-frame))
          (h (cdr (assq 'height vnb-launch-frame-params)))
          (w (cdr (assq 'width  vnb-launch-frame-params)))
          (l (cdr (assq 'left   vnb-launch-frame-params)))
          (tp (cdr (assq 'top    vnb-launch-frame-params))))
      (when (numberp h) (set-frame-height frame h))
      (when (numberp w) (set-frame-width  frame w))
      (when (and (numberp l) (numberp tp))
        (set-frame-position frame l tp))
      ;; Borders -- no explicit setter; only these go through
      ;; modify-frame-parameters.
      (let ((rest (cl-remove-if (lambda (p)
                                  (memq (car p) '(height width left top)))
                                vnb-launch-frame-params)))
        (when rest
          (modify-frame-parameters frame rest))))))

;;; -----------------------------------------------------------------------
;;; Frame-wide dark theme.
;;;
;;; The VNB session is dedicated to one task, so we set the frame
;;; background/foreground directly -- every buffer in the session
;;; (workspace, *VNB* REPL, *VNB State*, minibuffer, help, etc.)
;;; inherits the dark palette without per-mode face-remapping.

(defvar vnb-launch-colors
  '((background-color . "black")
    (foreground-color . "#e0e0e0")
    (cursor-color     . "#ffcc66"))
  "Frame colors applied by vnb-launch-workspace.
Set to nil to skip color customization.")

(defun vnb-launch--apply-colors ()
  "Apply VNB dark palette to the current frame and to faces that need it."
  (when (and vnb-launch-colors (display-graphic-p))
    (modify-frame-parameters (selected-frame) vnb-launch-colors)
    ;; Propagate to any future frames in this session.
    (setq default-frame-alist
          (append vnb-launch-colors default-frame-alist))
    ;; Mode line: distinguish active from inactive on dark bg.
    (set-face-attribute 'mode-line nil
                        :background "#1a3a5a" :foreground "#ffffff"
                        :box '(:line-width 1 :color "#3a7cb8"))
    (set-face-attribute 'mode-line-inactive nil
                        :background "#101820" :foreground "#888888"
                        :box '(:line-width 1 :color "#2a4a6a"))
    ;; Selection.
    (set-face-attribute 'region nil :background "#3a3a5a")
    ;; Minibuffer prompt.
    (set-face-attribute 'minibuffer-prompt nil
                        :foreground "#ffcc66" :weight 'bold)
    ;; Fringe (left/right gutter).
    (set-face-attribute 'fringe nil :background "black")))

;;; -----------------------------------------------------------------------
;;; Entry point: open the workspace.

(defun vnb-launch-workspace ()
  "Create or switch to the Initial Workspace buffer."
  (interactive)
  ;; Tell Emacs to stop tracking GNOME's "system font" setting.  Without
  ;; this, on Ubuntu/GNOME the system font (often a proportional
  ;; condensed sans-serif like "TeX Gyre Heros Cn") keeps reasserting
  ;; itself over our frame font, which is why VNB launches with a tiny
  ;; unreadable window even though `set-frame-parameter' returned cleanly.
  (when (boundp 'font-use-system-font)
    (setq font-use-system-font nil))
  ;; Let a command that prompts (e.g. Describe Structure) be invoked while
  ;; another minibuffer prompt is already live, instead of erroring out
  ;; with "Command attempted to use minibuffer while in minibuffer".  The
  ;; depth indicator shows a [N] marker so a nested prompt is visible; C-g
  ;; backs out one level at a time.
  (setq enable-recursive-minibuffers t)
  (minibuffer-depth-indicate-mode 1)
  ;; Built-in defaults first.
  (vnb-launch--apply-frame-params)
  (vnb-launch--apply-colors)
  (vnb-launch--apply-saved-font-size)
  ;; User prefs LAST so they always win, whether the file updates the
  ;; defvars (auto-saved format) or calls set-frame-parameter/set-face-
  ;; attribute directly (hand-edited format).  The auto-saved format
  ;; emitted by `vnb-launch--write-prefs' invokes the apply helpers at
  ;; the bottom, so either style takes effect.
  (vnb-launch--load-prefs)
  (vnb-launch--install-menu)
  (vnb-launch--install-toolbar)
  (let ((buf (get-buffer-create vnb-workspace-buffer-name)))
    (with-current-buffer buf
      (vnb-workspace-mode)
      (vnb-launch--paint-workspace))
    (switch-to-buffer buf)
    (delete-other-windows)))

;;; -----------------------------------------------------------------------
;;; Phase 2: Proof Workspace
;;;
;;; A single dedicated `*VNB Proof*' buffer that re-paints on every
;;; proof-state update from the prover.  Action buttons / keys for the
;;; common tactics; each tactic that takes arguments uses guided
;;; prompts (empty input cancels).  The raw `*VNB*' REPL is hidden by
;;; default; reachable via the VNB → Show Scratch Pad menu entry.

(defvar vnb-proof-buffer-name "*VNB Focus*"
  "Name of the Focus Workspace buffer (current sequent + tactic buttons).")

(defvar vnb-overview-buffer-name "*VNB Overview*"
  "Name of the Proof Overview buffer (all open goals, click to focus).")

(defvar vnb-proof--last-state ""
  "Most recent proof-state text received from the prover.
Cached so both painters (focus + overview) can re-render without
re-querying.")

;;; ----- Structured parser for VNB proof-state text -----
;;;
;;; print-proof-state (proof-commands.scm) emits one of:
;;;   "N open goal(s)."
;;;   "Focus:"
;;;   "  [N] LHS  =>  RHS"
;;;   ["Other open goals:" plus more "  [N] LHS  =>  RHS" lines]
;;; or "Proof complete." or "No current proof. ..."
;;;
;;; Returns a plist:
;;;   (:status STATUS :count N :focus SEQ :others (SEQ...))
;;; where STATUS is 'in-progress | 'done | 'none and SEQ is a plist
;;;   (:num N :asms STR :goal STR :grounded BOOL).
;;; Returns nil for empty input.

(defun vnb-launch--parse-state (text)
  "Parse VNB state TEXT into a structured plist; nil if TEXT is empty."
  (when (and text (not (string-empty-p text)))
    (let ((status 'in-progress)
          (count 0)
          (focus nil)
          (others '())
          (section nil))
      (dolist (line (split-string text "\n"))
        (cond
          ((string-match "\\`\\([0-9]+\\) open goal(s)\\.\\'" line)
           (setq count (string-to-number (match-string 1 line))))
          ((string= line "Focus:")           (setq section 'focus))
          ((string= line "Other open goals:") (setq section 'others))
          ((string= line "Proof complete.")  (setq status 'done))
          ((string-match "\\`No current proof\\." line) (setq status 'none))
          ((string-match
            "\\`  \\[\\(-?[0-9]+\\)\\] \\(.+?\\)  =>  \\(.+\\)\\'"
            line)
           (let* ((num     (string-to-number (match-string 1 line)))
                  (asms    (match-string 2 line))
                  (goal    (match-string 3 line))
                  (grounded (and (string-match "  \\[GROUNDED\\]\\'" goal)
                                 (prog1 t
                                   (setq goal (substring goal 0
                                                         (match-beginning 0))))))
                  (seq (list :num num :asms asms :goal goal
                             :grounded grounded)))
             (pcase section
               ('focus  (setq focus seq))
               ('others (push seq others)))))))
      (list :status status :count count
            :focus  focus
            :others (nreverse others)))))

;;; ----- Bracket-aware splitter -----
;;;
;;; Assumption lists are joined by ", " but formulas embed commas
;;; inside brackets (e.g. forall([x, y in A], body)).  Split only at
;;; bracket depth 0 across ()  []  {}.

(defun vnb-launch--split-top-level (str sep)
  "Split STR on SEP at top bracket depth.  Brackets: () [] {}."
  (let ((parts '()) (start 0) (depth 0) (i 0)
        (len (length str)) (slen (length sep)))
    (while (< i len)
      (let ((c (aref str i)))
        (cond
          ((memq c '(?\( ?\[ ?{))  (cl-incf depth) (cl-incf i))
          ((memq c '(?\) ?\] ?}))  (cl-decf depth) (cl-incf i))
          ((and (zerop depth)
                (<= (+ i slen) len)
                (string= (substring str i (+ i slen)) sep))
           (push (substring str start i) parts)
           (setq start (+ i slen))
           (setq i (+ i slen)))
          (t (cl-incf i)))))
    (push (substring str start) parts)
    (nreverse parts)))

(defun vnb-launch--render-sequent-block (seq)
  "Render a parsed sequent SEQ with assumptions one per line."
  (let* ((num   (plist-get seq :num))
         (asms  (plist-get seq :asms))
         ;; Strip the surrounding quotes older builds emit (wff->string);
         ;; harmless on newer builds that already render unquoted.
         (goal  (vnb-launch--dequote (plist-get seq :goal)))
         (grounded (plist-get seq :grounded))
         (parts (if (string= asms "()")
                    nil
                  (mapcar #'vnb-launch--dequote
                          (vnb-launch--split-top-level asms ", ")))))
    (insert "    ")
    (insert (propertize (format "[%d]" num) 'face 'vnb-dim))
    (insert "\n")
    (if (null parts)
        (progn (insert "      ")
               (insert (propertize "(no assumptions)" 'face 'vnb-dim))
               (insert "\n"))
      (let ((i 1))
        (dolist (a parts)
          (insert "      ")
          (insert (propertize (format "%d. " i) 'face 'vnb-dim))
          (insert (propertize a 'face 'vnb-assumption))
          (insert "\n")
          (cl-incf i))))
    (insert "    ")
    (insert (propertize "⊢" 'face 'vnb-accent))
    (insert "  ")
    (insert (propertize goal 'face 'vnb-goal))
    (when grounded
      (insert "  ")
      (insert (propertize "[GROUNDED]" 'face 'vnb-dim)))
    (insert "\n")))

(defvar vnb-proof-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m "d" 'vnb-pf-direct-inference)
    (define-key m "a" 'vnb-pf-assumption)
    (define-key m "=" 'vnb-pf-reflexivity)
    (define-key m "m" 'vnb-pf-rewrite)
    (define-key m "t" 'vnb-pf-theorem)
    (define-key m "i" 'vnb-pf-instantiate)
    (define-key m "w" 'vnb-pf-exists-witness)
    (define-key m "b" 'vnb-pf-backchain)
    (define-key m "B" 'vnb-pf-backchain-star)
    (define-key m "c" 'vnb-pf-arith)
    (define-key m "s" 'vnb-pf-ring-simplify)
    (define-key m "f" 'vnb-pf-focus)
    (define-key m "q" 'vnb-pf-qed)
    (define-key m "h" 'vnb-launch-workspace)
    (define-key m "o" 'vnb-launch--show-overview-workspace)
    (define-key m "r" 'vnb-pf-show-repl)
    (define-key m "S" 'vnb-ws-scratch-workspace)
    (define-key m "W" 'vnb-pf-save-proof-script)
    (define-key m "g" 'vnb-pf-refresh)
    m)
  "Keymap for the Focus Workspace buffer.")

(define-derived-mode vnb-proof-mode special-mode "VNB-Focus"
  "Major mode for the VNB Focus Workspace buffer."
  (setq buffer-read-only t)
  (setq truncate-lines nil)
  (vnb-launch--apply-faces))

(defun vnb-launch--paint-proof ()
  "Render the Focus Workspace: current sequent + tactic buttons."
  (let ((inhibit-read-only t)
        (parsed (vnb-launch--parse-state vnb-proof--last-state)))
    (erase-buffer)
    (insert "\n")
    (insert (propertize "  VNB Focus Workspace" 'face 'vnb-title))
    (insert "\n\n")
    (insert (propertize (make-string 60 ?─) 'face 'vnb-accent))
    (insert "\n\n  ")
    (vnb-launch--insert-button "Direct Inference" 'vnb-pf-direct-inference
                               "(di) decompose goal by top connective")
    (insert "  ")
    (vnb-launch--insert-button "Assume" 'vnb-pf-assumption
                               "(ass) close goal by matching an assumption")
    (insert "  ")
    (vnb-launch--insert-button "Close (a=a)" 'vnb-pf-reflexivity
                               "(rfl) close a goal that says a thing equals itself")
    (insert "\n  ")
    (vnb-launch--insert-button "Theorem" 'vnb-pf-theorem
                               "(ta NAME) add named theorem to context")
    (insert "  ")
    (vnb-launch--insert-button "Univ. Inst." 'vnb-pf-instantiate
                               "(inst FORMULA TERM) instantiate a FORALL hypothesis")
    (insert "  ")
    (vnb-launch--insert-button "Witness" 'vnb-pf-exists-witness
                               "(ew TERM) supply a witness for a FORSOME goal")
    (insert "\n  ")
    (vnb-launch--insert-button "Backchain" 'vnb-pf-backchain
                               "(bc FORMULA) backchain on an implication")
    (insert "  ")
    (vnb-launch--insert-button "Cite Lemma" 'vnb-pf-backchain-star
                               "(bc* 'NAME ()) match a named lemma's conclusion to the goal; its hypotheses become subgoals")
    (insert "  ")
    (vnb-launch--insert-button "Rewrite" 'vnb-pf-rewrite
                               "(mac 'NAME) rewrite the goal using a named equation/biconditional rule")
    (insert "  ")
    (vnb-launch--insert-button "Arith" 'vnb-pf-arith
                               "(arith) close a ground arithmetic goal, e.g. 2 + 3 = 5")
    (insert "  ")
    (vnb-launch--insert-button "Simplify" 'vnb-pf-ring-simplify
                               "(rs) ring-simplify: close an equality, incl. variables, e.g. (x+1)*(x-1) = x*x - 1")
    (insert "  ")
    (vnb-launch--insert-button "Focus" 'vnb-pf-focus
                               "(focus N) switch to another open goal")
    (insert "\n  ")
    (vnb-launch--insert-button "QED" 'vnb-pf-qed
                               "(qed NAME) install completed proof as theorem")
    (insert "  ")
    (vnb-launch--insert-button "Overview" 'vnb-launch--show-overview-workspace
                               "Show the Proof Overview (all open goals)")
    (insert "  ")
    (vnb-launch--insert-button "Home" 'vnb-launch-workspace
                               "Back to Home Workspace")
    (insert "  ")
    (vnb-launch--insert-button "Scratch Pad" 'vnb-pf-show-repl
                               "Show the Scratch Pad: type prover commands by hand (advanced; rarely needed)")
    (insert "  ")
    (vnb-launch--insert-button "Scratch Workspace" 'vnb-ws-scratch-workspace
                               "Lisp-interaction sheet: C-j sends the sexp (or region as a block) to the prover and inserts the result")
    (insert "\n  ")
    (vnb-launch--insert-button "Save Script" 'vnb-pf-save-proof-script
                               "Write this proof's commands to a re-loadable script file")
    (insert "  ")
    (vnb-launch--insert-button "Save Session" 'vnb-ws-save-session
                               "Write every proof completed this session to one script file")
    (insert "\n\n")
    (insert (propertize (make-string 60 ?─) 'face 'vnb-accent))
    (insert "\n\n")
    (vnb-launch--insert-error-panel)
    (cond
     ((null parsed)
      (insert (propertize "  (no proof in progress)\n" 'face 'vnb-dim)))
     ((eq (plist-get parsed :status) 'done)
      (insert "  ")
      (insert (propertize "✓ Proof complete." 'face 'vnb-goal))
      (insert "\n"))
     ((eq (plist-get parsed :status) 'none)
      (insert (propertize "  (no proof in progress)\n" 'face 'vnb-dim)))
     (t
      (let ((focus (plist-get parsed :focus))
            (count (plist-get parsed :count)))
        (insert "  ")
        (insert (propertize
                 (format "▸ Focus    %d open goal%s%s"
                         count (if (= count 1) "" "s")
                         (if (> count 1) "  (see Overview for the rest)" ""))
                 'face 'vnb-accent))
        (insert "\n\n")
        (if focus
            (vnb-launch--render-sequent-block focus)
          (insert (propertize "  (no focused goal)\n" 'face 'vnb-dim))))))
    (insert "\n")
    (insert (propertize (make-string 60 ?─) 'face 'vnb-accent))
    (insert "\n\n")
    (insert (propertize
             (concat "  Keys: d direct-inf  a assume  = close(a=a)  "
                     "m rewrite  t theorem  i univ-inst  w witness  "
                     "b bc  B cite-lemma  f focus  q qed  o overview  "
                     "h home  r scratch-pad  S scratch-workspace  "
                     "W save-script  g refresh\n")
             'face 'vnb-dim))
    (goto-char (point-min))))

(defun vnb-pf-refresh ()
  "Repaint the Proof Workspace from the cached last state."
  (interactive)
  (let ((buf (get-buffer vnb-proof-buffer-name)))
    (when buf
      (with-current-buffer buf
        (vnb-launch--paint-proof)))))

;;; ----- Structured renderer for VNB proof-state text -----
;;;
;;; print-proof-state (proof-commands.scm) emits a fixed format:
;;;   "N open goal(s)."
;;;   "Focus:"
;;;   "  [N] LHS  =>  RHS"
;;;   ["Other open goals:"]
;;;   ["  [N] LHS  =>  RHS" ...]
;;; or
;;;   "Proof complete."
;;;
;;; LHS is either "()" or a comma-separated assumption list.  Commas are
;;; embedded inside formulas too (e.g. forall([x, y in A], body)), so we
;;; render the assumption block as one styled line rather than risk a
;;; misparse.  "  =>  " is the only place the literal sequent arrow
;;; appears -- formula-level implies prints as " implies ", lowercase.

(defun vnb-launch--render-state (text)
  "Render the proof-state TEXT into the current buffer with styled faces."
  (let ((lines (split-string text "\n")))
    (dolist (line lines)
      (cond
       ;; "N open goal(s)."
       ((string-match "\\`\\([0-9]+\\) open goal(s)\\.\\'" line)
        (insert "  ")
        (insert (propertize
                 (format "%s open goal(s)" (match-string 1 line))
                 'face 'vnb-heading))
        (insert "\n"))
       ;; "Focus:"
       ((string= line "Focus:")
        (insert "\n  ")
        (insert (propertize "▸ Focus" 'face 'vnb-accent))
        (insert "\n"))
       ;; "Other open goals:"
       ((string= line "Other open goals:")
        (insert "\n  ")
        (insert (propertize "Other open goals" 'face 'vnb-accent))
        (insert "\n"))
       ;; "Proof complete."
       ((string= line "Proof complete.")
        (insert "\n  ")
        (insert (propertize "✓ Proof complete." 'face 'vnb-goal))
        (insert "\n"))
       ;; "No current proof. ..."
       ((string-match "\\`No current proof\\." line)
        (insert "  ")
        (insert (propertize line 'face 'vnb-dim))
        (insert "\n"))
       ;; Sequent line: "  [N] LHS  =>  RHS" (also handles trailing "  [GROUNDED]")
       ((string-match
         "\\`  \\(\\[[-0-9]+\\]\\) \\(.+?\\)  =>  \\(.+\\)\\'"
         line)
        (let* ((num   (match-string 1 line))
               (asms  (match-string 2 line))
               (goal  (match-string 3 line))
               (grounded (string-match "  \\[GROUNDED\\]\\'" goal)))
          (when grounded
            (setq goal (substring goal 0 (match-beginning 0))))
          (insert "    ")
          (insert (propertize num 'face 'vnb-dim))
          (insert "  ")
          (if (string= asms "()")
              (insert (propertize "(no assumptions)" 'face 'vnb-dim))
            (insert (propertize asms 'face 'vnb-assumption)))
          (insert "\n       ")
          (insert (propertize "⊢" 'face 'vnb-accent))
          (insert "  ")
          (insert (propertize goal 'face 'vnb-goal))
          (when grounded
            (insert "  ")
            (insert (propertize "[GROUNDED]" 'face 'vnb-dim)))
          (insert "\n")))
       ;; Blank line.
       ((string= line "")
        (insert "\n"))
       ;; Anything else: pass through dim so it's clearly "raw".
       (t
        (insert "  ")
        (insert (propertize line 'face 'vnb-body))
        (insert "\n"))))))

(defun vnb-launch--on-state-update (text)
  "Cache TEXT and repaint any open Focus / Overview workspace.
A fresh proof-state means the last action succeeded, so any cached
error from a prior failed attempt is also cleared here."
  (setq vnb-proof--last-state text)
  (setq vnb--last-error nil)
  (let ((fb (get-buffer vnb-proof-buffer-name))
        (ob (get-buffer vnb-overview-buffer-name)))
    (when fb (with-current-buffer fb (vnb-launch--paint-proof)))
    (when ob (with-current-buffer ob (vnb-launch--paint-overview)))))

(defun vnb-launch--on-vnb-error (_msg)
  "Repaint any open Focus / Overview workspace so the error panel appears.
The error text itself lives in `vnb--last-error', set by the preoutput
filter before this hook fires."
  (let ((fb (get-buffer vnb-proof-buffer-name))
        (ob (get-buffer vnb-overview-buffer-name)))
    (when fb (with-current-buffer fb (vnb-launch--paint-proof)))
    (when ob (with-current-buffer ob (vnb-launch--paint-overview)))))

(defun vnb-launch--insert-error-panel ()
  "If `vnb--last-error' is set, insert a styled error block at point."
  (when vnb--last-error
    (insert "  ")
    (insert (propertize (format "! Error: %s" vnb--last-error)
                        'face 'vnb-error))
    (insert "\n\n")
    (insert (propertize (make-string 60 ?─) 'face 'vnb-accent))
    (insert "\n\n")))

(defun vnb-launch--show-proof-workspace ()
  "Switch to the Focus Workspace as a single full-frame window."
  (interactive)
  (let ((buf (get-buffer-create vnb-proof-buffer-name)))
    (with-current-buffer buf
      (unless (eq major-mode 'vnb-proof-mode)
        (vnb-proof-mode))
      (vnb-launch--paint-proof))
    (delete-other-windows)
    (switch-to-buffer buf)))

;;; ----- Overview Workspace -----

(defvar vnb-overview-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m "f" 'vnb-launch--show-proof-workspace)
    (define-key m "h" 'vnb-launch-workspace)
    (define-key m "r" 'vnb-pf-show-repl)
    (define-key m "S" 'vnb-ws-scratch-workspace)
    (define-key m "W" 'vnb-pf-save-proof-script)
    (define-key m "g" 'vnb-ov-refresh)
    (define-key m "n" 'vnb-ov-next-goal)
    (define-key m "p" 'vnb-ov-prev-goal)
    (define-key m (kbd "RET") 'push-button)
    m)
  "Keymap for the Proof Overview buffer.")

(define-derived-mode vnb-overview-mode special-mode "VNB-Overview"
  "Major mode for the VNB Proof Overview buffer."
  (setq buffer-read-only t)
  (setq truncate-lines nil)
  (vnb-launch--apply-faces))

(defun vnb-launch--insert-action-button (label fn help)
  "Insert a clickable button labelled LABEL whose action calls thunk FN.
Lexical binding makes the closure capture variables from the caller."
  (insert-text-button
   (concat "  " label "  ")
   'face 'vnb-button
   'mouse-face 'vnb-button-mouse
   'follow-link t
   'help-echo help
   'action (lambda (_) (funcall fn))))

(defun vnb-launch--focus-on (n)
  "Send (focus N) to the prover and switch to the Focus Workspace."
  (vnb-launch--send-tactic (format "(focus %d)" n))
  (vnb-launch--show-proof-workspace))

(defun vnb-launch--paint-overview ()
  "Render the Proof Overview: every open goal, click to focus."
  (let ((inhibit-read-only t)
        (parsed (vnb-launch--parse-state vnb-proof--last-state)))
    (erase-buffer)
    (insert "\n")
    (insert (propertize "  VNB Proof Overview" 'face 'vnb-title))
    (insert "\n\n")
    (insert (propertize (make-string 60 ?─) 'face 'vnb-accent))
    (insert "\n\n  ")
    (vnb-launch--insert-button "Focus Workspace"
                               'vnb-launch--show-proof-workspace
                               "Switch to the Focus Workspace")
    (insert "  ")
    (vnb-launch--insert-button "Home" 'vnb-launch-workspace
                               "Back to Home Workspace")
    (insert "  ")
    (vnb-launch--insert-button "Refresh" 'vnb-ov-refresh
                               "Repaint the overview")
    (insert "  ")
    (vnb-launch--insert-button "Scratch Pad" 'vnb-pf-show-repl
                               "Show the Scratch Pad: type prover commands by hand (advanced; rarely needed)")
    (insert "  ")
    (vnb-launch--insert-button "Scratch Workspace" 'vnb-ws-scratch-workspace
                               "Lisp-interaction sheet: C-j sends the sexp (or region as a block) to the prover and inserts the result")
    (insert "\n  ")
    (vnb-launch--insert-button "Save Script" 'vnb-pf-save-proof-script
                               "Write this proof's commands to a re-loadable script file")
    (insert "  ")
    (vnb-launch--insert-button "Save Session" 'vnb-ws-save-session
                               "Write every proof completed this session to one script file")
    (insert "\n\n")
    (insert (propertize (make-string 60 ?─) 'face 'vnb-accent))
    (insert "\n\n")
    (vnb-launch--insert-error-panel)
    (cond
     ((null parsed)
      (insert (propertize "  (no proof in progress)\n" 'face 'vnb-dim)))
     ((eq (plist-get parsed :status) 'done)
      (insert "  ")
      (insert (propertize "✓ Proof complete." 'face 'vnb-goal))
      (insert "\n"))
     ((eq (plist-get parsed :status) 'none)
      (insert (propertize "  (no proof in progress)\n" 'face 'vnb-dim)))
     (t
      (let* ((count  (plist-get parsed :count))
             (focus  (plist-get parsed :focus))
             (others (plist-get parsed :others))
             (all    (sort (append (and focus (list focus))
                                   (copy-sequence others))
                           (lambda (a b)
                             (< (plist-get a :num) (plist-get b :num))))))
        (insert "  ")
        (insert (propertize (format "%d open goal%s"
                                    count (if (= count 1) "" "s"))
                            'face 'vnb-heading))
        (insert "\n\n")
        (dolist (seq all)
          (let* ((num      (plist-get seq :num))
                 (asms     (plist-get seq :asms))
                 (goal     (plist-get seq :goal))
                 (is-focus (and focus (= num (plist-get focus :num)))))
            (insert "  ")
            (insert (propertize (if is-focus "▸ " "  ") 'face 'vnb-accent))
            (insert (propertize (format "[%d]" num) 'face 'vnb-dim))
            (insert "  ")
            (insert (propertize
                     (if (string= asms "()") "(no asms)" asms)
                     'face 'vnb-assumption))
            (insert "\n      ")
            (insert (propertize "⊢" 'face 'vnb-accent))
            (insert "  ")
            (insert (propertize goal 'face 'vnb-goal))
            (insert "\n      ")
            (if is-focus
                (insert (propertize "(current focus)" 'face 'vnb-dim))
              (let ((n num))
                (vnb-launch--insert-action-button
                 "Focus on this"
                 (lambda () (vnb-launch--focus-on n))
                 (format "Make goal [%d] the current focus" n))))
            (insert "\n\n"))))))
    (insert (propertize (make-string 60 ?─) 'face 'vnb-accent))
    (insert "\n\n")
    (insert (propertize
             "  Keys: RET focus  n next  p prev  f focus-ws  h home  r scratch-pad  S scratch-workspace  W save-script  g refresh\n"
             'face 'vnb-dim))
    (goto-char (point-min))))

(defun vnb-ov-refresh ()
  "Repaint the Proof Overview from cached state."
  (interactive)
  (let ((buf (get-buffer vnb-overview-buffer-name)))
    (when buf
      (with-current-buffer buf
        (vnb-launch--paint-overview)))))

(defun vnb-ov-next-goal ()
  "Move point to the next \"Focus on this\" button."
  (interactive)
  (forward-button 1 t t))

(defun vnb-ov-prev-goal ()
  "Move point to the previous \"Focus on this\" button."
  (interactive)
  (backward-button 1 t t))

(defun vnb-launch--show-overview-workspace ()
  "Switch to the Proof Overview as a single full-frame window."
  (interactive)
  (let ((buf (get-buffer-create vnb-overview-buffer-name)))
    (with-current-buffer buf
      (unless (eq major-mode 'vnb-overview-mode)
        (vnb-overview-mode))
      (vnb-launch--paint-overview))
    (delete-other-windows)
    (switch-to-buffer buf)))

;;; ----- Tactic dispatch helpers -----

(defun vnb-launch--send-tactic (str)
  "Send a tactic-line STR to the running prover; auto-start if needed."
  (vnb-launch--ensure-prover)
  (let ((buf (get-buffer vnb-buffer-name)))
    (when buf
      (comint-send-string buf (concat str "\n")))))

(defun vnb-launch--read-required (prompt)
  "Read a non-empty string from the minibuffer; user-error on empty input.
Empty input is the universal cancel/'none of the above' across prompts."
  (let ((s (read-string prompt)))
    (when (string-match-p "\\`[ \t]*\\'" s)
      (user-error "Cancelled"))
    s))

(defun vnb-launch--dequote (s)
  "Strip one layer of surrounding double-quotes from S, if present.
Tactic senders wrap the formula with %S, which re-adds proper quoting, so
a bare formula is what's wanted.  This lets a user paste an assumption
verbatim (quotes and all) without producing a double-quoted, unparseable
argument."
  (let ((s (string-trim s)))
    (if (and (>= (length s) 2)
             (eq (aref s 0) ?\")
             (eq (aref s (1- (length s))) ?\"))
        (substring s 1 (1- (length s)))
      s)))

;;; ----- Tactic commands (guided prompts) -----

(defun vnb-pf-direct-inference ()
  "Decompose the current goal by its top connective.  Wraps (di)."
  (interactive)
  (vnb-launch--send-tactic "(di)"))

(defun vnb-pf-reflexivity ()
  "Close a goal of the form (= a a) -- a thing equal to itself.  Wraps (rfl)."
  (interactive)
  (vnb-launch--send-tactic "(rfl)"))

(defun vnb-pf-rewrite (name)
  "Rewrite the current goal using the named rule NAME.  Wraps (mac 'NAME).
NAME is a theorem/axiom whose core is an equation or biconditional; applying
it replaces matching pieces of the goal with the other side."
  (interactive
   (list (vnb-launch--read-required
          "Rewrite goal using rule name (empty cancels): ")))
  (vnb-launch--send-tactic (format "(mac '%s)" (vnb-launch--dequote name))))

(defun vnb-pf-assumption ()
  "Close the current goal if it matches an assumption.  Wraps (ass)."
  (interactive)
  (vnb-launch--send-tactic "(ass)"))

(defun vnb-pf-arith ()
  "Close a ground arithmetic goal by evaluation, e.g. 2 + 3 = 5.  Wraps (arith)."
  (interactive)
  (vnb-launch--send-tactic "(arith)"))

(defun vnb-pf-ring-simplify ()
  "Close an equality goal by ring normalization (handles variables).  Wraps (rs)."
  (interactive)
  (vnb-launch--send-tactic "(rs)"))

(defun vnb-pf-theorem (name)
  "Add the named theorem NAME to the current context.  Wraps (ta 'NAME)."
  (interactive
   (list (vnb-launch--read-required "Theorem name (empty cancels): ")))
  (vnb-launch--send-tactic (format "(ta '%s)" name)))

(defun vnb-pf-instantiate (formula term)
  "Instantiate FORALL hypothesis FORMULA at TERM.  Wraps (inst FORMULA TERM)."
  (interactive
   (list (vnb-launch--read-required "FORALL hypothesis to instantiate (type as shown, no quotes): ")
         (vnb-launch--read-required "Term: ")))
  (vnb-launch--send-tactic (format "(inst %S %S)"
                                   (vnb-launch--dequote formula)
                                   (vnb-launch--dequote term))))

(defun vnb-pf-exists-witness (term)
  "Supply TERM as a witness for the current FORSOME goal.  Wraps (ew TERM)."
  (interactive
   (list (vnb-launch--read-required "Witness term for the FORSOME goal (type as shown, no quotes): ")))
  (vnb-launch--send-tactic (format "(ew %S)" (vnb-launch--dequote term))))

(defun vnb-pf-backchain (formula)
  "Backchain on FORMULA = (IMPLIES p goal).  Wraps (bc FORMULA).
FORMULA may be an assumption's number (as shown in the Focus Workspace),
in which case it is sent as a bare index, e.g. (bc 2)."
  (interactive
   (list (vnb-launch--read-required "Backchain on assumption # or implication (type as shown): ")))
  (let ((arg (vnb-launch--dequote formula)))
    (vnb-launch--send-tactic
     (if (string-match-p "\\`[0-9]+\\'" arg)
         (format "(bc %s)" arg)
       (format "(bc %S)" arg)))))

(defun vnb-pf-backchain-star (name)
  "Cite the NAMED theorem/axiom NAME against the current goal.
Wraps (bc* 'NAME ()): peels NAME's leading FORALL/IMPLIES and matches its
CONCLUSION to the goal, then spawns one subgoal per hypothesis of NAME for
you to discharge with the palette.  This is the workhorse \"use a library
lemma\" move -- distinct from `b' (vnb-pf-backchain), the primitive
backchain on a bare implication/assumption.

This button always sends empty bindings.  If the conclusion leaves a schema
variable undetermined, pin it from the `r' Scratch Pad with
`(bc* 'NAME ((v val)...))' -- that still proceeds step by step: it spawns the
subgoals for you to discharge with the palette.  The further handler form
`(bc* 'NAME (...) h1 ...)' (one tactic-thunk per hypothesis) is NOT an
interactive move -- it needs the hypothesis count known up front and is a batch
convenience for proof FILES like scratch-roadtest.scm; interactively you just
let this button spawn the subgoals and close each with Assume etc.
NB: bc* cannot match a conclusion whose head is a structure accessor like
((MUL s) x y)."
  (interactive
   (list (vnb-launch--read-required
          "Cite lemma -- theorem/axiom name (empty cancels): ")))
  (vnb-launch--send-tactic (format "(bc* '%s ())" (vnb-launch--dequote name))))

(defun vnb-pf-focus (n)
  "Switch focus to the N-th open goal (1-based).  Wraps (focus N).
A non-positive index cancels."
  (interactive (list (read-number "Focus on which open goal (1-based; 0 cancels): " 1)))
  (when (or (not (integerp n)) (< n 1))
    (user-error "Cancelled"))
  (vnb-launch--send-tactic (format "(focus %d)" n)))

(defun vnb-pf-qed (name)
  "Install the completed proof as theorem NAME.  Wraps (qed 'NAME)."
  (interactive
   (list (vnb-launch--read-required "Install proof as theorem name: ")))
  (vnb-launch--send-tactic (format "(qed '%s)" name)))

(defun vnb-pf-show-repl ()
  "Pop to the Scratch Pad (the raw *VNB* command window) full-frame (advanced).
The State buffer's content is already in Focus/Overview, so we don't
split it in.  Use the VNB menu (or `o' / `f' / `h' from a workspace)
to navigate back."
  (interactive)
  (vnb-launch--ensure-prover)
  (let ((repl (get-buffer vnb-buffer-name)))
    (delete-other-windows)
    (switch-to-buffer repl)
    (goto-char (point-max))))

(defun vnb-ws-scratch-workspace ()
  "Open the Scratch Workspace: a lisp-interaction-style sheet for VNB.
Like the Emacs *scratch* buffer, but \\<vnb-command-mode-map>\\[vnb-command-eval-print]
sends the S-expression before point — or, with a region active, the region
as a (begin ...) block — to the running prover and inserts the result on the
next line.  Distinct from the raw Scratch Pad REPL (which just scrolls)."
  (interactive)
  (vnb-launch--ensure-prover)
  (vnb-command-buffer))

;;; Subscribe to state updates and to error events from the prover.
(add-hook 'vnb-state-update-hook 'vnb-launch--on-state-update)
(add-hook 'vnb-error-hook        'vnb-launch--on-vnb-error)

;;; -----------------------------------------------------------------------
;;; Build Structure: define a new structure and save it to structure-library/

(defvar vnb-structure-buffer-name "*VNB Structure*"
  "Name of the Build Structure scratch buffer.")

(defvar vnb-structure-template "\
;; ============================================================
;; BUILD STRUCTURE     C-c C-s = Save & Load     C-c C-k = Cancel
;; ============================================================
;;
;; Edit the declare-structure form below.  The NAME symbol becomes the
;; file name structure-library/<name>.scm (lowercased).  Save writes the
;; file, evaluates it in the running prover so the structure is usable
;; immediately, and registers it for auto-load on next launch.
;;
;; Clauses:
;;   (carriers C1 C2 ...)        one or more carrier set names
;;   (op   OP   (D1 D2 ...) R)   operation OP : D1 x ... x Dn -> R
;;   (constant CONST DOMAIN)     distinguished element

(declare-structure NAME
  (carriers ELEMENTS)
  (op PLUS  (ELEMENTS ELEMENTS) ELEMENTS)
  (op TIMES (ELEMENTS ELEMENTS) ELEMENTS))

;; --- characterising axioms ---
;; After saving, type axioms in the *VNB Commands* scratch sheet
;; (M-x vnb-command-buffer):
;;
;;   (theory-add-axiom! *current-theory* 'name-of-axiom
;;     '(FORALL s (IMPLIES (IS-NAME s) ...)))
"
  "Initial content inserted into a fresh Build Structure buffer.")

(defvar vnb-structure-mode-map
  (let ((m (make-sparse-keymap)))
    (set-keymap-parent m (if (boundp 'scheme-mode-map) scheme-mode-map nil))
    (define-key m (kbd "C-c C-s") 'vnb-structure-save)
    (define-key m (kbd "C-c C-k") 'vnb-structure-cancel)
    m)
  "Keymap for Build Structure buffer.")

(define-derived-mode vnb-structure-mode scheme-mode "VNB-Structure"
  "Major mode for the Build Structure scratch buffer.
\\<vnb-structure-mode-map>
Edit the declare-structure form, then \\[vnb-structure-save] to save."
  (setq truncate-lines nil))

(defun vnb-launch--parse-structure-name ()
  "Read the first declare-structure form in the current buffer; return its
NAME symbol.  Signals a `user-error' with a clear message on failure."
  (let* ((src  (buffer-substring-no-properties (point-min) (point-max)))
         (form (condition-case err
                   (car (read-from-string src))
                 (error (user-error "Cannot read the buffer: %s"
                                    (error-message-string err))))))
    (unless (and (consp form) (eq (car form) 'declare-structure))
      (user-error "First form must be (declare-structure NAME ...)"))
    (unless (and (cdr form) (symbolp (cadr form)))
      (user-error "Structure name (after declare-structure) must be a symbol"))
    (cadr form)))

(defun vnb-launch--user-additions-path ()
  (expand-file-name "structure-library/user-additions.scm" vnb-launch--dir))

(defun vnb-launch--append-user-addition (rel-path)
  "Append `(load \"REL-PATH\")' to user-additions.scm, unless already present."
  (let* ((file (vnb-launch--user-additions-path))
         (line (format "(load \"%s\")\n" rel-path)))
    (with-temp-buffer
      (when (file-exists-p file)
        (insert-file-contents file))
      (unless (save-excursion
                (goto-char (point-min))
                (search-forward line nil t))
        (goto-char (point-max))
        (unless (bolp) (insert "\n"))
        (insert line)
        (write-region (point-min) (point-max) file nil 'silent)))))

(defun vnb-structure-save ()
  "Save the current Build Structure buffer.
Writes structure-library/<name>.scm (lowercased), loads it in the running
prover so it is usable immediately, and registers it in
structure-library/user-additions.scm for auto-load on next launch."
  (interactive)
  (let* ((name       (vnb-launch--parse-structure-name))
         (lc         (downcase (symbol-name name)))
         (target-rel (format "structure-library/%s.scm" lc))
         (target-abs (expand-file-name target-rel vnb-launch--dir)))
    (when (and (file-exists-p target-abs)
               (not (yes-or-no-p (format "Overwrite %s? " target-rel))))
      (user-error "Cancelled"))
    (let ((content (buffer-substring-no-properties (point-min) (point-max))))
      (with-temp-file target-abs
        (insert content)))
    (vnb-launch--ensure-prover)
    (setq vnb--last-error nil)
    (vnb-eval-string (format "(load \"%s\")" target-abs))
    (cond
     (vnb--last-error
      (message "Wrote %s but load failed: %s  (edit and re-save)"
               target-rel vnb--last-error))
     (t
      (vnb-launch--append-user-addition target-rel)
      (message "Saved %s; loaded now; auto-load on next launch."
               target-rel)))))

(defun vnb-structure-cancel ()
  "Discard the Build Structure buffer and return to the Home Workspace."
  (interactive)
  (when (yes-or-no-p "Discard this structure? ")
    (kill-buffer)
    (vnb-launch-workspace)))

(defun vnb-ws-build-structure ()
  "Open the *VNB Structure* buffer with a declare-structure template."
  (interactive)
  (let ((buf (get-buffer-create vnb-structure-buffer-name)))
    (with-current-buffer buf
      (unless (eq major-mode 'vnb-structure-mode)
        (vnb-structure-mode))
      (when (= (point-min) (point-max))
        (insert vnb-structure-template)
        (goto-char (point-min))
        (when (search-forward "NAME" nil t)
          (forward-char -4)
          (push-mark (point) t t)
          (forward-char 4))))
    (delete-other-windows)
    (switch-to-buffer buf)))

;;; -----------------------------------------------------------------------
;;; Examples: a listing buffer over examples/*.scm, plus a step-through
;;; mode where RET on a script line sends just that line to the REPL.

(defvar vnb-examples-buffer-name "*VNB Examples*"
  "Name of the buffer listing available worked example proofs.")

(defun vnb-launch--examples-dir ()
  (expand-file-name "examples" vnb-launch--dir))

(defun vnb-launch--example-files ()
  "Return the .scm files in examples/, sorted by name."
  (let ((dir (vnb-launch--examples-dir)))
    (when (file-directory-p dir)
      (sort (directory-files dir t "\\.scm\\'") #'string<))))

(defun vnb-launch--example-title (path)
  "Extract `;;; Title: ...' from PATH, or fall back to its base name."
  (with-temp-buffer
    (insert-file-contents path nil 0 2000)
    (goto-char (point-min))
    (if (re-search-forward "^;;;[ \t]*Title:[ \t]*\\(.*?\\)[ \t]*$" nil t)
        (match-string-no-properties 1)
      (file-name-base path))))

(defvar vnb-examples-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m (kbd "RET")     'vnb-examples-open)
    (define-key m (kbd "<down>")  'next-line)
    (define-key m (kbd "<up>")    'previous-line)
    (define-key m "n"             'next-line)
    (define-key m "p"             'previous-line)
    (define-key m "g"             'vnb-ws-examples)
    (define-key m "q"             'quit-window)
    m)
  "Keymap for `vnb-examples-mode'.")

(define-derived-mode vnb-examples-mode special-mode "VNB-Examples"
  "Major mode for the VNB Examples listing buffer.
\\<vnb-examples-mode-map>
\\[vnb-examples-open]      open the example at point in a step-through script window.
\\[vnb-ws-examples]      refresh the listing (re-scan examples/).
\\[quit-window]      bury the buffer."
  (setq buffer-read-only t)
  (setq truncate-lines nil)
  (vnb-launch--apply-faces))

(defun vnb-ws-examples ()
  "Open the Examples listing buffer (scans examples/*.scm)."
  (interactive)
  (let ((buf (get-buffer-create vnb-examples-buffer-name)))
    (with-current-buffer buf
      (vnb-examples-mode)
      (let ((inhibit-read-only t)
            (files (vnb-launch--example-files)))
        (erase-buffer)
        (insert "\n")
        (insert (propertize "  VNB Examples\n" 'face 'vnb-title))
        (insert "\n")
        (insert (propertize
                 "  Worked example proofs.  Click or press RET to open one;\n"
                 'face 'vnb-body))
        (insert (propertize
                 "  in the script window, RET sends one line at a time.\n\n"
                 'face 'vnb-body))
        (cond
         ((null files)
          (insert (propertize "  (no example files found in examples/)\n"
                              'face 'vnb-dim)))
         (t
          (dolist (f files)
            (insert "  ")
            (insert-text-button
             (vnb-launch--example-title f)
             'face 'vnb-library-link
             'mouse-face 'vnb-button-mouse
             'follow-link t
             'help-echo (format "Open %s" (file-name-nondirectory f))
             'vnb-example-file f
             'action (lambda (btn)
                       (vnb-launch--show-example
                        (button-get btn 'vnb-example-file))))
            (insert "\n"))))
        (insert "\n")
        (insert (propertize
                 "  RET open   n/p navigate   g refresh   q quit\n"
                 'face 'vnb-dim))
        (goto-char (point-min))
        (forward-line 5)))
    (delete-other-windows)
    (switch-to-buffer buf)))

(defun vnb-examples-open ()
  "Open the example at point."
  (interactive)
  (let ((btn (button-at (point))))
    (if btn
        (vnb-launch--show-example (button-get btn 'vnb-example-file))
      (user-error "Point is not on an example"))))

(defvar vnb-example-script-mode-map
  (let ((m (make-sparse-keymap)))
    (set-keymap-parent m (if (boundp 'scheme-mode-map) scheme-mode-map nil))
    (define-key m (kbd "RET")     'vnb-example-send-line)
    (define-key m (kbd "C-c C-n") 'vnb-example-send-line)
    (define-key m (kbd "C-c C-q") 'quit-window)
    m)
  "Keymap for `vnb-example-script-mode'.")

(define-derived-mode vnb-example-script-mode scheme-mode "VNB-Example"
  "Major mode for a worked example proof script.
RET on a line sends just that line to the prover REPL and advances.
Blank lines and comment-only lines are skipped silently."
  (setq buffer-read-only t)
  (setq truncate-lines nil))

(defun vnb-launch--show-example (path)
  "Open PATH read-only in `vnb-example-script-mode' next to the REPL."
  (vnb-launch--ensure-prover)
  (let ((buf (find-file-noselect path)))
    (with-current-buffer buf
      (unless (eq major-mode 'vnb-example-script-mode)
        (vnb-example-script-mode))
      (goto-char (point-min)))
    (delete-other-windows)
    (let ((repl (get-buffer vnb-buffer-name)))
      (when repl
        (switch-to-buffer repl)
        (goto-char (point-max))))
    (split-window nil nil t)
    (set-window-buffer (next-window) buf)
    (select-window (next-window))))

(defun vnb-example-send-line ()
  "Send the current line to the prover REPL; advance to the next line.
Blank lines and comment-only lines (starting with `;') are skipped."
  (interactive)
  (let* ((raw     (buffer-substring-no-properties
                   (line-beginning-position) (line-end-position)))
         (trimmed (string-trim raw)))
    (cond
     ((string-empty-p trimmed))
     ((string-prefix-p ";" trimmed))
     (t (vnb-launch--send trimmed)))
    (forward-line 1)))

;;; -----------------------------------------------------------------------
;;; Auto-launch when loaded by the VNB shell script.
;;;
;;; We DEFER to `window-setup-hook' (runs after `emacs-startup-hook')
;;; AND wrap in a short `run-at-time' so the workspace fires only after
;;; the WM has had a chance to map the initial graphical frame.  If we
;;; ran inline during -l loading, `set-frame-parameter' calls (ours and
;;; the prefs file's) target a half-built frame, and Emacs's own startup
;;; later overwrites them -- the classic "loads correctly only via M-x
;;; load-file" symptom.
;;;
;;; Skip in batch mode so the file can be byte-loaded for syntax checks.
(unless noninteractive
  (add-hook 'window-setup-hook
            (lambda ()
              (run-at-time 0.3 nil 'vnb-launch-workspace))))

(provide 'vnb-launch)
;;; vnb-launch.el ends here
