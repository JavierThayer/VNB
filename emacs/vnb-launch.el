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

(defconst vnb-launch--docs-dir
  (file-name-as-directory (expand-file-name "docs" vnb-launch--dir))
  "Hand-written prose: design notes and working notes (docs/NAME.md).

Distinct from `vnb-launch--ref-dir', which the prover REGENERATES on every
load.  Nothing in docs/ is generated, so nothing in it is refreshed for you;
`vnb-view-note' reads whatever is on disk.")

(load (expand-file-name "vnb.el" vnb-launch--el-dir) nil t)

;; Auto-derived interactive commands for the no-argument tactics, read from the
;; generated command catalog (emacs/vnb-commands.lisp).  Defines M-x vnb-cmd-*
;; for every kind-0 tactic; the "No-arg Tactics" menu is installed into the
;; Focus keymap just below (after `vnb-proof-mode-map' is defined).
(load (expand-file-name "vnb-cmd-gen.el" vnb-launch--el-dir) nil t)

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
  '((t :foreground "#e0e0e0"))
  "Default text in VNB workspace buffers.  Deliberately carries NO background:
workspace buffers inherit the frame `background-color' (set by
vnb-launch-colors, overridable in ~/.vnb-display.el), so a single knob -- the
frame background -- controls every background, REPL and workspace alike."
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

(defface vnb-comment
  '((t :inherit vnb-default :foreground "#9fb3c8"))
  "Comment / read-only header text in scheme-derived workspaces.
Readable secondary colour on the dark frame -- replaces the stock
`font-lock-comment-face', which is barely legible on the dark teal
background (and used for the `;;;' headers of worked-example scripts)."
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

(defun vnb-launch--readable-comments ()
  "Remap scheme/lisp comment faces to the readable `vnb-comment'.
Scheme-derived workspaces (Build Structure, worked-example scripts) inherit
the stock `font-lock-comment-face' / `font-lock-comment-delimiter-face',
which are barely legible on the dark frame -- and they paint the `;;;'
header lines of example scripts.  Remapping both buffer-locally fixes the
readability and gives the leading `;'/`;;'/`;;;' the same colour as the
comment text, so the semicolons no longer clash at line starts."
  (face-remap-add-relative 'font-lock-comment-face 'vnb-comment)
  (face-remap-add-relative 'font-lock-comment-delimiter-face 'vnb-comment))

;;; -----------------------------------------------------------------------
;;; Workspace mode and buffer

(defvar vnb-workspace-buffer-name "*VNB Workspace*"
  "Name of the Home Workspace buffer.")

(defvar vnb-workspace-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m "g" 'vnb-ws-refresh)
    (define-key m "q" 'vnb-ws-quit)
    (define-key m "s" 'vnb-ws-start-proof)
    (define-key m "f" 'vnb-ws-what-is)
    (define-key m "b" 'vnb-ws-build-structure)
    (define-key m "t" 'vnb-ws-show-theorems)
    (define-key m "p" 'vnb-ws-show-pss)
    (define-key m "l" 'vnb-ws-browse-library)
    (define-key m "F" 'vnb-ws-show-fingerprints)
    (define-key m "d" 'vnb-describe-structure)
    (define-key m "D" 'vnb-ws-show-definitions)
    (define-key m "m" 'vnb-structure-manual)
    (define-key m "n" 'vnb-view-note)
    (define-key m "G" 'vnb-structure-graph-html)
    (define-key m "R" 'vnb-reference-html)
    (define-key m "H" 'vnb-home-html)
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
    (vnb-launch--insert-button "What Is…?"
                               'vnb-ws-what-is
                               "Look up a structure, number, or constant")
    (insert (propertize "   look up a structure, number, or constant — its accessors, shape, type\n\n" 'face 'vnb-body))
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
    (vnb-launch--insert-button "Notes"
                               'vnb-view-note
                               "Read a hand-written note from docs/ (design notes, working notes)")
    (insert (propertize "             hand-written notes in docs/, not generated\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Structure Graph"
                               'vnb-structure-graph-html
                               "Open the clickable structure graph (refines + view-as) in a browser")
    (insert (propertize "  refines & view-as relations as a clickable diagram\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Library (HTML)"
                               'vnb-reference-html
                               "Open the cross-linked HTML library reference (theorems, structures, PSS, indexes) in a browser")
    (insert (propertize "    whole library, cross-linked, in a browser\n\n"
                        'face 'vnb-body))
    (insert "  ")
    (vnb-launch--insert-button "Browser Home"
                               'vnb-home-html
                               "Open the HTML landing page: reference links stay in the browser, workbench links bounce back to Emacs")
    (insert (propertize "      HTML front door; workbench links return to Emacs\n\n"
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
                     "m manual  |  n notes\n"
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

;; `vnb-ws-start-proof' now opens the Start Proof Workspace -- a real editing
;; buffer for the goal formula, so long formulas are no longer cramped into a
;; one-line minibuffer prompt.  Its definition lives with that workspace's
;; machinery (search for "Start Proof Workspace" below), next to Build
;; Structure, which it mirrors.

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
  "Buffer name for the kid-facing arithmetic calculator sheet.")

(defvar vnb-calc-template "\
;; ────────────────────────────────────────────────────────────
;;  VNB CALCULATOR      C-j = work out this line      C-c C-k = close
;; ────────────────────────────────────────────────────────────
;;
;;  The same engine that checks proofs also does the sums.  Type an
;;  expression on its own line and press  C-j  -- the answer is written
;;  right after it.  Two kinds of expression work:
;;
;;    * NUMBERS  -- whole numbers with  +  -  *   (e.g. 2 * 3 * 5)
;;    * ALGEBRA  -- letters stand for unknowns; it multiplies the
;;                  brackets out and tidies up.  Use  ^  for powers, and
;;                  write  x*y  for \"x times y\"  (xy on its own would be
;;                  read as a single name).
;;
;;  Try these (put the cursor on a line and press C-j):
;; ────────────────────────────────────────────────────────────

2 + 3 + 5
10 - 4
2 * 3 * 5
(x + y)^2
(x + y)^2 - x*y
(x - y)*(x + y)
(a + b)^3
"
  "Initial content inserted into a fresh Calculator sheet.")
;; ordinary single-backslash LaTeX.

(defvar vnb-calc-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m (kbd "C-j")     'vnb-calc-eval-line)
    (define-key m (kbd "C-c C-c") 'vnb-calc-eval-line)
    (define-key m (kbd "C-c C-k") 'vnb-calc-cancel)
    m)
  "Keymap for the Calculator sheet.")

(define-derived-mode vnb-calc-mode prog-mode "VNB-Calc"
  "Major mode for the Calculator sheet -- a Scratch-style editable tape.
\\<vnb-calc-mode-map>Type an arithmetic expression on a line and \\[vnb-calc-eval-line]
to work it out in place; \\[vnb-calc-cancel] closes the sheet."
  (setq truncate-lines nil)
  (setq-local comment-start ";"))

(defun vnb-calc-eval-line ()
  "Work out the arithmetic expression on the current line, in place.
Sends it to the prover's vnb-guarded (calc ...) evaluator and appends
`=  answer' to the line, then opens a fresh line below.  Blank, comment
(`;'), and already-evaluated (`=') lines just get a newline."
  (interactive)
  (let* ((raw-line (buffer-substring-no-properties
                    (line-beginning-position) (line-end-position)))
         (expr     (string-trim raw-line)))
    (if (or (string= expr "")
            (string-prefix-p ";" expr)
            (string-match-p "=" expr))
        (progn (end-of-line) (insert "\n"))
      (vnb-launch--ensure-prover)
      (let* ((e   (vnb-launch--dequote expr))
             (rawv (vnb-eval-string (format "(calc %S)" e)))
             (ans (and rawv (string-trim rawv))))
        ;; A symbolic answer comes back as a quoted Scheme string
        ;; ("x ^ 2 + x * y + y ^ 2"); peel the quotes for display.
        (when (and ans (string-match "\\`\"\\(.*\\)\"\\'" ans))
          (setq ans (match-string 1 ans)))
        ;; Accept a numeric result OR a polynomial result (letters, digits,
        ;; + - * ^ ( ) and spaces).  The error message contains a colon, which
        ;; the charset excludes, so it is correctly rejected.
        (let ((ok (and ans (> (length ans) 0)
                       (string-match-p "\\`[-+ *^/.()0-9A-Za-z_]+\\'" ans))))
          (end-of-line)
          (insert (if ok (format "   =  %s" ans)
                    "   =  ?   (numbers, or algebra in  +  -  *  ^  -- write x*y, not xy)"))
          (insert "\n")
          (when ok (message "%s = %s" e ans)))))))

(defun vnb-calc-cancel ()
  "Close the Calculator sheet and return to the Home Workspace."
  (interactive)
  (kill-buffer)
  (vnb-launch-workspace))

(defun vnb-launch--protect-banner ()
  "Make the leading comment banner of the current buffer read-only.
Protects the contiguous run of comment (`;') lines at the top -- the workspace's
instruction header -- so it can't be edited or deleted by accident.  The body
below stays fully editable: the banner's trailing newline is `rear-nonsticky',
so typing on the first body line is allowed."
  (save-excursion
    (goto-char (point-min))
    (while (and (not (eobp)) (looking-at "^[ \t]*;"))
      (forward-line 1))
    (let ((end (point))
          (inhibit-read-only t))
      (when (> end (point-min))
        (add-text-properties (point-min) end
                             '(read-only t front-sticky t rear-nonsticky t))))))

(defun vnb-launch--accent-rule-lines ()
  "Paint the banner's `;; ───…' rule lines in the accent (pink) colour.
Uses overlays so the colour survives font-lock; the lines stay `;;' comments
\(so they're ignored when the workspace's contents are read), but read as the
same red/pink rules that fence off read-only regions elsewhere."
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^;;[ \t]*─+[ \t]*$" nil t)
      (let ((ov (make-overlay (match-beginning 0) (match-end 0))))
        (overlay-put ov 'face 'vnb-accent)
        ;; Sit above the whole-banner dim overlay laid by
        ;; `vnb-launch--paint-banner' so the pink rules still show.
        (overlay-put ov 'priority 1)))))

(defun vnb-launch--paint-banner ()
  "Paint the leading read-only comment banner in one uniform face.
The banner lines are `;'-comments (so the prover ignores them when the
workspace's contents are read), but in a scheme-derived workspace -- Build
Structure uses `scheme-mode' -- font-lock would otherwise colour the text
with `font-lock-comment-face' and the leading `;;'/`;;;' with
`font-lock-comment-delimiter-face': two clashing colours that make the
semicolons stand out at the start of every banner line.  An overlay (which
layers above font-lock's text-property faces) repaints the whole run as dim
secondary text, so the header reads as uniform read-only chrome regardless
of the buffer's major mode.  Call before `vnb-launch--accent-rule-lines',
which re-overlays the `;; ───' rules in accent pink at a higher priority."
  (save-excursion
    (goto-char (point-min))
    (while (and (not (eobp)) (looking-at "^[ \t]*;"))
      (forward-line 1))
    (let ((end (point)))
      (when (> end (point-min))
        (let ((ov (make-overlay (point-min) end)))
          (overlay-put ov 'face 'vnb-comment)
          (overlay-put ov 'priority 0))))))

(defun vnb-ws-calculator ()
  "Open the *VNB Calculator*: a Scratch-style editable tape.
\\<vnb-calc-mode-map>Type an arithmetic expression on a line and press \\[vnb-calc-eval-line] to work it
out right there -- the same prover that checks proofs also does the sums."
  (interactive)
  (vnb-launch--ensure-prover)
  (let ((buf (get-buffer-create vnb-calculator-buffer-name)))
    (with-current-buffer buf
      (unless (eq major-mode 'vnb-calc-mode)
        (vnb-calc-mode))
      (when (= (point-min) (point-max))
        (insert vnb-calc-template)
        (vnb-launch--protect-banner)
        (vnb-launch--paint-banner)
        (vnb-launch--accent-rule-lines)
        (goto-char (point-max))))
    (delete-other-windows)
    (switch-to-buffer buf)))

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
;;; Read a hand-written note (docs/NAME.md).
;;;
;;; The reference viewers above each ask the prover to regenerate their .md
;;; first.  This one does not, and must not: docs/ is prose, not output, and
;;; there is nothing to regenerate.  So `vnb-view-note' works with no prover
;;; running.

(defvar-local vnb-view-note--path nil
  "Absolute path of the note file shown in this buffer.")

(defun vnb-view-note--names ()
  "Basenames of the markdown notes in `vnb-launch--docs-dir', sorted."
  (sort (mapcar #'file-name-nondirectory
                (file-expand-wildcards
                 (expand-file-name "*.md" vnb-launch--docs-dir)))
        #'string<))

(defun vnb-view-note (&optional name)
  "Read the hand-written note docs/NAME.md in a `vnb-library-mode' buffer.

Prompts with completion over the notes on disk.  The buffer is a VIEWER, not
a visit: to edit the note, open the file itself -- its path is in the buffer
local `vnb-view-note--path'.

Needs no prover, because docs/ is prose and not generated (unlike
reference/, which every other viewer here regenerates first)."
  (interactive
   (list (let ((names (vnb-view-note--names)))
           (unless names
             (user-error "No .md notes in %s" vnb-launch--docs-dir))
           (completing-read "VNB note: " names nil t))))
  (let* ((path (expand-file-name name vnb-launch--docs-dir))
         (buf  (get-buffer-create
                (format "*VNB Note: %s*" (file-name-sans-extension name)))))
    (unless (file-exists-p path)
      (user-error "No such note: %s" path))
    (with-current-buffer buf
      (let ((inhibit-read-only t))       ; already in library-mode on a re-open
        (erase-buffer)
        (insert-file-contents path))
      (goto-char (point-min))
      (setq-local default-directory vnb-launch--dir)
      (vnb-library-mode)                 ; kills buffer-locals: set ours AFTER
      (setq-local vnb-view-note--path path)
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
;;; Focus Workspace inline-PNG toggle: render the LIVE focused sequent's
;;; assumptions and goal as LaTeX images instead of infix text.
;;;
;;; The prover emits TeX for the focused sequent (`write-sequent-tex' in
;;; tex-output.scm); we cache it stamped with the proof-state text it
;;; belongs to, paint the sequent block with $...$ spans, then let
;;; `vnb-tex-render-buffer' turn the spans into cached PNGs (dvipng).
;;;
;;; Re-entrancy: `vnb-state-update-hook' fires INSIDE the comint process
;;; filter, and `vnb-eval-string' sends-and-waits, so the prover round-trip
;;; must NOT run there.  The fetch is deferred with `run-at-time' after each
;;; state update; the deferred fetch caches the TeX and repaints.  The first
;;; (synchronous) paint after a step shows text; images appear a beat later.

(defvar vnb-focus-render-tex nil
  "When non-nil, the Focus Workspace renders the sequent as LaTeX images.
Toggle with `T' in the Focus Workspace (`vnb-pf-toggle-tex').")

(defvar vnb-pf--tex-cache nil
  "Cached focused-sequent TeX, or nil.
Shape: (:for STATE-TEXT :data PLIST), PLIST as written by the prover's
`write-sequent-tex' (symbol keys status/count/assumptions/goal).  Used
only while :for matches `vnb-proof--last-state', so stale TeX never shows.")

(defun vnb-pf--tex-data-for-current-state ()
  "Return the cached sequent-TeX PLIST if it matches the current state, else nil."
  (and vnb-pf--tex-cache
       (equal (plist-get vnb-pf--tex-cache :for) vnb-proof--last-state)
       (plist-get vnb-pf--tex-cache :data)))

(defun vnb-pf--prover-live-p ()
  "Non-nil when the VNB prover process is running."
  (let* ((buf  (get-buffer vnb-buffer-name))
         (proc (and buf (get-buffer-process buf))))
    (and proc (eq (process-status proc) 'run))))

(defun vnb-pf--fetch-tex ()
  "Round-trip the prover for the focused sequent's TeX, cache it, repaint.
Runs OUTSIDE the comint filter (scheduled via `run-at-time').  No-op
unless the Focus Workspace is live, the toggle is on, and the prover is up."
  (when (and vnb-focus-render-tex
             (get-buffer vnb-proof-buffer-name)
             (vnb-pf--prover-live-p))
    (vnb-tex--ensure-cache-dir)
    (let ((state vnb-proof--last-state)
          (path  (expand-file-name "focus-sequent.el" vnb-tex-cache-dir)))
      (ignore-errors (delete-file path))
      (ignore-errors (vnb-eval-string (format "(write-sequent-tex %S)" path)))
      (when (file-exists-p path)
        (let ((data (ignore-errors
                      (with-temp-buffer
                        (insert-file-contents path)
                        (goto-char (point-min))
                        (read (current-buffer))))))
          (when data
            (setq vnb-pf--tex-cache (list :for state :data data))
            (vnb-pf-refresh)))))))

(defun vnb-pf-toggle-tex ()
  "Toggle LaTeX-image rendering of the sequent in the Focus Workspace."
  (interactive)
  (when (and (not vnb-focus-render-tex) (not (display-images-p)))
    (user-error "This display can't show images (e.g. -nw); TeX rendering needs a graphical frame"))
  (setq vnb-focus-render-tex (not vnb-focus-render-tex))
  (if vnb-focus-render-tex
      (progn
        (message "Focus: rendering sequent as LaTeX (rendering...)")
        (vnb-pf--fetch-tex))
    (setq vnb-pf--tex-cache nil)
    (vnb-pf-refresh)
    (message "Focus: showing sequent as text")))

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
    (define-key m "R" 'vnb-reference-html)
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

(defvar vnb-what-is-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m "g" 'vnb-what-is)        ; look up another
    (define-key m "w" 'vnb-what-is)
    (define-key m "q" 'quit-window)
    (define-key m "?" 'describe-mode)
    m)
  "Keymap for `vnb-what-is-mode'.")

(define-derived-mode vnb-what-is-mode special-mode "VNB-WhatIs"
  "Major mode for the What-Is lookup workspace.
\\{vnb-what-is-mode-map}"
  (setq buffer-read-only t truncate-lines nil))

(defun vnb-launch--insert-rule (&optional width)
  "Insert a horizontal accent rule (the red line) and a newline.
The reusable read-only-region delimiter -- used in place of `;;;' comment
margins to fence off a header."
  (insert (propertize (make-string (or width 64) ?─) 'face 'vnb-accent) "\n"))

(defun vnb-what-is--insert-header ()
  "Insert the What-Is workspace header: instructions fenced by accent rules
\(no `;;;' margins -- the red rules mark the read-only region)."
  (vnb-launch--insert-rule)
  (insert (propertize "  What Is — lookup workspace\n" 'face 'vnb-title))
  (insert (propertize "  Enter  M-x what-is  (or press  g) to look something up:\n" 'face 'vnb-body))
  (insert (propertize "  a structure name · a number · a named constant · a concept word\n" 'face 'vnb-body))
  (insert (propertize "  metric · ring · 7 · 1/2 · pi · %i · complex · number\n" 'face 'vnb-dim))
  (insert (propertize "  the answer appears below.   (g look up another · q quit)\n" 'face 'vnb-dim))
  (vnb-launch--insert-rule))

(defun vnb-what-is--render (body-inserter)
  "Show the `*VNB: What Is*' workspace: the banner header, then BODY-INSERTER.
Single window -- no REPL or proof-state split.  BODY-INSERTER is called with
point just below the header to fill in the empty-state hint or an answer."
  (vnb-launch--ensure-prover)
  (let ((buf (get-buffer-create "*VNB: What Is*")))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (vnb-what-is-mode)
        (setq-local default-directory vnb-launch--dir)
        (erase-buffer)
        (vnb-what-is--insert-header)
        (insert "\n")
        (funcall body-inserter)
        (goto-char (point-min))))
    (switch-to-buffer buf)
    (delete-other-windows)))

(defun vnb-ws-what-is ()
  "Open the What-Is lookup workspace (instructions; press `g' to look up).
This is what the launcher's `What Is…?' link/button opens -- it does NOT
prompt; it lands you in the workspace with the read-only header, and you
start a lookup from there with `g' or \\[execute-extended-command] what-is."
  (interactive)
  (vnb-what-is--render
   (lambda () (insert "    (nothing looked up yet — press  g  to begin)\n"))))

(defun vnb-what-is (name)
  "Look up NAME and show what it is, in the `*VNB: What Is*' workspace.
NAME may be a (partial, case-insensitive) structure name, a number, a named
constant (`pi', `%i'), or a concept word (`complex', `number').  Prompts with
`Name:'.  The answer -- a structure's parts/accessors and shape, a number's
place in the nn..cc tower, a constant's type, the family a word names -- is
rendered below the header, NOT split against the REPL or proof state.  Press
`g' to look up another, `q' to quit.  Front door to building a formula: find
what a structure is called and what its accessors are, then write the term."
  (interactive
   (list (completing-read
          "Name: " (or (vnb-structure--names) '()) nil nil
          (and (derived-mode-p 'vnb-library-mode 'vnb-structure-card-mode 'vnb-what-is-mode)
               (ignore-errors (vnb-tex--name-at-point))))))
  (setq name (string-trim name))
  (when (string-empty-p name) (user-error "No name given"))
  (vnb-launch--ensure-prover)
  (vnb-tex--ensure-cache-dir)
  (let ((path (expand-file-name "what-is.txt" vnb-tex-cache-dir)))
    (when (file-exists-p path) (delete-file path))      ; never show a stale answer
    (vnb-eval-string (format "(write-what-is %S \"%s\")" name path))
    (vnb-what-is--render
     (lambda ()
       (if (file-exists-p path)
           (insert-file-contents path)
         (insert (format "what-is: no response from the prover for \"%s\".\n" name)))))))

(defalias 'what-is 'vnb-what-is
  "So `M-x what-is' works as advertised.")

(defvar vnb-what-now-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m "g" 'vnb-what-now)       ; re-run on the current goal
    (define-key m "q" 'quit-window)
    (define-key m "?" 'describe-mode)
    m)
  "Keymap for `vnb-what-now-mode'.")

(define-derived-mode vnb-what-now-mode special-mode "VNB-WhatNow"
  "Major mode for the What-Now proof-advice workspace.
\\{vnb-what-now-mode-map}"
  (setq buffer-read-only t truncate-lines nil))

(defun vnb-what-now ()
  "Proof copilot: ask what to try on the current open subgoal.
Captures the advice -- the lane it picks (closer / backchain / decompose) and
the moves to try -- into the `*VNB: What Now*' workspace and drops you there
(single window), rather than dumping it in the REPL where you drive the proof.
In the workspace, `g' re-runs on the current goal, `q' returns to the proof.
Run during a live proof; with none in progress it just says so."
  (interactive)
  (vnb-launch--ensure-prover)
  (vnb-tex--ensure-cache-dir)
  (let ((path (expand-file-name "what-now.txt" vnb-tex-cache-dir))
        (buf  (get-buffer-create "*VNB: What Now*")))
    (when (file-exists-p path) (delete-file path))    ; never show stale advice
    (vnb-eval-string (format "(write-what-now \"%s\")" path))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (vnb-what-now-mode)
        (setq-local default-directory vnb-launch--dir)
        (erase-buffer)
        (vnb-launch--insert-rule)
        (insert (propertize "  What Now — what to try on the focused goal\n" 'face 'vnb-title))
        (vnb-launch--insert-rule)
        (insert "\n")
        (if (file-exists-p path)
            (insert-file-contents path)
          (insert "what-now: no response from the prover.\n"))
        ;; drop the `;;' REPL comment margins -- the red rules fence the region now
        (goto-char (point-min))
        (while (re-search-forward "^;; ?" nil t) (replace-match ""))
        (goto-char (point-min))))
    (switch-to-buffer buf)
    (delete-other-windows)))

(defalias 'what-now 'vnb-what-now
  "So `M-x what-now' works alongside `M-x what-is'.")

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
Default is nil -- your system default browser -- so VNB needs no particular
browser installed.  For a clean, chromeless view, set this to a string naming
GNOME Web (\"epiphany-browser\" on Debian/Ubuntu, \"epiphany\" elsewhere);
combined with `vnb-graph-browser-args' (\"--incognito-mode\", the default) it
opens a fresh window every time.  If the named browser is not installed we
fall back to the system default.
  string   -- an executable name or path, opened via `browse-url-generic'
              (e.g. \"epiphany-browser\", \"chromium\", \"surf\", \"qutebrowser\").
  nil      -- the `browse-url' default (your system default browser).
  function -- used as `browse-url-browser-function' (e.g. #\\='eww-browse-url
              to view inside Emacs -- note: EWW renders the SVG as a static
              image, so graph NODES aren't clickable there; the text reference
              links and #anchors still work)."
  :type '(choice (string :tag "Browser executable")
                 (const :tag "System default" nil)
                 (function :tag "browse-url function"))
  :group 'vnb)

(defcustom vnb-graph-browser-args '("--incognito-mode")
  "Extra command-line arguments passed to `vnb-graph-browser'.
The default `--incognito-mode' makes GNOME Web (epiphany) start with user
data READ-ONLY: it neither restores tabs from a previous session nor saves
this one, so the VNB browser always opens clean.  These args are epiphany-
specific; if you point `vnb-graph-browser' at another browser set this to its
equivalent (e.g. (\"--incognito\") for chromium/chrome) or nil.
Used only when `vnb-graph-browser' is a string naming an executable on PATH;
ignored for the system-default and in-Emacs (function) cases."
  :type '(repeat string)
  :group 'vnb)

(defvar vnb-launch--browser-procs nil
  "Browser processes VNB launched, so `vnb-ws-quit' can close them on exit.")

(defun vnb--browse-graph (url)
  "Open URL according to `vnb-graph-browser', falling back to the default.
When `vnb-graph-browser' names an executable, launch it directly (with
`vnb-graph-browser-args') and remember the process so `vnb-ws-quit' can close
the window on exit."
  ;; Load browse-url first so `browse-url-generic-program' is a declared
  ;; special var: under lexical-binding, let-binding it before the library
  ;; is loaded would create a lexical (not dynamic) binding that
  ;; `browse-url-generic' never sees -- the "works on the second try" bug.
  (require 'browse-url)
  (cond
   ((functionp vnb-graph-browser) (funcall vnb-graph-browser url))
   ((and (stringp vnb-graph-browser) (> (length vnb-graph-browser) 0))
    (if (executable-find vnb-graph-browser)
        ;; start-process (not browse-url) so we hold the handle: lets us pass
        ;; the incognito/no-restore args AND close the window at quit.
        (condition-case err
            (let ((proc (apply #'start-process "vnb-browser" nil
                               vnb-graph-browser
                               (append vnb-graph-browser-args (list url)))))
              (set-process-query-on-exit-flag proc nil)
              (push proc vnb-launch--browser-procs)
              proc)
          (error
           (message "vnb: could not launch %s (%s); using system default browser"
                    vnb-graph-browser (error-message-string err))
           (browse-url url)))
      (message "vnb-graph-browser %S not on PATH; using system default browser"
               vnb-graph-browser)
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

;;; The whole library as a set of cross-linked browser pages.  reference/*.md
;;; (the docs the prover writes on load) are compiled by build-reference-html.py
;;; into one standalone page per doc (THEOREMS.html, STRUCTURE-INDEX.html, ...)
;;; plus a reference.html hub that links them all.  Every page has a shared
;;; sidebar and every backticked name is hyperlinked to its entry (across pages
;;; when needed).  We open the hub.  Read-only and prover-independent -- it just
;;; renders files already on disk.
(defun vnb-reference-html ()
  "Build and open the cross-linked HTML library reference in a browser.
Compiles reference/*.md (theorems, structures, PSS, definitions, the
operator/macete/fingerprint indexes, proof-debt) into one standalone page per
doc plus a reference.html hub, opened via `vnb-graph-browser'.
Click any backticked name to jump to its entry.  Refreshes the .md by
reloading the prover; this command just renders whatever is on disk."
  (interactive)
  (unless (executable-find "python3")
    (user-error "`python3' not found on PATH -- needed to build the reference HTML"))
  (let ((py   (expand-file-name "build-reference-html.py" vnb-launch--ref-dir))
        (html (expand-file-name "reference.html" vnb-launch--ref-dir))
        (log  (get-buffer-create " *vnb-reference-html*")))
    (with-current-buffer log (erase-buffer))
    (let ((default-directory vnb-launch--ref-dir))
      (unless (eq 0 (call-process "python3" nil log nil py))
        (user-error "build-reference-html.py failed (see ` *vnb-reference-html*')")))
    (unless (file-exists-p html)
      (user-error "reference.html was not produced"))
    (vnb--browse-graph (concat "file://" html))
    (message "Opened library reference in %s: %s"
             (or vnb-graph-browser "default browser") html)))

;;; -----------------------------------------------------------------------
;;; Browser landing page (home.html) + a tiny localhost listener.
;;;
;;; The HTML front door lives in the browser: reference links open other HTML
;;; pages, workbench links fetch http://127.0.0.1:PORT/do?fn=NAME, and this
;;; listener dispatches NAME through a FIXED WHITELIST (never arbitrary eval),
;;; then raises the Emacs frame -- so proving stays in Emacs.  Bound to
;;; loopback only.

(defcustom vnb-home-port 8973
  "TCP port for the localhost listener that the browser landing page
\(home.html) pokes to invoke Emacs commands.  Bound to 127.0.0.1 only."
  :type 'integer :group 'vnb)

(defcustom vnb-lobby-first t
  "Graphical-mode front door.  When non-nil (the default), launching in a
window system makes the browser lobby (home.html) the front door: the frame is
set up and the listener started, the lobby opens in the browser, and Emacs
iconifies itself; clicking a Workbench link raises Emacs into the matching work
surface.  The in-Emacs landing menu is suppressed (still on \\[execute-extended-command] vnb-launch-workspace).
Set to nil to keep the old in-Emacs landing page in graphical mode.  Has no
effect in terminal (-nw) mode, where there is no browser and the in-Emacs Home
Workspace is always the front door."
  :type 'boolean :group 'vnb)

(defvar vnb--home-server nil
  "The home-page localhost listener process, or nil when not running.")

(defconst vnb--home-actions
  '(("start-proof"     . vnb-ws-start-proof)
    ("first-proof"     . vnb-ws-first-proof)
    ("continue-proof"  . vnb-launch--show-proof-workspace)
    ("scratch"         . vnb-ws-scratch-workspace)
    ("what-is"         . vnb-ws-what-is)
    ("build-structure" . vnb-ws-build-structure)
    ("calculator"      . vnb-ws-calculator)
    ("examples"        . vnb-ws-examples)
    ("save-session"    . vnb-ws-save-session))
  "Whitelist mapping home.html `fn=' names to commands.  ONLY these run; the
listener never evaluates arbitrary input from the socket.  Emacs is reserved
for WORK (start/continue proofs, scratch, building) -- reference reading lives
in the browser (reference.html), so there is no `workspace'/landing-page entry
here.  Each name must also appear in build-home-html.py's WORKBENCH table; the
two are kept in sync by hand.")

(defun vnb--home-respond (proc status)
  "Send a bodyless HTTP response with STATUS and close PROC."
  (ignore-errors
    (process-send-string
     proc (concat "HTTP/1.1 " status "\r\n"
                  "Access-Control-Allow-Origin: *\r\n"
                  "Content-Length: 0\r\nConnection: close\r\n\r\n"))
    (delete-process proc)))

(defun vnb--home-filter (proc data)
  "Parse the HTTP request line in DATA and dispatch a whitelisted action."
  (if (not (string-match "GET /do\\?fn=\\([A-Za-z0-9_-]+\\)" data))
      (vnb--home-respond proc "404 Not Found")
    (let ((cmd (cdr (assoc (match-string 1 data) vnb--home-actions))))
      (if (not cmd)
          (vnb--home-respond proc "403 Forbidden")
        (vnb--home-respond proc "204 No Content")
        ;; defer out of the process filter; raise Emacs so the user lands here.
        ;; call-interactively (not funcall) so commands that prompt -- Describe
        ;; Structure, What Is, ... -- read their input in Emacs as usual.
        (run-at-time 0 nil
                     (lambda ()
                       (ignore-errors (call-interactively cmd))
                       (when (display-graphic-p)
                         ;; pull Emacs up even if lobby-first iconified it
                         (ignore-errors (make-frame-visible (selected-frame))
                                        (raise-frame)
                                        (x-focus-frame (selected-frame))))))))))

(defun vnb--home-server-ensure ()
  "Start the loopback listener if it is not already up; return the port."
  (unless (and vnb--home-server (process-live-p vnb--home-server))
    (setq vnb--home-server
          (make-network-process
           :name "vnb-home" :server t :host 'local
           :service vnb-home-port :family 'ipv4 :coding 'utf-8
           :filter #'vnb--home-filter)))
  vnb-home-port)

(defun vnb-home-html ()
  "Open the VNB browser landing page (home.html) in a browser.
Reference links open other HTML pages; workbench links poke a localhost
listener that runs a whitelisted Emacs command and raises this frame, so
the actual proving keeps happening in Emacs."
  (interactive)
  (unless (executable-find "python3")
    (user-error "`python3' not found on PATH -- needed to build home.html"))
  (let ((port (vnb--home-server-ensure))
        (py   (expand-file-name "build-home-html.py" vnb-launch--ref-dir))
        (html (expand-file-name "home.html" vnb-launch--ref-dir))
        (log  (get-buffer-create " *vnb-home-html*")))
    (with-current-buffer log (erase-buffer))
    (let ((default-directory vnb-launch--ref-dir))
      (unless (eq 0 (call-process "python3" nil log nil py
                                  (number-to-string port)))
        (user-error "build-home-html.py failed (see ` *vnb-home-html*')")))
    (unless (file-exists-p html)
      (user-error "home.html was not produced"))
    (vnb--browse-graph (concat "file://" html))
    (message "Opened VNB browser home (listener on 127.0.0.1:%d)" port)))

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
  "Shut down the prover process and the VNB browser, then exit Emacs."
  (interactive)
  (when (yes-or-no-p "Quit VNB (this also exits Emacs and the VNB browser)? ")
    (let ((buf (get-buffer vnb-buffer-name)))
      (when (and buf (vnb--process-live-p buf))
        (let ((proc (get-buffer-process buf)))
          (when proc
            (set-process-query-on-exit-flag proc nil)
            (delete-process proc)))))
    ;; Close any browser windows VNB opened.  Best-effort: a window that was
    ;; handed off to an already-running instance, or closed by hand, is gone
    ;; already, so delete-process is a harmless no-op there.
    (dolist (proc vnb-launch--browser-procs)
      (when (process-live-p proc)
        (ignore-errors (delete-process proc))))
    (setq vnb-launch--browser-procs nil)
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
        '((background-color . "#133333")
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
            ;; A `load' aborts at the FIRST error, so everything after the
            ;; offending form silently never runs (this is how a bad line in
            ;; ~/.vnb-display.el made later settings -- e.g. vnb-graph-browser --
            ;; appear to be ignored).  Make the failure LOUD instead of leaving
            ;; only a status string nobody reads.
            (error
             (let ((msg (format "VNB: %s failed to load (settings after the error were NOT applied): %s"
                                vnb-launch-prefs-file (error-message-string err))))
               (display-warning 'vnb msg :error)
               (message "%s" msg)
               (format "load failed: %s" (error-message-string err)))))))))

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
    ["What Is..."         vnb-ws-what-is        t]
    ["Build Structure..." vnb-ws-build-structure t]
    ["Show Theorems"      vnb-ws-show-theorems  t]
    ["Show PSS"           vnb-ws-show-pss       t]
    ["Describe Structure..." vnb-describe-structure t]
    ["Definitions"        vnb-ws-show-definitions t]
    ["Structure Manual"   vnb-structure-manual  t]
    ["Read Note..."       vnb-view-note         t]
    ["Structure Graph"    vnb-structure-graph-html   t]
    ["Library (HTML)"     vnb-reference-html         t]
    ["Browser Home"       vnb-home-html              t]
    ["View as PDF"        vnb-view-as-pdf       t]
    ["Suggest Forward Moves" vnb-suggest-forward-moves t]
    "---"
    ["Home Workspace"     vnb-launch-workspace             t]
    ["Focus Workspace"    vnb-launch--show-proof-workspace t]
    ["Proof Overview"     vnb-launch--show-overview-workspace t]
    ["Scratch Workspace"  vnb-ws-scratch-workspace         t]
    ["Refresh"            vnb-ws-refresh                   t]
    "---"
    ("Proof"
      ["Direct Inference"     vnb-pf-direct-inference t]
      ["Decompose Hyp..."     vnb-pf-antecedent-inference t]
      ["Assume"               vnb-pf-assumption       t]
      ["Assume All"           vnb-pf-assume-all       t]
      ["B+ (auto-close)"      vnb-pf-bplus            t]
      ["Theorem..."           vnb-pf-theorem          t]
      ["Cite Lemma (fact)..." vnb-pf-fact             t]
      ["Univ. Instantiate..." vnb-pf-instantiate      t]
      ["Exist. Witness..."    vnb-pf-exists-witness   t]
      ["Rewrite Hyp..."       vnb-pf-rewrite-hyp      t]
      ["Sep-Membership Elim..."   vnb-pf-sep-elim     t]
      ["Complement Elim..."   vnb-pf-comp-elim        t]
      ["Big-Union Elim..."    vnb-pf-bigunion-elim    t]
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
  (tool-bar-local-item "search"     'vnb-ws-what-is
                       'vnb-tb-what-is       vnb-launch--toolbar-map
                       :help "Look up a structure, number, or constant")
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
  '((background-color . "#133333")
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
    ;; Mode line: light-grey, raised 3-D bevel (GNU Emacs analogue of XEmacs
    ;; modeline-shadow-thickness); a dimmer, recessed grey when inactive.
    (set-face-attribute 'mode-line nil
                        :background "Gray60" :foreground "black"
                        :box '(:line-width 3 :style released-button))
    (set-face-attribute 'mode-line-inactive nil
                        :background "Gray35" :foreground "Gray80"
                        :box '(:line-width 3 :style released-button))
    ;; Selection.
    (set-face-attribute 'region nil :background "#3a3a5a")
    ;; Minibuffer prompt.
    (set-face-attribute 'minibuffer-prompt nil
                        :foreground "#ffcc66" :weight 'bold)
    ;; Fringe (left/right gutter) -- blend with the teal frame.
    (set-face-attribute 'fringe nil :background "#133333")))

;;; -----------------------------------------------------------------------
;;; Entry point: open the workspace.

(defun vnb-launch--frame-setup ()
  "Frame/font/colour/minibuffer/menu setup shared by every entry path.
Must run before any VNB buffer is shown, graphical or terminal -- skipping it
is what leaves the frame with GNOME's tiny system font."
  ;; Tell Emacs to stop tracking GNOME's "system font" setting.  Without this,
  ;; on Ubuntu/GNOME the system font (often a proportional condensed sans-serif
  ;; like "TeX Gyre Heros Cn") keeps reasserting itself over our frame font --
  ;; VNB launches with a tiny unreadable window even though
  ;; `set-frame-parameter' returned cleanly.
  (when (boundp 'font-use-system-font)
    (setq font-use-system-font nil))
  ;; Let a prompting command (e.g. Describe Structure) be invoked while another
  ;; minibuffer prompt is already live, instead of erroring with "Command
  ;; attempted to use minibuffer while in minibuffer".  The depth indicator
  ;; shows a [N] marker; C-g backs out one level at a time.
  (setq enable-recursive-minibuffers t)
  (minibuffer-depth-indicate-mode 1)
  ;; Built-in defaults first, then user prefs LAST so they always win (whether
  ;; the prefs file updates the defvars or calls set-frame-parameter directly).
  (vnb-launch--apply-frame-params)
  (vnb-launch--apply-colors)
  (vnb-launch--apply-saved-font-size)
  (vnb-launch--load-prefs)
  (vnb-launch--install-menu)
  (vnb-launch--install-toolbar))

(defun vnb-launch-workspace ()
  "Create or switch to the in-Emacs Home Workspace (the full menu).
This is the front door in terminal (-nw) mode; in graphical mode the browser
lobby is the front door, but this stays available via \\[execute-extended-command] vnb-launch-workspace."
  (interactive)
  (vnb-launch--frame-setup)
  (let ((buf (get-buffer-create vnb-workspace-buffer-name)))
    (with-current-buffer buf
      (vnb-workspace-mode)
      (vnb-launch--paint-workspace))
    (switch-to-buffer buf)
    (delete-other-windows)))

(defvar vnb-lobby-buffer-name "*VNB Lobby*"
  "Name of the minimal graphical-mode lobby buffer (front door is the browser).")

(defun vnb-launch--show-lobby-splash ()
  "Show a minimal orienting buffer for graphical mode.  The real front door is
the browser lobby; there is no in-Emacs menu here -- work surfaces open in
Emacs when a Workbench link is clicked in the browser."
  (let ((buf (get-buffer-create vnb-lobby-buffer-name)))
    (with-current-buffer buf
      (special-mode)
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert "\n")
        (insert (propertize "  VNB Math Assistant" 'face 'vnb-title)) (insert "\n")
        (insert (propertize "  Front door: your browser" 'face 'vnb-heading)) (insert "\n\n")
        (insert (propertize (make-string 60 ?-) 'face 'vnb-accent)) (insert "\n\n")
        (insert (propertize "  The home page opened in your browser.\n" 'face 'vnb-body))
        (insert (propertize "  Reference reading happens there; click a Workbench link and\n" 'face 'vnb-body))
        (insert (propertize "  the matching work surface opens here in Emacs.\n\n" 'face 'vnb-body))
        (insert (propertize "  Reopen the lobby:   M-x vnb-home-html\n" 'face 'vnb-dim))
        (insert (propertize "  In-Emacs menu:      M-x vnb-launch-workspace\n" 'face 'vnb-dim))
        (insert (propertize "  Terminal instead:   launch with  VNB -nw\n" 'face 'vnb-dim)))
      (goto-char (point-min)))
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
  "Render a parsed sequent SEQ with assumptions one per line.
When `vnb-focus-render-tex' is on and matching prover TeX is cached, emit
the assumptions and goal as $...$ math spans (turned into PNGs by
`vnb-tex-render-buffer' after the buffer is painted); otherwise as text."
  (let ((texdata (and vnb-focus-render-tex
                      (vnb-pf--tex-data-for-current-state))))
    (if texdata
        (vnb-launch--render-sequent-block-tex seq texdata)
      (vnb-launch--render-sequent-block-text seq))))

(defun vnb-launch--render-sequent-block-text (seq)
  "Render a parsed sequent SEQ as styled infix text, assumptions one per line."
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

(defun vnb-launch--render-sequent-block-tex (seq texdata)
  "Render sequent SEQ using TEXDATA (the prover's focused-sequent TeX plist).
Each assumption and the goal go in as a $...$ span; `vnb-tex-render-buffer'
later replaces the spans with cached PNGs.  SEQ supplies the goal number
and the GROUNDED flag; TEXDATA supplies the LaTeX."
  (let ((num      (plist-get seq :num))
        (grounded (plist-get seq :grounded))
        (asms     (plist-get texdata 'assumptions))
        (goal     (plist-get texdata 'goal)))
    (insert "    ")
    (insert (propertize (format "[%d]" num) 'face 'vnb-dim))
    (insert "\n")
    (if (null asms)
        (progn (insert "      ")
               (insert (propertize "(no assumptions)" 'face 'vnb-dim))
               (insert "\n"))
      (let ((i 1))
        (dolist (a asms)
          (insert "      ")
          (insert (propertize (format "%d. " i) 'face 'vnb-dim))
          (insert "$" a "$")
          (insert "\n")
          (cl-incf i))))
    (insert "    ")
    (insert (propertize "⊢" 'face 'vnb-accent))
    (insert "  ")
    (insert "$" goal "$")
    (when grounded
      (insert "  ")
      (insert (propertize "[GROUNDED]" 'face 'vnb-dim)))
    (insert "\n")))

(defvar vnb-proof-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m "d" 'vnb-pf-direct-inference)
    (define-key m "D" 'vnb-pf-antecedent-inference) ; hyp-side dual of d
    (define-key m "a" 'vnb-pf-assumption)
    (define-key m "A" 'vnb-pf-assume-all)
    (define-key m "+" 'vnb-pf-bplus)
    (define-key m "=" 'vnb-pf-reflexivity)
    (define-key m "m" 'vnb-pf-rewrite)
    (define-key m "M" 'vnb-pf-rewrite-hyp)          ; hyp-side dual of m
    (define-key m "e" 'vnb-pf-sep-elim)
    (define-key m "t" 'vnb-pf-theorem)
    (define-key m "F" 'vnb-pf-fact)
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
    (define-key m "T" 'vnb-pf-toggle-tex)
    (define-key m "g" 'vnb-pf-refresh)
    m)
  "Keymap for the Focus Workspace buffer.")

;; Hang the auto-generated "No-arg Tactics" menu off the Focus keymap, so every
;; no-argument tactic is reachable by mouse as well as M-x vnb-cmd-NAME.
(vnb-cmdgen-install-menu vnb-proof-mode-map)

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
    (insert "\n\n")
    (insert (propertize "  ▸  M-x what-now" 'face 'vnb-accent))
    (insert (propertize "   — ask the copilot what to try on this goal\n" 'face 'vnb-body))
    (insert (propertize "  ▸  M-x what-is " 'face 'vnb-accent))
    (insert (propertize "  — look up a structure, number, or constant\n" 'face 'vnb-body))
    (insert (propertize
             "     (tactics run from the single-key shortcuts below, or the Scratch Workspace)\n"
             'face 'vnb-dim))
    (insert "\n")
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
             (concat "  Keys: d direct-inf  D decompose-hyp  a assume  A assume-all  "
                     "+ B+auto-close  = close(a=a)  "
                     "m rewrite  M rewrite-hyp  e sep-elim  "
                     "t theorem  F fact  i univ-inst  w witness  "
                     "b bc  B cite-lemma  f focus  q qed  o overview  "
                     "h home  r scratch-pad  S scratch-workspace  "
                     "T tex-toggle  W save-script  g refresh\n")
             'face 'vnb-dim))
    ;; Turn the $...$ spans the TeX renderer emitted into inline PNGs.
    (when (and vnb-focus-render-tex (vnb-pf--tex-data-for-current-state))
      (vnb-tex-render-buffer))
    (goto-char (point-min))))

(defun vnb-pf-refresh ()
  "Refresh the Proof Workspace.

PULL a fresh proof state from a live prover: re-emit (show), whose
VNB-STATE block flows back through the preoutput filter and triggers a
repaint via `vnb-launch--on-state-update'.  This recovers the display
whenever a state PUSH was missed -- e.g. the sp/tactic block arrived
before the workspace hook was wired, or the comint filter was wedged by a
reload -- which a cache-only repaint cannot do.

Repaint from the cache first (immediate, and the only effect when the
prover is not running).  Does NOT auto-start the prover, so refresh has no
window side effects."
  (interactive)
  (let ((buf (get-buffer vnb-proof-buffer-name)))
    (when buf
      (with-current-buffer buf
        (vnb-launch--paint-proof))))
  (let ((pbuf (get-buffer vnb-buffer-name)))
    (when (and pbuf (get-buffer-process pbuf))
      (comint-send-string pbuf "(show)\n"))))

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
    (when ob (with-current-buffer ob (vnb-launch--paint-overview)))
    ;; The first paint above shows text (no fresh TeX yet).  If the toggle
    ;; is on, fetch the new sequent's TeX OUTSIDE this comint filter and
    ;; repaint with images.  run-at-time defers past the filter so the
    ;; send-and-wait round-trip can't re-enter it.
    (when (and fb vnb-focus-render-tex)
      (run-at-time 0 nil #'vnb-pf--fetch-tex))))

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
  "Focus the open goal whose displayed node number is N, then switch to the
Focus Workspace.  N is the bracketed [N] node id from the overview, so we drive
the prover's `focus-id' (by node number), NOT `focus' (a 1-based position)."
  (vnb-launch--send-tactic (format "(focus-id %d)" n))
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

(defun vnb-pf--asm-arg (s)
  "Format an assumption selector S for splicing into a hyp-targeting tactic.
A bare assumption number -- the number the Focus Workspace shows next to each
assumption -- is passed through literally, so `(sep-me 2)' selects the 2nd
assumption (the SAME numbering the Scratch Pad uses; the two control surfaces
agree).  Anything else is treated as a formula and quoted with %S.  S is
assumed already `vnb-launch--dequote'd."
  (if (string-match-p "\\`[0-9]+\\'" s)
      s
    (format "%S" s)))

(defun vnb-pf--read-asm-arg (prompt)
  "Read an assumption selector with PROMPT: an assumption # or a formula.
Returns the splice-ready string (a bare index or a %S-quoted formula).
Empty input cancels.  Shared by every hypothesis-targeting Focus command so
they all accept `#N' identically -- the interactive counterpart of the
Scheme-side `->raw-formula/idx'."
  (vnb-pf--asm-arg (vnb-launch--dequote (vnb-launch--read-required prompt))))

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
it replaces matching pieces of the goal with the other side.

The name prompt offers SUGGESTIONS first: rules whose LHS pattern fingerprint-
matches a subterm of the current goal (via `suggest-rewrite-names'), ranked
most-specific first, with the top one as the RET default.  TAB lists them; the
full `(rewrite-names)' pool is the fallback, and any name can still be typed."
  (interactive
   (list (vnb-pf--read-name "(suggest-rewrite-names)" "(rewrite-names)"
                            "Rewrite goal using rule")))
  (vnb-launch--send-tactic (format "(mac '%s)" (vnb-launch--dequote name))))

(defun vnb-pf-assumption ()
  "Close the current goal if it matches an assumption.  Wraps (ass)."
  (interactive)
  (vnb-launch--send-tactic "(ass)"))

(defun vnb-pf-assume-all ()
  "Close EVERY open goal already discharged by an assumption.  Wraps (ass-all).
Order-independent sweep over all open goals -- the natural finisher after a
`B' (Cite Lemma) spawns several hypothesis subgoals, each closable by its own
context.  Goals not assumption-closable are left untouched."
  (interactive)
  (vnb-launch--send-tactic "(ass-all)"))

(defun vnb-pf-arith ()
  "Close a ground arithmetic goal by evaluation, e.g. 2 + 3 = 5.  Wraps (arith)."
  (interactive)
  (vnb-launch--send-tactic "(arith)"))

(defun vnb-pf-ring-simplify ()
  "Close an equality goal by ring normalization (handles variables).  Wraps (rs)."
  (interactive)
  (vnb-launch--send-tactic "(rs)"))

(defun vnb-pf-theorem (name)
  "Add the named theorem NAME to the current context.  Wraps (ta 'NAME).
The name prompt completes over the full `(theorem-names)' pool, floating the
lemmas whose conclusion fingerprint-matches the current goal
(`suggest-backchain-names') to the top -- the facts you are most likely about
to use.  TAB lists them; any name can still be typed."
  (interactive
   (list (vnb-pf--read-name "(suggest-backchain-names)" "(theorem-names)"
                            "Add theorem")))
  (vnb-launch--send-tactic (format "(ta '%s)" (vnb-launch--dequote name))))

(defun vnb-pf-fact (name terms)
  "Cite lemma NAME forward: add it, instantiate at TERMS, detach in-context
guards.  Wraps (fact 'NAME term...).

Unlike `t' (Theorem, which only ADDS the lemma via `ta'), `fact' ASSEMBLES
it -- peeling the lemma's leading FORALLs at the TERMS you give and
discharging hypotheses already in the assumptions -- so the instantiated,
detached consequent lands ready to use.

Reads the lemma name, then instantiation terms one at a time, the standard
variadic protocol: RET on an empty term finishes.  A lemma with no leading
FORALLs (e.g. null-rr-seq-exists) takes no terms -- just RET at the first
term prompt to send (fact 'NAME).  Terms are VNB surface syntax (s, f,
x(s)); they are parsed prover-side."
  (interactive
   (let ((nm   (vnb-pf--read-lemma-name))
         (ts   '())
         (more t)
         (i    1))
     (while more
       (let ((s (string-trim
                 (read-string
                  (format "Instantiation term %d (RET to finish): " i)))))
         (if (string-empty-p s)
             (setq more nil)
           (push s ts)
           (setq i (1+ i)))))
     (list nm (nreverse ts))))
  (vnb-launch--send-tactic
   (format "(fact '%s%s)"
           (vnb-launch--dequote name)
           (mapconcat (lambda (tm) (format " %S" tm)) terms ""))))

(defun vnb-pf-instantiate (formula term)
  "Instantiate a FORALL hypothesis at TERM.  Wraps (inst FORMULA TERM).
FORMULA may be the hypothesis's assumption # (as shown in the Focus Workspace)
instead of the retyped formula, e.g. (inst 1 n)."
  (interactive
   (list (vnb-launch--read-required "FORALL hypothesis: assumption # or formula (type as shown): ")
         (vnb-launch--read-required "Term: ")))
  (vnb-launch--send-tactic (format "(inst %s %S)"
                                   (vnb-pf--asm-arg (vnb-launch--dequote formula))
                                   (vnb-launch--dequote term))))

(defun vnb-pf-antecedent-inference (sel)
  "Decompose an ASSUMPTION by its top connective -- the hypothesis-side dual of
Direct Inference.  Wraps (ai SEL); SEL is an assumption # (as shown) or the
assumption formula.  Splits an AND hypothesis into its conjuncts, eliminates a
FORSOME hypothesis into a fresh witness plus its body, etc."
  (interactive
   (list (vnb-pf--read-asm-arg "Decompose which assumption (# or formula): ")))
  (vnb-launch--send-tactic (format "(ai %s)" sel)))

(defun vnb-pf-rewrite-hyp (name sel)
  "Rewrite an ASSUMPTION using named rule NAME -- the hypothesis-side dual of
Rewrite.  Wraps (mac-h 'NAME SEL); SEL is an assumption # (as shown) or the
assumption formula.  NAME must be an equation/biconditional, including a
defined-PREDICATE unfold.  (Functoid unfolds live in the macete table, not the
theorem table, so they can't be applied to a hypothesis this way -- unfold them
in the goal with Rewrite instead.)

The ASSUMPTION is read first so the rule prompt can offer SUGGESTIONS: rules
whose LHS pattern fingerprint-matches a subterm of THAT assumption (via
`suggest-rewrite-names-asm'), ranked most-specific first, top one as the RET
default.  TAB lists them; the `(rewrite-names)' pool is the fallback."
  (interactive
   (let ((sel (vnb-pf--read-asm-arg "Rewrite which assumption (# or formula): ")))
     (list (vnb-pf--read-name (format "(suggest-rewrite-names-asm %s)" sel)
                              "(rewrite-names)" "Rewrite hyp using rule")
           sel)))
  (vnb-launch--send-tactic (format "(mac-h '%s %s)" (vnb-launch--dequote name) sel)))

(defun vnb-pf-sep-elim (sel)
  "Eliminate a separation-membership assumption y in SEP(x, A, p).  Wraps
(sep-me SEL); SEL is an assumption # (as shown) or the assumption formula.
Adds y in A and p[x:=y] to the context."
  (interactive
   (list (vnb-pf--read-asm-arg "Sep-membership assumption to eliminate (# or formula): ")))
  (vnb-launch--send-tactic (format "(sep-me %s)" sel)))

(defun vnb-pf-comp-elim (sel)
  "Eliminate a complement-membership assumption y in COMP(A).  Wraps
(comp-me SEL); SEL is an assumption # (as shown) or the assumption formula."
  (interactive
   (list (vnb-pf--read-asm-arg "Complement-membership assumption to eliminate (# or formula): ")))
  (vnb-launch--send-tactic (format "(comp-me %s)" sel)))

(defun vnb-pf-bigunion-elim (sel)
  "Eliminate a big-union-membership assumption y in BIG-UNION(...).  Wraps
(bu-me SEL); SEL is an assumption # (as shown) or the assumption formula."
  (interactive
   (list (vnb-pf--read-asm-arg "Big-union-membership assumption to eliminate (# or formula): ")))
  (vnb-launch--send-tactic (format "(bu-me %s)" sel)))

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
  (vnb-launch--send-tactic
   (format "(bc %s)" (vnb-pf--asm-arg (vnb-launch--dequote formula)))))

(defun vnb-pf--name-list (form)
  "Eval FORM in the prover; parse its `(a b c)' result into a list of strings.
Splits on whitespace -- robust for the flat symbol lists `theorem-names' /
`suggest-backchain-names' return (names carry no internal spaces).  nil on a
missing/garbled response."
  (let ((raw (ignore-errors (vnb-eval-string form))))
    (when (and raw (string-match "(\\(.*\\))" raw))
      (split-string (match-string 1 raw) "[ \t\n]+" t))))

(defun vnb-pf--read-name (suggest-form pool-form label)
  "Read a name argument with index-driven completion.  Shared by every Focus
command whose argument is the NAME of a stored result -- Cite-Lemma (`bc*'),
Rewrite (`mac'/`mac-h'), Add-Theorem (`ta').

SUGGEST-FORM is a prover s-expression string returning a RANKED list of the
names most relevant to the current focus (e.g. `(suggest-backchain-names)',
`(suggest-rewrite-names)'); its results are offered first and the top one is
the RET default.  POOL-FORM returns the full fallback pool (e.g.
`(theorem-names)', `(rewrite-names)') so any other name can still be typed.
LABEL is the prompt noun (e.g. \"Cite lemma\").  Both forms are evaluated in
the prover via `vnb-pf--name-list'; this is the elisp counterpart of the
Scheme-side index facility, so the two surfaces complete from the same ranking.
TAB lists the ranked matches; empty input cancels."
  (vnb-launch--ensure-prover)
  (let* ((sugg    (vnb-pf--name-list suggest-form))
         (all     (vnb-pf--name-list pool-form))
         (ordered (delete-dups (append sugg all)))
         ;; identity sort so the index ranking survives into *Completions*
         ;; (completing-read sorts alphabetically otherwise).
         (table   (lambda (string pred action)
                    (if (eq action 'metadata)
                        '(metadata (display-sort-function . identity)
                                   (cycle-sort-function . identity))
                      (complete-with-action action ordered string pred))))
         (prompt  (if sugg
                      (format "%s [%d match; top: %s] (RET=top): "
                              label (length sugg) (car sugg))
                    (format "%s -- name (empty cancels): " label)))
         (input   (completing-read prompt table nil nil nil nil (car sugg))))
    (if (and (stringp input) (string-match-p "\\`[ \t]*\\'" input))
        (user-error "Cancelled")
      input)))

(defun vnb-pf--read-lemma-name ()
  "Read a Cite-Lemma name, offering goal-matched suggestions first.
Asks the prover `(suggest-backchain-names)' for lemmas whose conclusion
fingerprint-matches the current focus goal (the same index behind
`suggest-backchain'), ranks them ahead of the full `(theorem-names)' pool in
completion, and defaults to the top suggestion -- RET on empty input takes it.
TAB lists the ranked matches; any other name can still be typed freely."
  (vnb-pf--read-name "(suggest-backchain-names)" "(theorem-names)" "Cite lemma"))

;;; -----------------------------------------------------------------------
;;; Slice 4: completion-at-point for the s-expr / Scratch Workspace surface.
;;;
;;; The Focus readers above complete a name in the MINIBUFFER.  Here we give
;;; the SAME index to the surface where you TYPE the s-expression directly: a
;;; completion-at-point function that, when point is on the name argument of a
;;; name-taking command -- (mac 'R..., (bc* 'R..., (ta 'R... -- completes it
;;; against the live index (ranked suggestions first, full pool behind), and
;;; otherwise completes the command name itself.  TAB drives it (and corfu /
;;; company too, if the user runs them).  Same ranking the buttons use, inline.
;;; The lighter `(find-mac substr)' / `(find-thm substr)' REPL search is the
;;; grep-style counterpart for when you'd rather not complete at point.

(defvar vnb-launch--name-arg-commands
  '(("mac"   "(suggest-rewrite-names)"   "(rewrite-names)")
    ("mac-h" nil                         "(rewrite-names)")
    ("ta"    "(suggest-backchain-names)" "(theorem-names)")
    ("bc*"   "(suggest-backchain-names)" "(theorem-names)")
    ("fact"  "(suggest-backchain-names)" "(theorem-names)"))
  "Commands whose first argument is the NAME of a stored result.
Each entry is (HEAD SUGGEST-FORM POOL-FORM): inside that argument, ranked
names from SUGGEST-FORM (nil = none, e.g. `mac-h' whose ranking needs the
assumption that is typed later) come first, then the POOL-FORM fallback.  The
s-expr twin of the Focus `vnb-pf--read-name' readers -- same prover forms.")

(defun vnb-launch--ordered-table (names)
  "A completion table over NAMES preserving their order in *Completions*,
so the index ranking is not re-sorted alphabetically."
  (lambda (string pred action)
    (if (eq action 'metadata)
        '(metadata (display-sort-function . identity)
                   (cycle-sort-function . identity))
      (complete-with-action action names string pred))))

(defconst vnb-launch--name-token-chars "[:alnum:]_?!*+/<>=.-"
  "Characters making up a VNB command/result name token (for completion).")

(defun vnb-launch--capf-symbol-bounds ()
  "Bounds (START . END) of the name-ish token ending at point, or nil."
  (let ((end (point))
        (start (save-excursion
                 (skip-chars-backward vnb-launch--name-token-chars)
                 (point))))
    (and (< start end) (cons start end))))

(defun vnb-launch--capf-name-entry (tokstart)
  "If the token at TOKSTART is an argument of a name-taking command, return
that command's `vnb-launch--name-arg-commands' entry; else nil.  The head is
the first symbol of the innermost enclosing list; the token counts as an
argument only when it begins strictly after that head."
  (save-excursion
    (let ((open (car (last (nth 9 (syntax-ppss tokstart))))))
      (when open
        (goto-char (1+ open))
        (skip-chars-forward " \t\n")
        (let ((hstart (point)))
          (skip-chars-forward vnb-launch--name-token-chars)
          (and (> (point) hstart)        ; a head symbol exists
               (> tokstart (point))      ; token is AFTER it -> an argument
               (assoc (buffer-substring-no-properties hstart (point))
                      vnb-launch--name-arg-commands)))))))

(defun vnb-launch--capf-command-names ()
  "All VNB command names, for head-position completion.
Prefers the generated catalog `vnb-cmd--catalog' (single-sourced from the
Scheme registry); falls back to the static `vnb-commands-alist'."
  (cond
   ((and (boundp 'vnb-cmd--catalog) vnb-cmd--catalog)
    (mapcar (lambda (e) (symbol-name (car e))) vnb-cmd--catalog))
   ((boundp 'vnb-commands-alist) (mapcar #'car vnb-commands-alist))
   (t nil)))

(defun vnb-launch--command-capf ()
  "`completion-at-point-functions' entry for the VNB Scratch Workspace.
On the NAME argument of a name-taking command, complete against the live
index (ranked suggestions + pool, the relevant ones annotated); elsewhere
complete the command name.  Returns nil when there is nothing to complete, so
any other capf may still run."
  (let ((b (vnb-launch--capf-symbol-bounds)))
    (when b
      (let* ((start (car b)) (end (cdr b))
             (entry (vnb-launch--capf-name-entry start)))
        (if entry
            (let* ((sugg  (and (nth 1 entry)
                               (ignore-errors (vnb-pf--name-list (nth 1 entry)))))
                   (pool  (ignore-errors (vnb-pf--name-list (nth 2 entry))))
                   (names (delete-dups (append sugg pool))))
              (when names
                (list start end (vnb-launch--ordered-table names)
                      :exclusive 'no
                      :annotation-function
                      (lambda (c) (and (member c sugg) " ★goal")))))
          (let ((names (vnb-launch--capf-command-names)))
            (when names
              (list start end names :exclusive 'no))))))))

(defun vnb-launch--command-capf-setup ()
  "Install the s-expr-surface CAPF in this Scratch Workspace buffer and point
TAB at `completion-at-point' so it drives the live index."
  (add-hook 'completion-at-point-functions #'vnb-launch--command-capf nil t)
  (local-set-key (kbd "TAB") #'completion-at-point))

(add-hook 'vnb-command-mode-hook #'vnb-launch--command-capf-setup)

(defun vnb-pf--bc-undetermined (nm)
  "Ask the prover which schema vars citing NM leaves undetermined.
Returns the parsed (ok …)/(unknown)/(no-proof)/(no-match) sexp, or nil."
  (let ((raw (vnb-eval-string (format "(bc*-undetermined '%s)" nm))))
    (and raw (string-match "(\\(.*\\))" raw)
         (ignore-errors (car (read-from-string raw))))))

(defun vnb-pf--reduce-goal ()
  "Peel the focus goal's leading FORALL/IMPLIES (di); return the di count (0+)."
  (let ((raw (vnb-eval-string "(bc*-reduce-goal!)")))
    (or (and raw (ignore-errors (car (read-from-string (string-trim raw))))) 0)))

(defun vnb-pf-backchain-star (name)
  "Cite the NAMED theorem/axiom NAME against the current goal, prompting for
any schema variables its conclusion leaves undetermined.

Wraps (bc* 'NAME ...): peels NAME's leading FORALL/IMPLIES and matches its
CONCLUSION to the goal, then spawns one subgoal per hypothesis of NAME for you
to discharge with the palette.  This is the workhorse \"use a library lemma\"
move -- distinct from `b' (vnb-pf-backchain), the primitive backchain on a
bare implication/assumption.

The name prompt offers SUGGESTIONS first: lemmas whose conclusion fingerprint-
matches the current goal (via `suggest-backchain-names'), ranked most-specific
first, with the top one as the default.  RET takes it; TAB lists them; you can
still type any other name.

Because suggestions are ranked by the goal's EVENTUAL conclusion (the leading
FORALL/IMPLIES is peeled before fingerprinting), a suggested lemma can fail to
match a goal that still carries an antecedent like (a in X) => ….  When that
happens this peels the goal (a di) and retries automatically -- exactly the
step you'd take by hand, and the antecedent it assumes is usually a hypothesis
the lemma then needs.

Before sending, it asks the prover which schema variables the conclusion-match
leaves open (those living only in NAME's hypotheses).  For each, you type a
value as a VNB term in surface syntax (e.g. RAN(f), nn) -- no quoting, no
((v val)) form; the command parses it and supplies it.  If the conclusion
determines everything, it sends straight through with no extra prompts.

The further handler form (bc* 'NAME (...) h1 ...) (one tactic-thunk per
hypothesis) is NOT an interactive move -- it needs the hypothesis count known
up front and is a batch convenience for proof FILES; interactively you just let
this spawn the subgoals and close each with Assume etc.
NB: bc* cannot match a conclusion whose head is a structure accessor like
((MUL s) x y)."
  (interactive (list (vnb-pf--read-lemma-name)))
  (vnb-launch--ensure-prover)
  (let* ((nm   (vnb-launch--dequote name))
         (resp (vnb-pf--bc-undetermined nm)))
    ;; The suggester ranks lemmas by the goal's EVENTUAL conclusion -- it peels
    ;; the leading FORALL/IMPLIES.  So a suggested lemma can fail to match the
    ;; LITERAL goal that still carries an antecedent (a ∈ X) ⇒ ….  If so, peel
    ;; the goal (di) -- the move you'd make by hand, and the antecedent it
    ;; assumes is usually a hypothesis the lemma needs -- and retry once.
    (when (and (eq (and (consp resp) (car resp)) 'no-match)
               (> (vnb-pf--reduce-goal) 0))
      (setq resp (vnb-pf--bc-undetermined nm)))
    (pcase (and (consp resp) (car resp))
      ('unknown  (user-error "No such theorem/axiom: %s" nm))
      ('no-proof (user-error "No current proof"))
      ('no-match (user-error "Conclusion of %s does not match the goal" nm))
      ('ok
       (let ((vars (cdr resp)) (binds '()))
         (dolist (v vars)
           (push (cons v (vnb-launch--dequote
                          (vnb-launch--read-required
                           (format "%s = (VNB term, empty cancels): " v))))
                 binds))
         (vnb-launch--send-tactic
          (if (null binds)
              (format "(bc* '%s ())" nm)
            (format "(bc*-apply-term-bindings '%s (list %s))"
                    nm
                    (mapconcat (lambda (b)
                                 (format "(cons '%s %S)" (car b) (cdr b)))
                               (nreverse binds) " "))))))
      (_ (user-error "Backchain query failed: no response from prover")))))

(defun vnb-pf-bplus ()
  "B+ -- the saturating closer.  Wraps (bplus).
Sweeps EVERY open goal under the proof and closes everything it can DECISIVELY
close: goals already discharged by their own context (ass-all), plus a cite of
the top fingerprint-ranked backchain lemma WHENEVER all that lemma's hypotheses
are already assumptions.  Each goal is peeled (di) to its conclusion first.
Repeats until a pass closes nothing, then reports whether the proof closed or
how many goals it stalled on (and lands focus on the first such goal).

It makes only moves it can SEE will land -- the dg has no undo, so rather than
guess-and-backtrack it stops wherever a real choice is needed and leaves that
goal to you.  Think of it as `A' (ass-all) plus automatic `B' on every goal
whose lemma hypotheses are already in hand: it clears the mechanical/plumbing
goals in one keystroke."
  (interactive)
  (vnb-launch--send-tactic "(bplus)"))

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
;;; Start Proof Workspace: edit the goal formula in a real buffer, then begin
;;; the proof.  Mirrors Build Structure (a *VNB Structure* editor): an editing
;;; buffer with C-c C-c to commit and C-c C-k to cancel.  Replaces the old
;;; one-line minibuffer prompt, which made long formulas painful to type.

(defvar vnb-startproof-buffer-name "*VNB Start Proof*"
  "Name of the Start Proof editing buffer.")

(defvar vnb-startproof-template "\
;; ────────────────────────────────────────────────────────────
;; START PROOF     C-c C-c = Begin proof     C-c C-k = Cancel
;; ────────────────────────────────────────────────────────────
;;
;; Write the goal below in VNB string (infix) syntax, e.g.
;;
;;   forall([x in nn], x in zz)
;;
;;   forall([R], is-commutative-ring(R) implies
;;     forall([a in a(R), b in a(R)], (mul(R))(a, b) = (mul(R))(b, a)))
;;
;; Multiple lines are fine -- they are joined into one formula; comment
;; lines (starting with ';') are ignored.  C-c C-c parses the goal, starts
;; the proof, and switches to the Focus workspace.  (A quick one-liner can
;; still go straight through  (sp (wff \"...\"))  in the Scratch Workspace.)
;; ────────────────────────────────────────────────────────────

"
  "Initial content inserted into a fresh Start Proof workspace.")

(defvar vnb-startproof-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m (kbd "C-c C-c") 'vnb-startproof-submit)
    (define-key m (kbd "C-c C-k") 'vnb-startproof-cancel)
    m)
  "Keymap for the Start Proof editing buffer.")

(define-derived-mode vnb-startproof-mode prog-mode "VNB-StartProof"
  "Major mode for the Start Proof workspace.
\\<vnb-startproof-mode-map>
Edit the goal formula, then \\[vnb-startproof-submit] to begin the proof,
or \\[vnb-startproof-cancel] to cancel.  Comment lines (starting with `;')
are ignored when the goal is read."
  (setq truncate-lines nil)
  (setq-local comment-start ";")
  (when (fboundp 'show-paren-local-mode)   (show-paren-local-mode 1))
  (when (fboundp 'electric-pair-local-mode) (electric-pair-local-mode 1)))

(defun vnb-launch--startproof-formula ()
  "Return the goal from the current buffer: every non-comment, non-blank line
joined with spaces, trimmed.  Comment lines start with `;'."
  (let ((lines '()))
    (save-excursion
      (goto-char (point-min))
      (while (not (eobp))
        (let ((line (buffer-substring-no-properties
                     (line-beginning-position) (line-end-position))))
          (unless (string-match-p "\\`[ \t]*\\(;.*\\)?\\'" line)
            (push line lines)))
        (forward-line 1)))
    (string-trim (mapconcat #'identity (nreverse lines) " "))))

(defun vnb-startproof-submit ()
  "Parse the goal in this buffer and begin the proof in the Focus workspace."
  (interactive)
  (let ((formula (vnb-launch--startproof-formula)))
    (when (string= formula "")
      (user-error "No formula given -- write the goal below the header"))
    (vnb-launch--ensure-prover)
    (vnb-launch--show-proof-workspace)
    (vnb-launch--send
     (format "(sp (make-wff-from-string %S))" formula))))

(defun vnb-startproof-cancel ()
  "Discard the Start Proof buffer and return to the Home Workspace."
  (interactive)
  (when (yes-or-no-p "Discard this formula? ")
    (kill-buffer)
    (vnb-launch-workspace)))

(defun vnb-ws-start-proof ()
  "Open the Start Proof workspace: compose the goal formula (VNB infix syntax),
then \\<vnb-startproof-mode-map>\\[vnb-startproof-submit] to carry out its proof in the Focus workspace.  Gives long
formulas room the minibuffer never had."
  (interactive)
  (let ((buf (get-buffer-create vnb-startproof-buffer-name)))
    (with-current-buffer buf
      (unless (eq major-mode 'vnb-startproof-mode)
        (vnb-startproof-mode))
      (when (= (point-min) (point-max))
        (insert vnb-startproof-template)
        (vnb-launch--protect-banner)
        (vnb-launch--paint-banner)
        (vnb-launch--accent-rule-lines)
        (goto-char (point-max))))
    (delete-other-windows)
    (switch-to-buffer buf)))

;;; -----------------------------------------------------------------------
;;; Your First Proof: a gentle, guided on-ramp for a complete newcomer.
;;; Reuses vnb-startproof-mode (so C-c C-c submits the goal); the template
;;; pre-fills a tautological goal whose proof is the two-step assume/discharge
;;; loop -- verified to close via (di) then (ass).

(defvar vnb-firstproof-buffer-name "*VNB First Proof*"
  "Name of the guided first-proof buffer.")

(defvar vnb-firstproof-template "\
;; ────────────────────────────────────────────────────────────
;;  YOUR FIRST PROOF      C-c C-c = Begin      C-c C-k = Cancel
;; ────────────────────────────────────────────────────────────
;;
;;  The goal on the last line says: every natural number is a natural
;;  number.  It is true purely by logic, with no real mathematical
;;  content -- a *tautology* -- which is exactly what makes it a safe,
;;  perfect first proof.
;;
;;  Press  C-c C-c  to begin.  A \"Focus\" window opens, showing the goal.
;;  There, type each of these and press RET:
;;
;;      (di)      \"assume x is a natural number\"  -- the goal becomes  x in nn
;;      (ass)     \"but that's already what we assumed\"  -- proved!
;;
;;  That assume-then-discharge loop is the heart of every proof.  When you
;;  are ready for more, try  Start Proof  with a goal of your own.
;; ────────────────────────────────────────────────────────────

forall([x in nn], x in nn)
"
  "Initial content for the guided first-proof workspace.")

(defun vnb-ws-first-proof ()
  "Open the Your First Proof workspace: a guided, two-step first proof.
Pre-fills a tiny true goal; \\<vnb-startproof-mode-map>\\[vnb-startproof-submit] begins it, then (di) and (ass)
in the Focus window close it -- the whole assume/discharge loop in miniature."
  (interactive)
  (let ((buf (get-buffer-create vnb-firstproof-buffer-name)))
    (with-current-buffer buf
      (unless (eq major-mode 'vnb-startproof-mode)
        (vnb-startproof-mode))
      (when (= (point-min) (point-max))
        (insert vnb-firstproof-template)
        (vnb-launch--protect-banner)
        (vnb-launch--paint-banner)
        (vnb-launch--accent-rule-lines)
        (goto-char (point-max))))
    (delete-other-windows)
    (switch-to-buffer buf)))

;;; -----------------------------------------------------------------------
;;; Build Structure: define a new structure and save it to structure-library/

(defvar vnb-structure-buffer-name "*VNB Structure*"
  "Name of the Build Structure scratch buffer.")

(defvar vnb-structure-template "\
;; ────────────────────────────────────────────────────────────
;; BUILD STRUCTURE     C-c C-s = Save & Load     C-c C-k = Cancel
;; ────────────────────────────────────────────────────────────
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
;; ────────────────────────────────────────────────────────────

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
  "Initial content inserted into a fresh Build Structure workspace.")

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
  (setq truncate-lines nil)
  (vnb-launch--apply-faces)
  (vnb-launch--readable-comments))

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
  "Open the Build Structure workspace with a declare-structure template."
  (interactive)
  (let ((buf (get-buffer-create vnb-structure-buffer-name)))
    (with-current-buffer buf
      (unless (eq major-mode 'vnb-structure-mode)
        (vnb-structure-mode))
      (when (= (point-min) (point-max))
        (insert vnb-structure-template)
        (vnb-launch--protect-banner)
        (vnb-launch--paint-banner)
        (vnb-launch--accent-rule-lines)
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
  (setq truncate-lines nil)
  (vnb-launch--apply-faces)
  (vnb-launch--readable-comments))

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

(defun vnb-launch--enter ()
  "Top-level startup, branching on whether there is a window system.
Terminal (-nw): no browser, so the in-Emacs Home Workspace is the front door.
Graphical, `vnb-lobby-first' (default): the browser lobby is the front door --
set up the frame, open the lobby, show a minimal splash, and iconify Emacs; a
Workbench link raises Emacs into the work surface.  The in-Emacs landing menu
is suppressed (still on M-x vnb-launch-workspace).
Graphical, `vnb-lobby-first' nil: keep the old in-Emacs landing page."
  (cond
   ((not (display-graphic-p))
    (vnb-launch-workspace))
   (vnb-lobby-first
    (vnb-launch--frame-setup)
    (vnb-launch--show-lobby-splash)
    (ignore-errors (vnb-home-html))     ; starts listener + opens home.html
    ;; let the browser map first, then drop Emacs to the taskbar
    (run-at-time 0.6 nil
                 (lambda () (ignore-errors (iconify-frame (selected-frame))))))
   (t
    (vnb-launch-workspace))))

;; -----------------------------------------------------------------------
;; Personal configuration.  The `VNB' launcher runs `emacs -Q', so your
;; ~/.emacs and ~/.emacs.d/init.el are NOT read (a deliberate, predictable
;; environment).  Instead, if ~/.vnb.el exists it is loaded here -- put your
;; VNB option overrides there.  It loads AFTER every defcustom, so a plain
;; setq wins (no `with-eval-after-load' needed) and takes effect before the
;; workspace opens any browser below.  Example ~/.vnb.el:
;;     (setq vnb-graph-browser "epiphany")   ; "epiphany-browser" on Debian/Ubuntu
;; Override the path with the VNB_CONFIG environment variable if you like.
(let ((user-cfg (or (getenv "VNB_CONFIG") (expand-file-name "~/.vnb.el"))))
  (when (file-readable-p user-cfg)
    (load (expand-file-name user-cfg) nil t)))

(unless noninteractive
  (add-hook 'window-setup-hook
            (lambda ()
              (run-at-time 0.3 nil 'vnb-launch--enter))))

(provide 'vnb-launch)
;;; vnb-launch.el ends here
