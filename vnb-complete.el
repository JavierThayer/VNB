;;; vnb-complete.el -- completing-read integration for VNB commands
;;;
;;; Usage: add to your Emacs init or to vnb.el:
;;;
;;;   (load "/path/to/vnb-complete.el")
;;;
;;; Then M-x vnb-insert-command (or bind it) to insert a command with
;;; minibuffer completion.

(defvar vnb-command-list nil
  "Alist of VNB commands loaded from vnb-commands.lisp.
Each entry is (NAME ARGLIST DESCRIPTION).")

(defvar vnb-commands-file
  (expand-file-name "vnb-commands.lisp"
                    (file-name-directory
                     (or load-file-name buffer-file-name default-directory)))
  "Path to vnb-commands.lisp relative to this file.")

(defun vnb-load-commands ()
  "Read vnb-commands.lisp into `vnb-command-list'."
  (with-temp-buffer
    (insert-file-contents vnb-commands-file)
    (setq vnb-command-list (read (current-buffer)))))

(vnb-load-commands)

;;; Build completing-read candidates as an alist: (display-string . name-symbol)
;;; completing-read accepts alists; the car is displayed, the cdr is the value.
(defun vnb--candidates ()
  (mapcar (lambda (entry)
            (let* ((name (car entry))
                   (args (cadr entry))
                   (desc (caddr entry))
                   ;; Truncate description at first period for display
                   (short (if (string-match "\\." desc)
                              (substring desc 0 (match-end 0))
                            desc))
                   (display (format "%-14s %-20s  %s"
                                    (symbol-name name)
                                    (if args (format "%s" args) "()")
                                    short)))
              (cons display name)))
          vnb-command-list))

(defun vnb-insert-command ()
  "Completing-read over VNB commands and insert the chosen one."
  (interactive)
  (let* ((cands (vnb--candidates))
         (choice (completing-read "VNB command: " cands nil t))
         (name  (cdr (assoc choice cands)))
         (entry (assoc name vnb-command-list))
         (args  (cadr entry)))
    (insert "(" (symbol-name name))
    (dolist (arg args)
      (insert " "))
    (insert ")")
    ;; Leave point before the closing paren so the user fills in args
    (when args
      (backward-char (1+ (length args)))
      (backward-char (1- (length args))))))

(defun vnb-describe-command (name-sym)
  "Display the full description of VNB command NAME-SYM in the echo area."
  (interactive
   (list (intern (completing-read "Describe VNB command: "
                                  (mapcar (lambda (e) (symbol-name (car e)))
                                          vnb-command-list)
                                  nil t))))
  (let ((entry (assoc name-sym vnb-command-list)))
    (if entry
        (message "%s %s -- %s" (car entry) (cadr entry) (caddr entry))
      (message "Unknown command: %s" name-sym))))

(provide 'vnb-complete)
