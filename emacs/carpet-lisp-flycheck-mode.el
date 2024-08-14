(flycheck-define-checker carpet-lisp
  "Carpet Lisp type checker"
  :command ("carpet-lisp-check-types"
            "--machine-readable"
            source-original)
  :error-patterns
  ((error line-start (file-name) ":" line ":3 " (message) line-end)
   (warning line-start (file-name) ":" line ":0 " (message) line-end))
  :modes (lisp-mode))
