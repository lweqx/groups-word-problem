(require 'evil)
(evil-mode 1)

(defun proof-mode-config ()
    (local-set-key (kbd "<M-down>") 'proof-assert-next-command-interactive)
    (local-set-key (kbd "<M-up>") 'proof-undo-last-successful-command)
    (local-set-key (kbd "<M-right>") 'proof-goto-point)
    (local-set-key (kbd "<M-left>") 'proof-goto-end-of-locked)

    (evil-ex-define-cmd "Cc" 'coq-Check)
    (evil-ex-define-cmd "Cp" 'coq-Print)

    (electric-indent-mode 0)

    (set 'evil-shift-width 2)
)

(add-hook 'proof-mode-hook 'proof-mode-config)
