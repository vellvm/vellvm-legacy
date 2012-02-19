;; These variables will be added to the Coq loadpath for every file
;; under this directory. Be sure to change it to reflect your current
;; settings

;; FIXME: maybe we should include just one directory recursively and
;; change the Requires correspondingly.

((coq-mode . ((coq-load-path . ("~/SVN/sol/vol/src3.0/Vellvm"
                                "~/SVN/sol/vol/src3.0/Vellvm/ott"
                                "~/SVN/sol/vol/src3.0/Vellvm/monads"
                                "~/SVN/sol/vol/src3.0/Vellvm/compcert"
                                "~/SVN/sol/vol/src3.0/Vellvm/GraphBasics"
                                "~/SVN/sol/vol/src3.0/Transforms"
                                "~/SVN/sol/vol/src3.0/TV"
                                "~/SVN/sol/vol/src3.0/SoftBound"
                                "~/SVN/sol/theory/metatheory_8.3"))
              (coq-prog-args . ("-emacs-U" ;; required for Coq to work
                                           ;; with proof general
                                "-impredicative-set")))))
