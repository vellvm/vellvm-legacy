;; These variables will be added to the Coq loadpath for every file
;; under this directory. Be sure to change it to reflect your current
;; settings

;; FIXME: maybe we should include just one directory recursively and
;; change the Requires correspondingly.

((coq-mode . ((coq-load-path . ("~/SVN/sol/vol/src/Vellvm"
                                "~/SVN/sol/vol/src/Vellvm/ott"
                                "~/SVN/sol/vol/src/Vellvm/monads"
                                "~/SVN/sol/vol/src/Vellvm/compcert"
                                "~/SVN/sol/vol/src/Vellvm/GraphBasics"
                                "~/SVN/sol/vol/src/Transforms"
                                "~/SVN/sol/vol/src/TV"
                                "~/SVN/sol/vol/src/SoftBound"
                                "~/SVN/sol/theory/metatheory_8.3"))
              (coq-prog-args . ("-emacs-U" ;; required for Coq to work
                                           ;; with proof general
                                "-impredicative-set")))))
