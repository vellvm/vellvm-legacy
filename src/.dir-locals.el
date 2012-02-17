;; These variables will be added to the Coq loadpath for every file
;; under this directory. Be sure to change it to reflect your current
;; settings

;; FIXME: maybe we should include just one directory recursively and
;; change the Requires correspondingly.

((coq-mode . ((coq-load-path . ("~/src/vol/src/Vellvm"
                                "~/src/vol/src/Vellvm/ott"
                                "~/src/vol/src/Vellvm/monads"
                                "~/src/vol/src/Vellvm/compcert"
                                "~/src/vol/src/Vellvm/GraphBasics"
                                "~/src/vol/src/Transforms"
                                "~/src/vol/src/TV"
                                "~/src/vol/src/SoftBound"
                                "~/src/vol/theory/metatheory_8.3"))
              (coq-prog-args . ("-emacs-U" ;; required for Coq to work
                                           ;; with proof general
                                "-impredicative-set")))))
