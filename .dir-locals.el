;; Specify coq-load path relative to project root
((coq-mode . ((eval . (flet ((pre (s) (concat 
                                       (locate-dominating-file buffer-file-name
                                                               ".dir-locals.el") 
                                       s)))
                        (setq coq-load-path 
                              `(,(pre "src/Vellvm")
                                ,(pre "src/Vellvm/ott")
                                ,(pre "src/Vellvm/Dominators")
                                ,(pre "lib/compcert-1.9")
                                ,(pre "lib/cpdtlib")
                                ,(pre "lib/GraphBasics")
                                ,(pre "lib/metalib-20090714")
                                ,(pre "lib/Coq-Equations-8.4/src")
                                (rec ,(pre "lib/Coq-Equations-8.4/theories") "Equations")))))
              (coq-prog-args . ("-emacs-U"
                                "-impredicative-set")))))
                                      
