;; Specify coq-load path relative to project root
((coq-mode . ((eval . (flet ((pre (s) (concat 
                                       (locate-dominating-file buffer-file-name
                                                               ".dir-locals.el") 
                                       s)))
                        (setq coq-load-path 
                              `(,(pre "Vellvm")
                                ,(pre "Vellvm/ott")
                                ,(pre "Vellvm/Dominators")
                                ,(pre "../lib/compcert")
                                ,(pre "../lib/GraphBasics")
                                ,(pre "../lib/metatheory_8.4")
                                ,(pre "../lib/Coq-Equations-8.4-1/src")
                                (rec ,(pre "../extralibs/Coq-Equations-8.4-1/theories") "Equations")))))
              (coq-prog-args . ("-emacs-U"
                                "-impredicative-set")))))
                                      
