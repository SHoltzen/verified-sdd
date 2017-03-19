(TeX-add-style-hook
 "report"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "twocolumn")))
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "graphicx"
    "amsmath"
    "amsthm")
   (LaTeX-add-labels
    "fig:sdd"
    "fig:unsatthm"
    "sec:vtree")
   (LaTeX-add-environments
    "definition")
   (LaTeX-add-bibliographies
    "bib"))
 :latex)

