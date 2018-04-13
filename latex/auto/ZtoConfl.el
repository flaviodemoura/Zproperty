(TeX-add-style-hook
 "ZtoConfl"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("llncs" "a4paper" "envcountsame")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("fontenc" "T1") ("babel" "british") ("biblatex" "backend=bibtex" "style=numeric-comp" "sorting=none" "firstinits=true")))
   (TeX-run-style-hooks
    "latex2e"
    "llncs"
    "llncs10"
    "inputenc"
    "fontenc"
    "babel"
    "lmodern"
    "coqdoc"
    "amsmath"
    "amssymb"
    "amsfonts"
    "color"
    "url"
    "hyperref"
    "graphicx"
    "biblatex")
   (TeX-add-symbols
    '("flavio" 1)))
 :latex)

