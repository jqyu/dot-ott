ott -i DOT.ott -o DOT.tex -o Definitions.v -coq_lngen true
coqc Definitions.v
lngen -o Infrastructure.v --coq-ott=Definitions DOT.ott
coqc Infrastructure.v
pdflatex DOT
