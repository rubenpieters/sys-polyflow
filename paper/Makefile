# based on https://tex.stackexchange.com/questions/40738/how-to-properly-make-a-latex-project

DOCNAME = paper

.PHONY: $(DOCNAME).pdf all clean

all: $(DOCNAME).pdf

$(DOCNAME).pdf: $(DOCNAME).tex $(DOCNAME).bib sections/*.tex
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make $(DOCNAME).tex

watch: $(DOCNAME).tex
	see $(DOCNAME).pdf &
	latexmk -pvc -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make $(DOCNAME).tex

clean:
	latexmk -CA
