paper.pdf: paper.tex paper.bib sections/*.tex
	latexmk -pdf paper.tex -shell-escape

.PHONY: clean
clean:
	rm -rf *.aux *.log *.pdf *.bbl *.blg *.out *.fls *_latexmk _minted*
