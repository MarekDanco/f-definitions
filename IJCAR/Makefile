# makeenv optional file for additional setting
# LATEXARGS additional flags to latex to be set in makeenv
# LATEXMK latex compilation defaulting to latexmk, can be changed in makeenv
# POST_CMD additional action after latexmk
# Example: insert LATEXARGS=-file-line-error into makeenv
# Example: insert POST_CMD=&& /bin/cp -fv $(TRGT).pdf ~/Documents/

-include makeenv
TRGT=paper
DIST=janota

LATEXMK?=latexmk

.PHONY: arxiv all b clean

all:
	@$(LATEXMK) -pdf $(LATEXARGS) $(TRGT) $(POST_CMD)

b:
	bibtex $(TRGT)

clean:
	@$(LATEXMK) -C -pdf $(LATEXARGS) $(TRGT)

abstract.txt: paper.tex
	./extract_abstract.sh paper.tex >>abstract.txt

dist: all abstract.txt
	echo 'to be done'
	exit 1
	mkdir $(DIST)
	cp -v *.pdf $(TRGT).bbl *.cls *.bib *.tex $(DIST)/
	cd $(DIST) ; zip -r $(DIST).zip *

arxiv: all
	mkdir -p arxiv
	cp -v experiments/data/scaling_plot.png arxiv/
	latexpand --empty-comments --expand-bbl $(TRGT).bbl $(TRGT).tex >arxiv/arxiv.tex
	sed -i -e 's/experiments\/data\/scaling_plot\.png/scaling_plot.png/' arxiv/arxiv.tex
	cd arxiv && zip arxiv.zip *.*
