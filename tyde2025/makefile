LAGDA_FILES := $(wildcard agda/*.lagda.tex)

TEX_FILES := $(addprefix latex/,$(addsuffix .tex,$(basename $(basename $(notdir $(LAGDA_FILES))))))

all: paper.pdf

paper.pdf: references.bib $(TEX_FILES)
	latexmk --lualatex paper.tex

latex/%.tex: agda/%.lagda.tex
	agda -i agda/ --latex $<

clean:
	rm -f *.aux *.bbl *.blg *.fdb_latexmk *.fls *.log *.out *.pdf *.ptb *.xcp
	rm -f agda/*.agdai
	rm -f latex/*.tex
