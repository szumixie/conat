LAGDA_FILES := $(wildcard agda/*.lagda.tex agda/*/*.lagda.tex agda/*/*/*.lagda.tex)

TEX_FILES := $(subst agda,latex,$(subst .lagda.tex,.tex,$(LAGDA_FILES)))

all: paper.pdf

paper.pdf: paper.tex references.bib $(TEX_FILES)
	latexmk --lualatex paper.tex

latex/%.tex: agda/%.lagda.tex
	agda -i agda/ --latex $<

clean:
	rm -f *.aux *.bbl *.bcf *.blg *.fdb_latexmk *.fls *.log *.out *.pdf *.ptb *.run.xml *.xcp comment.cut
	rm -f agda/*.agdai agda/*/*.agdai agda/*/*/*.agdai
	rm -f latex/*.tex latex/*/*.tex latex/*/*/*.tex
