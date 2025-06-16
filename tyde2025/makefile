LAGDA_FILES := $(wildcard agda/*.lagda.tex)

TEX_FILES := $(addprefix latex/,$(addsuffix .tex,$(basename $(basename $(notdir $(LAGDA_FILES))))))

all: paper.pdf

paper.pdf: $(TEX_FILES)
	latexmk --lualatex paper.tex

latex/%.tex: agda/%.lagda.tex
	agda -i agda/ --latex $<
