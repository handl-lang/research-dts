PAPER = ../PAPER.md
DEFAULTS = pandoc.yaml

.PHONY: all pdf tex clean

all: pdf tex

pdf: paper.pdf
tex: main.tex

paper.pdf: $(PAPER) $(DEFAULTS)
	pandoc --defaults $(DEFAULTS) --pdf-engine=xelatex --output $@ $<

main.tex: $(PAPER) $(DEFAULTS)
	pandoc --defaults $(DEFAULTS) --output $@ $<

clean:
	rm -f *.aux *.log *.out *.toc *.synctex.gz *.fdb_latexmk *.fls main.tex paper.pdf
