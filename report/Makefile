all:    BPlusTree-report.pdf
BPlusTree-report.pdf: BPlusTree-report.tex BPlusTree-report.bib sections/*.tex
	pdflatex BPlusTree-report
	bibtex BPlusTree-report
	pdflatex BPlusTree-report
	pdflatex BPlusTree-report
clean:
	rm -f BPlusTree-report.aux
	rm -f BPlusTree-report.bbl
	rm -f BPlusTree-report.blg
	rm -f BPlusTree-report.dvi
	rm -f BPlusTree-report.log
	rm -f BPlusTree-report.toc
	rm -f BPlusTree-report.pdf