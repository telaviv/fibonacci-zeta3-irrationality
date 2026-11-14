#!/bin/sh
# Build paper/main.pdf into paper/build/ (pdflatex, embedded bibliography). Run from paper/.
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/pass1.log
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/pass2.log
grep -E "^!|undefined|multiply defined" build/main.log || echo "no errors, no undefined references"
grep -c "Overfull" build/main.log || true
