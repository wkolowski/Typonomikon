#!/bin/sh
# Tym skryptem można zaorać książkę do gołej ziemii i zbudować od nowa. Część skryptu jest opisana w komentarzach do build.sh.
# make clean kasuje wszystkie pliki .v.d .aux .glob i cholera wie co jeszcze
# rm makefile kasuje starego makefile'a


make clean
rm makefile
rm -rf htmls/

./make_makefile.sh
make
mkdir htmls/
coqdoc --with-footer extra/footer.html --with-header extra/header.html --no-lib-name --lib-subtitles --parse-comments --no-index --toc --toc-depth 2 -d htmls book/*v
cp css/*css htmls/
cp js/* htmls/
mv htmls/toc.html htmls/index.html
