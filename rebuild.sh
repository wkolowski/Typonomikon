#!/bin/sh
# Tym skryptem można zaorać książkę do gołej ziemii i zbudować od nowa.

# Usuń wszystkie pliki .v.d .aux .glob i cholera wie co jeszcze.
make clean

# Opróżnij foldery htmls/ i tex/
rm -rf htmls/* tex/*

# Zrób nowego makefile'a.
coq_makefile -R "." CoqBookPL -o makefile $(find . -name "*v")

# Zbuduj wersje HTML i PDF książki.
./build.sh
