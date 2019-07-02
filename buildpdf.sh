#!/bin/sh
# Tym skryptem można skompilować książkę do PDF.

# TODO: symbol pierwiastka kwadratowego źle się wyświetla

# coqdoc book/*v --latex -o tex/Książka.tex generuje pliki .tex i .sty z plików .v i umieszcza je w folderze tex/
# --inputenc utf8 ustawa odpowiednie kodowanie
# --no-lib-name --lib-subtitles robi ładniejszy format tytułu dla każdego rozdziału
# --parse-comments odpowiada za to, że komentarze postaci (* ===> cośtam *) normalnie się wyświetlają
# --no-index pozbywa się indeksu (czyli spisu identyfikatorów, definicji, twierdzeń etc.)
# --toc --toc-depth 2 robi spis treści o głębokości 2
coqdoc book/*v --latex -o tex/Książka.tex                                  \
       --inputenc utf8                                                     \
       --no-lib-name --lib-subtitles                                       \
       --parse-comments                                                    \
       --no-index                                                          \
       --toc --toc-depth 2                                                 \
       -p "\usepackage[greek, polish]{babel}"                              \
       -p "\DeclareUnicodeCharacter{221A}{\sqrt{}}" \
       -p "\DeclareUnicodeCharacter{2208}{\in}"         \
       -p "\DeclareUnicodeCharacter{2261}{\equiv}"


# Skompiluj książkę do PDF i umieść w tex/. Opcje:
# -interaction=nonstopmode ustawia przetwarzanie w batch mode
# -f wymusza pominięcie błędów
latexmk tex/Książka.tex -pdf -outdir=tex/ \
        -interaction=nonstopmode          \
        -f                                \
