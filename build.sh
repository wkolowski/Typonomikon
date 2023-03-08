#!/bin/sh

# Zrób nowego makefile'a na wypadek, gdyby pojawiły się jakieś nowe pliki .v
coq_makefile -R "." Typonomikon -arg "-async-proofs-cache force" -o makefile $(find . -name "*v")

# Skompiluj pliki .v - dzięki temu mamy pewność, że cały kod z książki działa poprawnie.
make # -j `nproc`

# Wywal makefile'a - po co ma zaśmiecać folder?
rm makefile makefile.conf

# Zbuduj wersję HTML.

# coqdoc book/*v --html -d docs generuje pliki .html z plików .v i umieszcza je w folderze docs/
# --with-footer assets/footer.html dodaje stopkę, która jest pusta
# --with-header assets/header.html dodaje nagłówek, w którym są szpiegujące analitiksy z Google'a
# --no-lib-name --lib-subtitles robi ładniejszy format tytułu dla każdego rozdziału
# --parse-comments odpowiada za to, że komentarze postaci (* ===> cośtam *) normalnie się wyświetlają
# --no-index pozbywa się indeksu (czyli spisu identyfikatorów, definicji, twierdzeń etc.)
# --toc --toc-depth 2 robi spis treści o głębokości 2
# Update 2017-02-17: opcja --utf8 została wywalona, dzięki czemu "->" wyświetla się teraz jako "->", a nie jako "→", jak poprzednio.
# TODO: zmniejszyć --toc-depth do 1 (w swoim czasie rzecz jasna)
coqdoc book/*v                                            \
       -d docs                                            \
       --html                                             \
       --with-header assets/header.html                   \
       --with-footer assets/footer.html                   \
       --no-lib-name                                      \
       --lib-subtitles                                    \
       --parse-comments                                   \
       --no-index                                         \
       --toc --toc-depth 3

# Dodaj style CSS, pliki .js potrzebne nie pamiętam do czego, oraz okładkę.
cp assets/*css assets/*js assets/*jpg assets/index.html docs/

# Zbuduj wersję PDF.

# TODO: lambda, eta, i gamma się nie wyświetlają.
# TODO: symbol pierwiastka kwadratowego źle się wyświetla.

# Skompiluj okładkę.
latexmk assets/cover.tex -pdf -outdir=tex/                \
        -interaction=nonstopmode                          \
        -f                                                \
        -quiet

# coqdoc book/*v --latex -o tex/Książka.tex generuje pliki .tex i .sty z plików .v i umieszcza je w folderze tex/
# --inputenc utf8 ustawa odpowiednie kodowanie
# --no-lib-name --lib-subtitles robi ładniejszy format tytułu dla każdego rozdziału
# --parse-comments odpowiada za to, że komentarze postaci (* ===> cośtam *) normalnie się wyświetlają
# --no-index pozbywa się indeksu (czyli spisu identyfikatorów, definicji, twierdzeń etc.)
# --toc --toc-depth 2 robi spis treści o głębokości 2
# -p dodaje do latexowej preambuły linijki ustawiające język polski i naprawiające błędy związane z Unicode
# Co więcej, -p dodaje pakiet pdfpages, który jest używany do zrobienia strony tytułowej. Całość jest trochę
# zhakowana, bo -p dodaje też na początku dodatkowe \begin{document}, przez co są 2. Ale działa!
coqdoc book/*v --latex -o tex/Książka.tex                 \
       --inputenc utf8                                    \
       --no-lib-name --lib-subtitles                      \
       --parse-comments                                   \
       --no-index                                         \
       --toc --toc-depth 2                                \
       -p "\usepackage[greek, polish]{babel}"             \
       -p "\usepackage{textgreek}"                        \
       -p "\usepackage{pdfpages}"                         \
       -p "\DeclareUnicodeCharacter{221A}{\sqrt{}}"       \
       -p "\DeclareUnicodeCharacter{2208}{\in}"           \
       -p "\DeclareUnicodeCharacter{2261}{\equiv}"        \
       -p "\DeclareUnicodeCharacter{03BF}{\omicron}"      \
       -p "\begin{document}"                              \
       -p "\includepdf{tex/cover.pdf}"

# Skompiluj źródła .tex książki do PDF i umieść w tex/. Opcje:
# -interaction=nonstopmode ustawia przetwarzanie w batch mode
# -f wymusza pominięcie błędów
# -quiet wycisza spam
latexmk tex/Książka.tex -pdf -outdir=tex/                 \
        -interaction=nonstopmode                          \
        -f                                                \
        -quiet

dot txt/plany/plan.dot        -Tjpg -o txt/plany/plan.jpg
dot txt/plany/logika.dot      -Tjpg -o txt/plany/logika.jpg
dot txt/plany/rekursja.dot    -Tjpg -o txt/plany/rekursja.jpg
dot txt/plany/indukcja.dot    -Tjpg -o txt/plany/indukcja.jpg

dot txt/sugestie/rekordy.dot  -Tjpg -o txt/sugestie/rekordy.jpg
dot txt/sugestie/rekordy2.dot -Tjpg -o txt/sugestie/rekordy2.jpg

dot txt/ściągi/modalności.dot -Tjpg -o txt/ściągi/modalności.jpg
