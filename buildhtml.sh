#!/bin/sh
# Tym skryptem można skompilować książkę do HTML.

# coqdoc book/*v --html -d htmls generuje pliki .html z plików .v i umieszcza je w folderze htmls/
# --with-footer extra/footer.html dodaje stopkę, która jest pusta
# --with-header extra/header.html dodaje nagłówek, w którym są szpiegujące analitiksy od żydów z Google'a
# --no-lib-name --lib-subtitles robi ładniejszy format tytułu dla każdego rozdziału
# --parse-comments odpowiada za to, że komentarze postaci (* ===> cośtam *) normalnie się wyświetlają
# --no-index pozbywa się indeksu (czyli spisu identyfikatorów, definicji, twierdzeń etc.)
# --toc --toc-depth 2 robi spis treści o głębokości 2
# Update 2017-02-17: opcja --utf8 została wywalona, dzięki czemu "->" wyświetla się teraz jako "->", a nie jako "→", jak poprzednio.
coqdoc book/*v --html -d htmls                           \
       --with-footer extra/footer.html                   \
       --with-header extra/header.html                   \
       --no-lib-name --lib-subtitles                     \
       --parse-comments                                  \
       --no-index                                        \
       --toc --toc-depth 2

# Ustaw ładne style css (coqdoc generuje swoje które wszystko psują).
cp css/*css htmls/

# Wrzuć do htmls/ pliki .js, które są potrzebne, ale nie pamiętam do czego.
cp js/* htmls/

# Dodaj okładkę.
cp extra/index-bg.jpg htmls/
cp extra/index.html htmls/
