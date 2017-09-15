#!/bin/sh
# Tym skryptem można skompilować "książkę". Co to robi:
# make kompiluje pliki .v (potrzebne żeby coqdoc mógł dodać linki do definicji i cośtam jeszcze (chyba?))
# Update 2017-02-17: opcja --utf8 została wywalona, dzięki czemu "->" wyświetla się teraz jako "->", a nie jako "→", jak poprzednio. To samo dotyczy innych znaków.
# --with-footer extra/footer.html zabija stopkę
# --with-header extra/header.html robi nagłówek generowanych plików .html
# --no-lib-name robi ładniejszy tytuł
# --lib-subtitles chyba nie działa
# --parse-comments odpowiada za to, że komentarze postaci (* ===> cośtam *) normalnie się wyświetlają
# --no-index pozbywa się indeksu
# --toc robi spis treści
# --toc-depth 2 spłyca spis treści do cywilizowanej głębokości
# -d htmls book/*v wrzuca pliki .html wygenerowane z poszczególnych rozdziałów do htmls/
# cp css/*css htmls/ przerzuca style do htmls/ (coqdoc generuje swoje które wszystko psują). Te z css są lepsze i z nimi wszystko jest ładnie.
# cp js/* htmls/ przerzuca pliki .js do htmls/ (są potrzebne żeby wszystko ładnie się wyświetlało)
# mv (...) zmienia toc.html na index.html, żeby na github.io wszystko się od razu ładnie wyświetlało

make
coqdoc --with-footer extra/footer.html --with-header extra/header.html --no-lib-name --lib-subtitles --parse-comments --no-index --toc --toc-depth 2 -d htmls book/*v
cp css/*css htmls/
cp js/* htmls/
mv htmls/toc.html htmls/index.html
