#!/bin/sh
# Tym skryptem można skompilować "książkę". Co to robi:
# rm html/*html czyści starą wersję wygenerowanych plików html
# coqc book/*v kompiluje pliki .v (potrzebne żeby coqdoc mógł dodać linki do definicji i cośtam jeszcze (chyba?))
# Update 2017-02-17: opcja --utf8 została wywalona, dzięki czemu "->" wyświetla się teraz jako "->", a nie jako "→", jak poprzednio. To samo dotyczy innych znaków.
# --body-only --with-header HEAD_PREPEND ogarnia nagłówek generowanych plików .html
# --no-lib-name robi ładniejszy tytuł
# --lib-subtitles chyba nie działa
# --parse-comments odpowiada za to, że komentarze postaci (* ===> cośtam *) normalnie się wyświetlają
# --no-index pozbywa się indeksu
# --toc robi spis treści
# --toc-depth 2 spłyca spis treści do cywilizowanej głębokości
# -d html book/R*v wrzuca pliki .html wygenerowane z poszczególnych rozdziałów do html
# cp css/*css html/ przerzuca style do html/ (coqdoc generuje swoje które wszystko psują). Te z css są lepsze i z nimi wszystko jest ładnie.
# cp js/* html/ przerzuca js do html/ (są potrzebne żeby wszystko ładnie się wyświetlało)
# mv (...) zmienia toc.html na index.html, żeby na github.io wszystko się od razu ładnie wyświetlało
# rm (...) kasuje śmieci pozostałe po kompilacji plików .v

coqc book/*v;
coqdoc --body-only --with-header HEAD_PREPEND --no-lib-name --lib-subtitles --parse-comments --no-index --toc --toc-depth 2 -d html book/*v;
cp css/*css html/;
cp js/* html/;
mv html/toc.html html/index.html;
#rm book/*glob book/*vo
