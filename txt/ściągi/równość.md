# Ściąga - różne poziomy równości

| równość      | ten sam <br> ta sama | przykład pozytywny (równe) | przykład negatywny (nierówne) | świat      | jak sprawdzić | obchodzi nas ta równość |
| ------------ | -------------------- | -------------------------- | ----------------------------- | ---------- | ------------- | ----------------------- |
| napisowa     | ciąg znaków          | `1+1` <br> `1+1`           | `1+1` <br> `1 + 1`            | składnia   | oczami        | kiedy chcemy ładnie sformatować kod |
| składniowa   | term                 | `1+1` <br> `1 + 1`         | `1+1` <br> `S 1`              | składnia   | mózgiem       | kiedy dostaliśmy błąd składni       |
| α-konwersja  | term                 | `fun a : X => a` <br> `fun b : X => b` | `fun x y => x` <br> `fun x y => y` | składnia  | mózgiem | pomerdały nam się nazwy |
| definicyjna  | postać normalna      | `1 + 1` <br> `S 1`         | `1+n` <br> `n+1`              | składnia   | `reflexivity` | kiedy chcemy tak sformułować twierdzenie, żeby dowód był prostszy |
| zdaniowa     | element              | `S n` <br> `n + 1`         | `2` <br> `3`                  | semantyka  | dowód `=`/`<>`| jeszcze jak |
| równoważność | rzecz                | `[1]` <br> `[2]` <br> ta sama długość   | `[]` <br> `[1]` <br> inna długość | semantyka | dowód | kiedy `=` nie wyraża dobrze naszych potrzeb |

Objaśnienia:
- wpis "składnia" w kolumnie "świat" znaczy, że nie możemy tworzyć zdań (czyli elementów `Prop`), które dokonują rozróżnień na tym poziomie. Byty z tego świata to byty czysto językowe. Mają one różne przyjemne właściwości, np. wszystkie składniowe rodzaje równości są rozstrzygalne na metapoziomie.
- wpis "semantyka" w kolumnie "swiat" znaczy, że możemy tworzyć zdania (elementy `Prop`), które dokonują rozróżnień na tym poziomie. Byty z tego świata nie mają charakteru językowego, lecz są rzeczywistymi (w pewnym sensie) obiektami. Równości semantyczne nie są rozstrzygalne na metapoziomie.