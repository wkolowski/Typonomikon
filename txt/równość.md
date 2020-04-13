# Ściąga - różne poziomy równości

| równość      | ten sam/ta sama | przykład pozytywny | przykład negatywny | świat      | jak sprawdzić | obchodzi nas ta równość, kiedy |
| ------------ | ----------------| ------------------ | ------------------ | ---------- | ------------- | --------------------- |
| napisowa     | ciąg znaków     | `1+1` <br> `1+1`   | `1+1` <br> `1 + 1` | zewnętrzny | oczami        | chcemy ładnie sformatować kod  |
| składniowa   | term            | `1+1` <br> `1 + 1` | `1+1` <br> `S 1`   | zewnętrzny | oczami        | dostajemy błąd składni         |
| definicyjna  | postać normalna | `1 + 1` <br> `S 1` | `1+n` <br> `n+1`   | zewnętrzny | `reflexivity` | chcemy tak sformułować twierdzenie, żeby dowód był prostszy |
| zdaniowa     | element         | `S n` <br> `n + 1` | `2` <br> `3`       | wewnętrzny | dowód `=`/`<>`| często
| równoważność | rzecz           | `[1]` <br> `[2]` <br> ta sama długość   | `[]` <br> `[1]` <br> inna długość | wewnętrzny | dowód | kiedy `=` nie wyraża dobrze naszych potrzeb

Objaśnienia:
- "świat zewnętrzny" znaczy, że nie możemy tworzyć zdań (czyli elementów `Prop`), które dokonują rozróżnień na tym poziomie
- "świat wewnętrzny" znaczy, że możemy 