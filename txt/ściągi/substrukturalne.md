| Nazwa                 | Zamiana | Kontrakcja | Osłabianie | Hipotez można użyć      | Kontekst to     | Trzeba zużyć wszystkie hipotezy? |
| --------------------- | ------- | ---------- | ---------- | ----------------------- | --------------- | -------------------------------- |
| Logika astrukturalna* | NIE     | NIE        | NIE        | dokładnie raz, po kolei | [kolejka][2]    | TAK                              |
| [Logika liniowa][1]   | TAK     | NIE        | NIE        | dokładnie raz           | [multizbiór][3] | TAK                              |
| Logika afiniczna      | TAK     | NIE        | TAK        | co najwyżej raz         | [multizbiór][3] | NIE                              |
| Logika relewantna     | TAK     | TAK        | NIE        | co najmniej raz         | [zbiór][4]      | TAK                              |
| Logika strukturalna*  | TAK     | TAK        | TAK        | Dowolną ilość razy      | [zbiór][4]      | NIE                              |

Nazwy oznaczone gwiazdką (*) zostały wymyślone przeze mnie na potrzeby podrozdziału i tej tabelki.

Objaśnienia reguł:
- reguła zamiany pozwala zamieniać hipotezy miejscami
- reguła kontrakcji pozwala kopiować hipotezy
- reguła osłabiania pozwala kasować hipotezy

[1]: https://en.wikipedia.org/wiki/Linear_logic
[2]: https://en.wikipedia.org/wiki/Queue_(abstract_data_type)
[3]: https://en.wikipedia.org/wiki/Multiset
[4]: https://en.wikipedia.org/wiki/Set_(abstract_data_type)