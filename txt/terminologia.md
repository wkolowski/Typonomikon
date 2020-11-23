# O słowach słów kilka

Jest problem ze słowami, gdyż jest ich dużo. W tej notatce na szybko spróbuję coś na to zaradzić. O jakie słowa chodzi? Ano: "element", "term", "wartość", "dane", "program", "algorytm" i może coś jeszcze - zobaczymy co mi do głowy przyjdzie w trakcie pisania.

## Termy i elementy

Term to pojęcie zupełnie podstawowe, szkoda definiować. Term jest w postaci normalnej jeżeli nie można go już bardziej obliczyć. Term jest zamknięty, kiedy jego kontekst jest pusty. Elementy typu to jego zamknięte termy w postaci normalnej.

Uwaga: są dwa spojrzenia na termy, wewnętrzne i zewnętrzne.

Termy w sensie wewnętrznym zawsze mają jakiś typ w jakimś kontekście. Można je sobie wyobrażać jako osądy postaci `G |- t : A`. W takim ujęciu `|- 2 : nat` jest termem, zaś `f f` nie jest termem, bo nie da się tego otypować.

Z drugiej strony mamy termy w sensie zewnętrznym, które dla rozróżnienia możemy zwać pretermami. Są to gołe wyrażenia, poprawnie zbudowane według reguł gramatyki (np. `f f` jest pretermem), ale nie muszą być dobrze otypowane.

## Dane, kodane i procesy

Tu sprawa jest banalnie prosta. Dane to elementy typów induktywnych, zaś kodane to elementy typów koinduktywnych. Ponieważ jednak słowo "kodane" jest niemal magiczne, lepiej elementy typów koinduktywnych nazywać procesami. Wot, strumień to taki proces generujący elementy danego typu. Trzeba tylko trohu uważać, bo "proces" w tym sensie koliduje z "procesem" w sensie systemów operacyjnych.

Należy też zauważyć, że niektóre rzeczy to ani nie dane ani nie kodane, np. funkcje.

Dane można przekształcać w procesy i to nawet na dwa sposoby (indukcja i koindukcja), ale przekształcenie procesu w dane jest dużo trudniejsze (musi być robione ad hoc).

## Wartości i obliczenia

Słowo "obliczenia" ma dwa znaczenia:
- obliczanie termu do postaci normalnej
- coś, co ma efekty uboczne

Pierwsze znaczenie odnosi się do termów i elementów i nie o nie tutaj chodzi - chodzi o to drugie, a mianowicie: wartości nie mają efektów ubocznych, a obliczenia MOGĄ mieć efekty uboczne, ale nie muszą.

## Program, algorytm, funkcja

Funkcja to term typu `A -> B` (lub `forall x : A, B x`).

Program to kod, który reprezentuje funkcję.

Algorytm to wysokopoziomowa idea, która reprezentuje program.

Jeżeli mamy potężny język, jak Coq, program i algorytm stają się w zasadzie tym samym.

## Uogólnione elementy i kontynuacje

Wiemy już, że `x : A` to element typu `A`. Czym zaś są "uogólnione elementy"?

Uogólnione elementy to termy... w postaci normalnej, czyli `G |- t : A`. Wewnątrz systemu można reprezentować je jako funkcje `t : G -> A`.

Jako dualne jawi się tutaj pojęcie kontynuacji: dla typu `X` typem kontynuacji jest typ `X -> A` dla dowolnego `A`. Trzeba będzie pomyśleć o tej perspektywie nieco więcej...