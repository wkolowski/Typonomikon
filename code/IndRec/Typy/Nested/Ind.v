(** Generowanie reguł indukcji dla zagnieżdżonych typów induktywnych (w stylu
    [RoseTree], a nie w stylu [Bush]):
    https://www.ps.uni-saarland.de/~ullrich/bachelor/thesis.pdf

    W skrócie: wszystko opiera się na translacji parametrycznej, tzn. zamieniany
    [list] na [Forall], [BTree] na [Forall_BTree] etc. Prostsze typy (jak [nat]
    albo [bool]) zamieniają się w [True]. Rodziny indeksowane (np. [vec]) działają
    podobnie do [list], ale może być dodatkowy problem przy translacji ich indeksów.
*)