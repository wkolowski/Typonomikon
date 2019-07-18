(*

    Pierwszym, stosunkowo błahym problemem jest fakt, że typy łamiące
    kryterium ścisłej pozytywności nie mają modeli teoriozbiorowych —
    znaczy to po prostu, że nie można reprezentować ich w teorii zbiorów
    za pomocą żadnych zbiorów. Dla wielu matematyków stanowi to problem
    natury praktycznej (są przyzwyczajeni do teorii zbiorów) lub
    filozoficznej.

    Problem ten wynika z faktu, że konstruktory typów induktywnych są
    injekcjami, zaś typy argumentów, w których definiowany typ występuje
    na pozycji negatywnej, są "za duże". Np. w przypadku typu [wut bool]
    konstruktor [C] jest injekcją z [wut bool -> bool] w [wut bool].
    Gdybyśmy chcieli interpretować typy jako zbiory, to zbiór
    [wut bool -> bool] jest "za duży", by można było go wstrzyknąć do
    [wut bool], gdyż jest w bijekcji ze zbiorem potęgowym [wut bool], a
    w teorii zbiorów powszechnie wiadomo, że nie ma injekcji ze zbioru
    potęgowego jakiegoś zbioru do niego samego.

    Nie przejmuj się, jeżeli nie rozumiesz powyższego paragrafu — nie
    jest to główny powód obowiązywania kryterium ścisłej pozytywności,
    wszak jako buntownicy zajmujący się teorią typów nie powinniśmy
    zbytnio przejmować się teorią zbiorów.

 - Cantor, Russel, Girard *)