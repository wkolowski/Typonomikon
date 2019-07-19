

(** Żeby zrozumieć ten komunikat o błędzie, musimy najpierw przypomnieć
    sobie składnię konstruktorów. Konstruktory typu induktywnego [T] będą
    mieć (w dość sporym uproszczeniu) postać [arg1 -> ... -> argN -> T] —
    są to funkcje biorące pewną (być może zerową) ilość argumentów, a ich
    przeciwdziedziną jest definiowany typ [T].

    Jeżeli definiowany typ [T] nie występuje nigdzie w typach argumentów
    [arg1 ... argN], sytuacja jest klarowna i wszystko jest w porządku.
    W przeciwnym wypadku, w zależności od postaci typów argumentów, mogą
    pojawić się problemy.

    Jeżeli typ któregoś z argumentów jest równy [T], nie ma problemu —
    jest to po prostu argument rekurencyjny. Mówimy, że [T] występuje w
    [T] ściśle pozytywnie. Jeżeli argument jest postaci [A -> T] dla
    dowolnego typu [A], również nie ma problemu — dzięki argumentom o takich
    typach możemy reprezentować np. drzewa o nieskończonym współczynniku
    rozgałęzienia. Mówimy, że w [A -> T] typ [T] występuje ściśle pozytywnie.
    To samo, gdy argument jest postaci [A * T] lub [A + T] etc.

    Problem pojawia się dopiero, gdy typ argumentu jest postaci [T -> A]
    lub podobnej (np. [A -> T -> B], [T -> (T -> A) -> B] etc.). W takich
    przypadkach mówimy, że typ [T] występuje na pozycji negatywnej (albo
    "nie-ściśle-pozytywnej"). *)