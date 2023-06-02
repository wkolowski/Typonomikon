(** * C1: Podstawy programowania funkcyjnego [TODO] *)

(** UWAGA: ten rozdział został naprędce posklejany z fragmentów innych,
    więc może nie mieć większego sensu. *)

(** * Enumeracje (TODO) *)

(* begin hide *)
(*
TODO 1: przykładowe typy: dni tygodnia, miesiące, pory roku, strony świata
TODO 2: opisać opcje za pomocą analogii do "która godzina", jak w
TODO 2: https://www.cs.cmu.edu/~15150/previous-semesters/2012-spring/resources/lectures/09.pdf
TODO 3: boole pozwalają patrzeć, opcje pozwalają widzieć
*)
(* end hide *)

(** * Enumeracje z argumentami (TODO) *)

(** * Rekordy (TODO) *)

(** W wielu językach programowania występują typy rekordów (ang. record
    types). Charakteryzują się one tym, że mają z góry określoną ilość
    pól o potencjalnie różnych typach. W językach imperatywnych rekordy
    wyewoluowały zaś w obiekty, które różnią się od rekordów tym, że mogą
    zawierać również funkcje, których dziedziną jest obiekt, w którym
    funkcja się znajduje.

    W Coqu mamy do dyspozycji rekordy, ale nie obiekty. Trzeba tu po raz
    kolejny pochwalić siłę systemu typów Coqa — o ile w większości języków
    rekordy są osobnym konstruktem językowym, o tyle w Coqu mogą być one z
    łatwością reprezentowane przez typy induktywne z jednym konstruktorem
    (wraz z odpowiednimi projekcjami, które dekonstruują rekord). *)

Module rational2.

Record rational : Set :=
{
  sign : bool;
  numerator : nat;
  denominator : nat;
  denominator_not_zero : denominator <> 0
}.

(** Z typem induktywnym o jednym konstruktorze już się zetknęliśmy,
    próbując zdefiniować liczby wymierne. Powyższa definicja używająca
    rekordu ma drobną przewagę nad poprzednią, w której słowo kluczowe
    [Inductive] pada explicité:
    - wygląda ładniej
    - ma projekcje *)

Check sign.
(* ===> sign : rational -> bool *)

Check denominator_not_zero.
(* ===> denominator_not_zero
    : forall r : rational, denominator r <> 0 *)

(** Dzięki projekcjom mamy dostęp do poszczególnych pól rekordu bez
    konieczności jego dekonstruowania — nie musimy używać konstruktu
    [match] ani taktyki [destruct], jeżeli nie chcemy. Często bywa to
    bardzo wygodne.

    Projekcję [sign] możemy interpretować jako funkcję, która bierze
    liczbę wymierną [r] i zwraca jej znak, zaś projekcja
    [denominator_not_zero] mówi nam, że mianownik żadnej liczb wymiernej
    nie jest zerem.

    Pozwa tymi wizualno-praktycznymi drobnostkami, obie definicje są
    równoważne (w szczególności, powyższa definicja, podobnie jak
    poprzednia, nie jest dobrą reprezentacją liczb wymiernych). *)

End rational2.

(** **** Ćwiczenie (kalendarz) *)

(** Zdefiniuj typ induktywny reprezentujący datę i napisz ręcznie
    wszystkie projekcje. Następnie zdefiniuj rekord reprezentujący
    datę i zachwyć się tym, ile czasu i głupiego pisania zaoszczędziłbyś,
    gdybyś od razu użył rekordu... *)

(* begin hide *)
(* TODO : zrób to ćwiczenie *)
(* end hide *)

(** * Moduły (TODO) *)

(** Nie lubię Coqowego systemu modułów, więc w tym rozdziale jeszcze
    długo nic nie zagości. *)

(* begin hide *)

(** Trochę materiałów o modułach, coby sobie to wszystko lepiej w głowie posortować.

    Moduły w Coqu:
    - https://coq.inria.fr/refman/language/core/modules.html
    - https://github.com/coq/coq/wiki/ModuleSystemTutorial
    - http://adam.chlipala.net/cpdt/html/Large.html
    - https://www.researchgate.net/publication/2840744_Implementing_Modules_in_the_Coq_System
    - https://stackoverflow.com/questions/48837996/import-module-vs-include-module-in-coq-module-system/49717951

    Moduły w OCamlu:
    - https://ocaml.org/learn/tutorials/modules.html
    - https://dev.realworldocaml.org/files-modules-and-programs.html
    - https://www.cs.cornell.edu/courses/cs3110/2019fa/textbook/modules/intro.html
    - https://www.ocaml.org/releases/4.11/htmlman/moduleexamples.html

    First-class modules:
    - https://dev.realworldocaml.org/first-class-modules.html
    - https://www.cs.cornell.edu/courses/cs3110/2020sp/manual-4.8/manual028.html
    - https://www.cl.cam.ac.uk/~jdy22/papers/first-class-modules.pdf
    - https://people.mpi-sws.org/~rossberg/1ml/1ml-extended.pdf

    Modular implicits:
    - https://tycon.github.io/modular-implicits.html
    - http://www.lpw25.net/papers/ml2014.pdf

    Tajpklasy/moduły w Haskellu:
    - https://www.youtube.com/watch?v=XtogTwzcGcM (DOBRY KONTENT!)
    - https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/first_class_modules.pdf

    OCamlowe moduły vs Haskellowe tajpklasy:
    - https://blog.shaynefletcher.org/2017/05/more-type-classes-in-ocaml.html
    - http://okmij.org/ftp/Computation/typeclass.html
    - https://accu.org/journals/overload/25/142/fletcher_2445/
    - https://people.mpi-sws.org/~dreyer/papers/mtc/main-long.pdf
    - https://www.reddit.com/r/ocaml/comments/364vqg/examples_of_ocaml_modules_which_cant_be_done_in/

*)

(* end hide *)

(** * Typy wbudowane (TODO) *)

(** Tutaj będą opisane typy, która można spotkać w normalnych językach
    programowania, takie jak [int] czy [float]. *)

(** * Styl, czyli formatowanie, wcięcia i komentarze (TODO) *)

(* begin hide *)
(*
TODO 1: Dodać rozdział o stylu, wcięciach, komentowaniu etc.
TODO 1: Patrz tu: https://www.cs.princeton.edu/courses/archive/fall19/cos326/style.php#1
TODO 2: Co do stylu, to tu jest Haskell style guide:
TODO 2: https://kowainik.github.io/posts/2019-02-06-style-guide)
TODO 3: Najtrudniejsza rzeczą w programowaniu jest wymyślanie nazw
*)
(* end hide *)

(** Tu będzie rozdział o stylu, czyli rzeczach takich jak czytelne
    formatowanie kodu czy pisanie zrozumiałych komentarzy. *)

(** ** Formatowanie kodu i wcięcia *)

(** ** Komentarze *)

(** ** Ars nazywandi, czyli trudna sztuka wymyślania nazw *)