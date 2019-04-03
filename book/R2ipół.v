(** * R2ipół : Rekursja *)

(** W poprzednim rozdziale dość dogłębnie zapoznaliśmy się z mechanizmem
    definiowania induktywnych typów i rodzin typów. Nauczyliśmy się też
    definiować funkcje operujące na ich elementach za pomocą dopasowania
    do wzorca oraz rekursji.

    Indukcja i rekursja są ze sobą bardzo ściśle powiązane. Obie operają
    się na autoreferencji, czyli odnoszeniu się do samego siebie:
    - liczba naturalna to zero lub następnik liczby naturalnej
    - długość listy złożonej z głowy i ogona to jeden plus długość ogona *)

(** Można użyć nawet mocniejszego stwierdzenia: indukcja i rekursja są
    dokładnie tym samym zjawiskiem. Skoro tak, dlaczego używamy na jego
    opisanie dwóch różnych słów? Cóż, jest to zaszłość historyczna, jak
    wiele innych, które napotkaliśmy. Rozróżniamy zdania i typy/specyfikacje,
    dowody i termy/programy, relacje i rodziny typów etc., choć te pierwsze
    są specjalnymi przypadkami tych drugich. Podobnie indukcja pojawiła się
    po raz pierwszy jako technika dowodzenia faktów o liczbach naturalnych,
    zaś rekursja jako technika pisania programów.

    Dla jasności, terminów tych będziemy używać w następujący sposób:
    - indukcja będzie oznaczać metodę definiowania typów oraz
      metodę dowodzenia
    - rekursja będzie oznaczać metodę definiowania funkcji *)




(** TODO *)



(** Ogólnie funkcja rekurencyjna to taka, która w swojej definicji odnosi
    się do samej siebie. Rodzaje rekurencji można podzielić w zależności
    od tego, w jaki sposób to robi:
    - Rekursja strukturalna to taka, w której funkcja wywołuje siebie
      na argumentach będących podtermami poprzednich argumentów
    - Rekursja dobrze ufundowana to taka, w której funkcja wywołuje siebie
      jedynie na argumentach "mniejszych", gdzie o tym, które argumenty są
      mniejsze, a które większe, decyduje pewna relacja dobrze ufundowana.
      Intuicyjnie relacja dobrze ufundowana to taka, że nie możemy
      w nieskończoność robić wywołań rekurencyjnych na coraz mniejszych
      argumentach, gdyż w końcu trafimy na najmniejszy.
    - Funkcje f i g są wzajemnie rekurencyjne, gdy funkcja f wywołuje g,
      a g wywołuje f. To, że f nie wywołuje samej siebie bezpośrednio nie
      oznacza wcale, że nie jest rekurencyjna. Schemat ten można uogólnić
      na dowolną ilość funkcji.
    - Rekursja ogólna to taka, w którym funkcja może odwoływać się do
      samej siebie w dowolny sposób. *)

(** ** Rekursja ogólna *)

(** W Coqu rekursja ogólna nie jest dozwolona. Powód jest prozaiczny:
    jest ona sprzeczna. W celu zobrazowania spróbujmy zdefiniować za
    pomocą taktyk następującą funkcję rekurencyjną: *)

Fixpoint loop (u : unit) : False.
Proof.
  apply loop. assumption.
Abort. (* Coq odrzuca komendę [Qed.] *)

(** Przyjrzyjmy się uważnie definicji funkcji [loop]. Mimo, że udało
    nam się ujrzeć znajomy napis "No more subgoals", próba użycia
    komendy [Qed] kończy się błędem. Gdyby tak się nie stało, możliwe
    byłoby skonstruowanie dowodu [False]: *)

(* Definition the_universe_explodes : False := loop tt. *)

(** Aby chronić nas przed tą katastrofą, Coq nakłada na rekurencję
    ograniczenie: argument główny wywołania rekurencyjnego musi być
    strukturalnym podtermem argumentu głównego obecnego wywołania.
    Innymi słowy, dozwolona jest jedynie rekursja strukturalna. *)

(** ** Rekursja strukturalna *)

(** Przyjrzyjmy się ponownie definicji dodawania: *)

Print plus.
(* plus = 
   fix plus (n m : nat) {struct n} : nat :=
     match n with
     | 0 => m
     | S p => S (plus p m)
     end
        : nat -> nat -> nat *)

(** Możemy zaobserwować parę rzeczy. Pierwsza, techniczna sprawa: po
    [=] widzimy nieznany nam konstrukt [fix]. Pozwala on tworzyć
    anonimowe funkcje rekruencyjne, tak jak [fun] pozwala tworzyć
    anonimowe funkcje nierekurencyjne. Funkcje zdefiniowane komendami 
    [Fixpoint] i [Definition] są w jęzku termów Coqa reprezentowane
    odpowiednio za pomocą [fix] i [fun].

    Po drugie: za listą argumentów, a przed zwracanym typem, występuje
    adnotacja [{struct n}]. Wskazuje ona, który z argumentów funkcji
    jest argumentem głównym. Definiując funkcje rekurencyjne zazwyczaj
    nie musimy go pisać, gdyż Coq jest w stanie sam wywnioskować, który
    argument jest główny.

    Czym jest argument główny? Aby to zrozumieć, zbadajmy najpierw
    relację bycia podtermem (dla uproszczenia, skupimy się na termach
    typów induktywnych). Relację tę opisują dwie proste zasady:
    - po pierwsze, jeżeli dany term został skonstruowany pewnym konstruktorem,
      to jego podtermami są rekurencyjne argumenty konstruktora. Przykład:
      [0] jest podtermem [S 0], zaś [nil] podtermem [cons 42 nil].
    - po drugie, jeżeli [t1] jest podtermem [t2], a [t2] podtermem [t3],
      to [t1] jest podtermem [t3] — własność ta nazywa się tranzytywnością.
      Przykład: [S 0] jest podtermem [S (S 0)], a zatem [0] jest podtermem
      [S (S 0)]. Podobnie [nil] jest podtermem [cons 666 (cons 42 nil)] *)

(** **** Ćwiczenie *)

(** Zdefiniuj relacje bycia podtermem dla liczb naturalnych i list. *)

(* begin hide *)
Inductive subterm_nat : nat -> nat -> Prop :=
    | subterm_nat_S : forall n : nat, subterm_nat n (S n)
    | subterm_nat_trans : forall x y z : nat,
        subterm_nat x y -> subterm_nat y z -> subterm_nat x z.

Inductive subterm_list {A : Type} : list A -> list A -> Prop :=
    | subterm_list_cons : forall (h : A) (t : list A),
        subterm_list t (h :: t)
    | subterm_list_trans : forall x y z : list A,
        subterm_list x y -> subterm_list y z -> subterm_list x z.

Inductive trans_clos {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
    | trans_clos_step : forall x y : A, R x y -> trans_clos R x y
    | trans_clos_trans : forall x y z : A,
        R x y -> trans_clos R y z -> trans_clos R x z.

Inductive subterm_nat_base : nat -> nat -> Prop :=
    | subterm_nat_base_c : forall n : nat, subterm_nat_base n (S n).

Definition subterm_nat' : nat -> nat -> Prop :=
    trans_clos subterm_nat_base.

Inductive subterm_list_base {A : Type} : list A -> list A -> Prop :=
    | subterm_list_base_c : forall (h : A) (t : list A),
        subterm_list_base t (h :: t).

Definition subterm_list' {A : Type} : list A -> list A -> Prop :=
    trans_clos subterm_list_base.
(* end hide *)

(** Udowodnij, że przytoczone wyżej przykłady nie są oszustwem.
    Komenda [Goal] jest wygodna, gdyż używając jej nie musimy
    nadawać twierdzeniu nazwy. Użycie [Qed] zapisze twierdzenie
    jako [Unnamed_thm], [Unnamed_thm0], [Unnamed_thm1] etc. *)

Goal subterm_nat 0 (S 0).
(* begin hide *)
Proof. constructor. Qed.
(* end hide *)

Goal subterm_list nil (cons 42 nil).
(* begin hide *)
Proof. constructor. Qed.
(* end hide *)

(* begin hide *)
Goal subterm_list' nil (cons 42 nil).
Proof. do 2 constructor. Qed.
(* end hide *)

(* begin hide *)
Goal subterm_nat' 0 (S 0).
Proof. do 2 constructor. Qed.
(* end hide *)

(** 

    Argumentem głównym funkcji [plus] jest jej pierwszy argument (o czym
    informuje nas adnotacja [{struct n}]), gdyż to on jest dopasowywany
    jako pierwszy (i jedyny). W przypadku gdy [n] jest równe [S p], [plus]
    jest wywoływany rekurencyjnie z argumentami [p] i [m], co jest dozwolone,
    gdyż jego argument główny, [p], jest podtermem [S p]. *)