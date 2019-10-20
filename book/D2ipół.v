(** W tym rozdziale będą różne formy indukcji/rekursji, których chwilowo nie
    chcę wstawiać do głównego tekstu rozdziałów D1 i D2, bo tam nie pasują.
    Prędzej czy później zostaną one z tymi rozdział zintegrowane (albo i nie -
    nie mamy pańskiego płaszcza i co nam pan zrobi?). *)

(** * Rekursja prymitywna (TODO) *)

(* begin hide *)
(** Tutaj opisać to, co w Agdzie zwie się "rekursją prymitywną", czyli taką,
    która dokładnie pasuje do kształtu indukcji w typie, a zatem można ją
    bezpośrednio przetłumaczyć na regułę indukcji. Co więcej, pojęcie to
    wydaje się być całkiem użyteczne w kontekście metody Bove-Capretta oraz
    mówienia o "kształcie rekursji" czy "kształcie indukcji". *)
(* end hide *)

(** * Rekursja zagnieżdżona *)

Require Import X3.

(** Czas na omówienie pewnej ciekawej, ale średnio użytecznej formy rekursji
    (z pamięci nie jestem w stanie przytoczyć więcej niż dwóch sztampowych
    przykładów jej użycia), a jest nią rekursja zagnieżdżona (zwana też
    czasem rekursją monotoniczną - kwestię najlepszej nazwy dla tego czegoś
    i jej uzasadnienia omówimy potem).

    Cóż to za zwierzątko, rekursja zagnieżdżona? Żeby się tego dowiedzieć,
    rzućmy najpierw okiem na przykład jakiejś funkcji, której definicja
    wymaga użycia rekursji zagnieżdżonej. *)

Fail Fixpoint ack (n m : nat) : nat :=
match n, m with
    | 0, m => S m
    | S n', 0 => ack n' 1
    | S n', S m' => ack n' (ack (S n') m')
end.

(* ===> The command has indeed failed with message:
        Cannot guess decreasing argument of fix. *)

(** Powyższa funkcja zwana jest funkcją Ackermanna, gdyż wymyślił ją...
    zgadnij kto. Jest ona całkiem sławna, choć z zupełnie innych powodów
    niż te, dla których my się jej przyglądamy. Nie oblicza ona niczego
    specjalnie użytecznego - jej wynikami są po prostu bardzo duże liczby.
    Jeżeli nie wierzysz, spróbuj policzyć ręcznie [ack 4 2] - zdziwisz się.

    Jak widać, Coq nie akceptuje powyższej definicji. Winny temu jest rzecz
    jasna kształt rekursji. Dla [n] równego [0] zwracamy [S m], co jest ok.
    Dla [n] postaci [S n'] i [m] równego [0] robimy wywołanie rekurencyjne
    na [n'] i [1], co również jest ok. Jednak jeżeli [n] i [m] odpowednio
    są postaci [S n'] i [S m'], to robimy wywołanie rekurencyjne postaci
    [ack n' (ack (S n') m')]. W wewnętrznym wywołaniu rekurencyjnym pierwszy
    argument jest taki sam jak w obecnym wywołaniu, a zatem pierwszy argument
    nie może być argumentem głównym. Gdyby argumentem głównym był drugi
    argument, to jest tym bardziej źle, gdyż w zewnętrznym wywołaniu
    rekurencyjnym nie jest nim [m'], lecz [ack (S n') m']. Nie ma się więc
    co dziwić, że Coq nie może zgadnąć, który argument ma być argumentem
    głównym.

    Mimo, że Coq nie akceptuje tej definicji, to wydaje się ona być całkiem
    spoko. Żaden z argumentów nie może wprawdzie posłużyć nam za argument
    główny, ale jeżeli rozważymy ich zachowanie jako całość, to okazuje się,
    że w każdym wywołaniu rekurencyjnym mamy dwie możliwości:
    - albo pierwszy argument się zmniejsza
    - albo pierwszy argument się nie zmienia, ale drugi argument się
      zmniejsza

    Możemy z tego wywnioskować, że jeżeli wywołamy [ack] na argumentach
    [n] i [m], to w ogólności najpierw [m] będzie się zmniejszał, ale
    ponieważ musi kiedyś spaść do zera, to wtedy [n] będzie musiał się
    zmniejszyć. Oczywiście wtedy w kolejnym wywołaniu zaczynamy znowu z
    jakimś [m], które potem się zmniejsza, aż w końcu znowu zmniejszy
    się [n] i tak dalej, aż do chwili, gdy [n] spadnie do zera. Wtedy
    rekursja musi się skończyć.

    Jednym z typowych zastosowań rekursji zagnieżdżonej jest radzenie
    sobie z takimi właśnie przypadkami, w których mamy ciąg argumentów
    i pierwszy maleje, lub pierwszy stoi w miejscu a drugi maleje i tak
    dalej. Z tego też powodu rekursja zagnieżdżona bywa czasem nazywana
    rekursją monotoniczną.

    Czas zobaczyć, jak techniki tej można użyć do zdefiniowania funkcji
    Ackermanna. *)

Fixpoint ack (n : nat) : nat -> nat :=
match n with
    | 0 => S
    | S n' =>
        fix ack' (m : nat) : nat :=
        match m with
            | 0 => ack n' 1
            | S m' => ack n' (ack' m')
        end
end.

(** Zauważmy przede wszystkim, że nieco zmienia się wygląd typu naszej
    funkcji. Jest on wprawdzie dokładnie taki sam ([nat -> nat -> nat]),
    ale zapisujemy go inaczej. Robimy to by podkreslić, że wynikiem [ack]
    jest funkcja. W przypadku gdy [n] jest postaci [S n'] zdefiniowana
    jest ona za pomocą [fix]a tak, jak wyglądają dwie ostatnie klauzule
    dopasowania z oryginalnej definicji, ale z wywołaniem [ack (S n') m']
    zastąpionym przez [ack' m']. Tak więc funkcja [ack'] reprezentuje
    częściową aplikację [ack n].

    Co w powyższej definicji sprawia, że jest to przykład rekursji
    zagnieżdżonej? *)

Print ack.
(* ===> ack =
        fix ack (n : nat) : nat -> nat :=
          match n with
          | 0 => S
          | S n' =>
              fix ack' (m : nat) : nat :=
                match m with
                | 0 => ack n' 1
                | S m' => ack n' (ack' m')
                end
          end
            : nat -> nat -> nat
*)

(** Tym, którzy nie pamiętają, przypominam, że komenda [Fixpoint] jest
    jedynie cukrem syntaktycznym na wyrażenie [fix], które służy do
    definiowania funkcji rekurencyjnych. [fix] działa podobnie jak [fun],
    ale pozwala dodatkowo nadać definiowanej przez siebie funkcji nazwę,
    dzięki czemu możemy robić wywołania rekurencyjne. Tak więc komendę
    [Fixpoint] możemy zastąpić komendą [Definition] i wyrażeniem [fix].

    Czym więc jest rekursja zagnieżdżona? Z rekursją zagnieżdżoną mamy
    do czynienia, gdy przez rekursję (czyli za pomocą [fix]a) definiujemy
    funkcję, która zwraca inną funkcję, i ta zwracana funkcja także jest
    zdefiniowana przez rekursję (czyli za pomocą [fix]a). Oczywiście to
    tylko pierwszy krok - wynikowa funkcja również może zwracać funkcję,
    która jest zdefiniowana przez rekursję i tak dalej.

    Widać zatem jak na dłoni, że [ack] jest zdefiniowane za pomocą rekursji
    zagnieżdżonej, gdyż w powyższej definicji za pomocą [fix]a definiujemy
    funkcję, która dla [n] postaci [S n'] zwraca funkcję zdefiniowaną za
    pomocą kolejnego [fix]a. *)

Definition plus : nat -> nat -> nat :=
  fix f (n : nat) : nat -> nat :=
  match n with
      | 0 => fun m : nat => m
      | S n' => fun m : nat => S (f n' m)
  end.

(** Dla balansu, powyższa definicja funkcji [plus] nie jest przykładem
    rekursji zagnieżdżonej, gdyż o ile definiujemy [plus] przez rekursję
    i zwracamy funkcję z [nat] w [nat], to funkcja ta zdefiniowana jest
    za pomocą [fun], a więc nie jest rekurencyjna.

    Podsumowując: rekursja jest zagnieżdżona, gdy w definicji funkcji
    pojawiają się co najmniej dwa wystąpienia [fix], jedno wewnątrz
    drugiego. Stąd też pochodzi nazwa "rekursja zagnieżdżona": jeden
    [fix] jest zagnieżdżony wewnątrz drugiego.

    Dobra, dość tych teoretycznych bajdurzeń. Zobaczmy, jak możemy udowodnić
    coś ciekawego na temat funkcji [ack]. *)

(* begin hide *)
Lemma ack_ind :
  forall
    (P : nat -> nat -> nat -> Prop)
    (P0 : forall m : nat, P 0 m (S m))
    (PS0 : forall n' : nat, P n' 1 (ack n' 1) -> P (S n') 0 (ack (S n') 0))
    (PSS : forall n' m' : nat,
      P (S n') m' (ack (S n') m') ->
      P n' (ack (S n') m') (ack n' (ack (S n') m')) ->
      P (S n') (S m') (ack (S n') (S m'))),
        forall n m : nat, P n m (ack n m).
Proof.
  induction n as [| n'].
    cbn. apply P0.
    induction m as [| m'].
      apply PS0. apply IHn'.
      apply PSS.
        apply IHm'.
        apply IHn'.
Qed.
(* end hide *)

Lemma ack_eq :
  forall n m : nat,
    ack n m =
    match n, m with
        | 0, _ => S m
        | S n', 0 => ack n' 1
        | S n', S m' => ack n' (ack (S n') m')
    end.
Proof.
  destruct n, m; reflexivity.
Qed.

(** Pierwszą i najważniejszą (bo najbardziej przydatną) rzeczą, której nam
    trzeba, jest równanie rekurencyjne, które charakteryzuje funkcję [ack]
    tak, jak nieudanie próbowaliśmy ją początkowo zdefiniować. Jest ono
    niesamowicie użyteczne, gdyż użycie taktyki [cbn] bardzo często będzie
    się kończyć odwinięciem definicji [ack], co skutkuje zaśmieceniem naszego
    drogocennego ekranu i utrudnia rozeznanie w stanie dowodu. *)

Lemma ack_big :
  forall n m : nat,
    m < ack n m.
Proof.
(* begin hide *)
  apply ack_ind.
    do 2 constructor.
    intros. cbn. omega.
    intros. rewrite ack_eq. omega.
Restart.
(* end hide *)
  induction n as [| n'].
    cbn. intro. apply le_n.
    induction m as [| m'].
      cbn. apply lt_trans with 1.
        apply le_n.
        apply IHn'.
      rewrite ack_eq. specialize (IHn' (ack (S n') m')). omega.
Qed.

(** Tadam... w sumie, to zaskoczenia nie ma. Reguła jest prosta: jeżeli
    funkcja jest zdefiniowana przez rekursję zagnieżdżoną, to dowody
    będą szły przez zagnieżdżone użycia indukcji.

    W powyższym dowodzie zaczynamy od indukcji po [n], bo jest to argument
    głównym funkcji [ack]. Pierwszy przypadek jest prosty - trzeba obliczyć
    i użyć zwrotność porządku. Drugi przypadek jest bardziej wymagający.
    Zauważ, że nie używamy tutaj taktyki [cbn], ponieważ skończyłoby się to
    odwinięciem definicji [ack] do nieprzyjemnej postaci.

    W drugim przypadku używamy indukcji po [m], gdyż jest ono argumentem
    głównym wewnętrznej funkcji [ack']. W pierwszym przypadku znów jest
    w miarę łatwo: zero jest mniejsze niż jeden, zaś jeden jest mniejsze
    od [ack n' 1] na mocy hipotezy indukcyjnej (ale tej pochodzącej od
    indukcji po [n], a nie po [m]!).

    W ostatnim przypadku również nie używamy [cbn] - efekt byłby podobny
    jak poprzednio, czyli zaśmiecenie ekranu długaśnym [fix]em. Zamiast
    tego korzystamy z równania rekurencyjnego, które elegancko przepisuje
    nam [ack] do pożądanej postaci. Dzięki odrobinie spostrzegawczości
    możemy zauważyć, że po odpowiednim zainstancjowaniu hipotezy indukcyjnej
    (tej pochodzącej z indukcji po [n], a nie po [m] - tej nie możemy wcale
    zainstancjować!) dostajemy szlaczek nierówności
    [m' < ack (S n') m' < ack n' (ack (S n') m')], z którego nasz celu wynika
    bez problemu - na szczęście nie musimy tego arytmetycznego rozumowania
    robić ręcznie, bo bozia dała nam taktykę [omega], która potrafi zrobić
    to sama. *)

(** **** Ćwiczenie *)

(** Udowodnij, że funkcja [ack] zachowuje porządek [<=], tzn. na większym
    lub równym argumencie (czy to pierwszym, czy drugim, czy obydwu) jej
    wynik również jest większy lub równy.

    Uwaga: to ćwiczenie jest trudne technicznie, ale nie konceptualnie. *)

Lemma ack_monotone :
  forall n1 n2 : nat, n1 <= n2 ->
    forall m1 m2 : nat, m1 <= m2 ->
      ack n1 m1 <= ack n2 m2.
(* begin hide *)
Proof.
  induction 1.
    induction 1.
      reflexivity.
      rewrite IHle. destruct n1.
        cbn. apply le_S, le_n.
        rewrite (ack_eq (S n1) (S m)).
          pose (ack_big n1 (ack (S n1) m)). omega.
    induction 1.
      destruct m1.
        cbn. apply IHle. do 2 constructor.
        rewrite (ack_eq (S m) (S m1)).
          rewrite (IHle (S m1) (ack (S m) m1)).
            reflexivity.
            apply ack_big.
      rewrite (ack_eq (S m)). apply IHle. apply le_trans with (S m0).
        apply le_S. exact H0.
        apply ack_big.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

Require Import Arith.

(** Zdefiniuj funkcję [merge] o typie
    [forall (A : Type) (cmp : A -> A -> bool), list A -> list A -> list A],
    która scala dwie listy posortowane według porządku wyznaczanego przez
    [cmp] w jedną posortowaną listę. Jeżeli któraś z list posortowana nie
    jest, wynik może być dowolny.

    Wskazówka: zgadnij, dlaczego to ćwiczenie pojawia się w podrozdziale o
    rekursji zagnieżdżonej. *)

(* begin hide *)
Fixpoint merge
  {A : Type} (cmp : A -> A -> bool) (l1 : list A) : list A -> list A :=
match l1 with
  | [] => fun l2 : list A => l2
  | h1 :: t1 =>
      fix merge' (l2 : list A) : list A :=
        match l2 with
          | [] => l1
          | h2 :: t2 =>
              if cmp h1 h2
              then h1 :: merge cmp t1 l2
              else h2 :: merge' t2
        end
end.
(* end hide *)

Compute merge leb [1; 4; 6; 9] [2; 3; 5; 8].
(* ===> = [[1; 2; 3; 4; 5; 6; 8; 9]]
        : list nat *)

(** Obie listy są posortowane według [leb], więc wynik też jest. *)

Compute merge leb [5; 3; 1] [4; 9].
(* ===> = [[4; 5; 3; 1; 9]]
        : list nat *)

(** Pierwsza lista nie jest posortowana według [leb], więc wynik jest
    z dupy. *)

(** **** Ćwiczenie *)

(** Skoro już udało ci się zdefiniować [merge], to udowodnij jeszcze parę
    lematów, cobyś nie miał za dużo wolnego czasu. *)

Lemma merge_eq :
  forall {A : Type} {cmp : A -> A -> bool} {l1 l2 : list A},
    merge cmp l1 l2 =
    match l1, l2 with
        | [], _ => l2
        | _, [] => l1
        | h1 :: t1, h2 :: t2 =>
            if cmp h1 h2
            then h1 :: merge cmp t1 l2
            else h2 :: merge cmp l1 t2
    end.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      reflexivity.
      destruct (cmp h1 h2); cbn.
        rewrite IHt1. reflexivity.
        rewrite IHt2. reflexivity.
Qed.
(* end hide *)

Lemma merge_nil_l :
  forall {A : Type} {cmp : A -> A -> bool} {l : list A},
    merge cmp [] l = l.
(* begin hide *)
Proof.
  reflexivity.
Qed.
(* end hide *)

Lemma merge_nil_r :
  forall {A : Type} {cmp : A -> A -> bool} {l : list A},
    merge cmp l [] = l.
(* begin hide *)
Proof.
  destruct l; reflexivity.
Qed.
(* end hide *)

Lemma merge_length :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 : list A},
    length (merge f l1 l2) = length l1 + length l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      rewrite <- plus_n_O. reflexivity.
      destruct (f h1 h2); cbn.
        rewrite IHt1. cbn. reflexivity.
        rewrite IHt2. rewrite plus_n_Sm. reflexivity.
Qed.
(* end hide *)

(* begin hide *)
Ltac inv H := inversion H; subst.

Lemma merge_rev :
  forall {A : Type} {cmp : A -> A -> bool} {l1 l2 : list A},
    merge cmp (rev l1) (rev l2) =
    rev (merge (fun x y : A => cmp y x) l1 l2).
Proof.
  induction l1 as [| h1 t1].
    intros. cbn. reflexivity.
    induction l2 as [| h2 t2].
      cbn. rewrite merge_nil_r. reflexivity.
      rewrite !merge_eq. cbn [rev].
        case_eq (rev t1 ++ [h1]); intros.
          apply (f_equal rev) in H. rewrite rev_app in H. inversion H.
          case_eq (rev t2 ++ [h2]); intros.
            apply (f_equal rev) in H0. rewrite rev_app in H0. inversion H0.
            destruct t1, t2.
              inv H; inv H0. cbn. admit.
              inv H. cbn in H0. rewrite merge_nil_l.
Abort.
(* end hide *)

(* begin hide *)
Lemma merge_rev :
  forall {A : Type} {cmp : A -> A -> bool} {l1 l2 : list A},
    merge cmp l1 l2 = rev (merge (fun x y : A => cmp y x) (rev l1) (rev l2)).
Proof.
  induction l1 as [| h1 t1].
    intros. cbn. rewrite rev_inv. reflexivity.
    induction l2 as [| h2 t2].
      rewrite merge_eq. case_eq (rev t1 ++ [h1]); intros.
        apply (f_equal length) in H. rewrite length_app, plus_comm in H.
          inversion H.
        cbn. rewrite merge_nil_r, rev_app, rev_inv. cbn. reflexivity.
      rewrite !merge_eq. case_eq (cmp h1 h2); intros.
        
Abort.
(* end hide *)

Lemma merge_map :
  forall {A B : Type} {cmp : B -> B -> bool} {f : A -> B} {l1 l2 : list A},
      merge cmp (map f l1) (map f l2) =
      map f (merge (fun x y : A => cmp (f x) (f y)) l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      reflexivity.
      destruct (cmp (f h1) (f h2)); cbn.
        rewrite <- IHt1. cbn. reflexivity.
        rewrite IHt2. reflexivity.
Qed.
(* end hide *)

Lemma merge_replicate :
  forall {A : Type} {cmp : A -> A -> bool} {x y : A} {n m : nat},
    merge cmp (replicate n x) (replicate m y) =
    if cmp x y
    then replicate n x ++ replicate m y
    else replicate m y ++ replicate n x.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    destruct (cmp x y); try reflexivity.
      intros. rewrite app_nil_r. reflexivity.
    induction m as [| m']; cbn.
      destruct (cmp x y).
        rewrite app_nil_r. reflexivity.
        reflexivity.
      case_eq (cmp x y); intro eq.
        rewrite merge_eq. destruct n'; cbn.
          reflexivity.
          specialize (IHn' (S m')). cbn in IHn'.
            rewrite eq, <- IHn' in *. reflexivity.
        rewrite IHm', eq. reflexivity.
Qed.
(* end hide *)

Fixpoint ins
  {A : Type} (cmp : A -> A -> bool) (x : A) (l : list A) : list A :=
match l with
    | [] => [x]
    | h :: t => if cmp x h then x :: h :: t else h :: ins cmp x t
end.

Lemma merge_ins_l :
  forall {A : Type} {cmp : A -> A -> bool} {l : list A} {x : A},
    merge cmp [x] l = ins cmp x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (cmp x h).
      reflexivity.
      rewrite <- IHt. cbn. reflexivity.
Qed.
(* end hide *)

Lemma merge_ins_r :
  forall {A : Type} {cmp : A -> A -> bool} {l : list A} {x : A},
    merge cmp l [x] = ins cmp x l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (cmp h x), (cmp x h).
Abort.
(* end hide *)

Lemma merge_ins' :
  forall {A : Type} {cmp : A -> A -> bool} {l1 l2 : list A} {x : A},
    merge cmp (ins cmp x l1) (ins cmp x l2) =
    ins cmp x (ins cmp x (merge cmp l1 l2)).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    induction l2 as [| h2 t2]; cbn.
      reflexivity.
      intro. case_eq (cmp x h2); cbn; intros.
        destruct (cmp x x).
          reflexivity.
          rewrite H. reflexivity.
        rewrite H, IHt2. reflexivity.
    induction l2 as [| h2 t2]; cbn; intros.
      case_eq (cmp x h1); cbn; intros eq.
        destruct (cmp x x).
          destruct (cmp h1 x).
            admit.
            reflexivity.
          rewrite eq. reflexivity.
        rewrite eq. destruct (cmp h1 x).
Abort.
(* end hide *)

Lemma merge_all_true :
  forall {A : Type} {cmp : A -> A -> bool} {l : list A} {x : A},
    all (fun y : A => cmp x y) l = true ->
      merge cmp [x] l = x :: l.
(* begin hide *)
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    case_eq (cmp x h); intros eq.
      reflexivity.
      rewrite eq in H. cbn in H. inversion H.
Qed.
(* end hide *)

Lemma merge_ind :
  forall {A : Type} (P : list A -> list A -> list A -> Prop)
    {f : A -> A -> bool},
      (forall l : list A, P [] l l) ->
      (forall l : list A, P l [] l) ->
      (forall (h1 h2 : A) (t1 t2 r : list A),
        f h1 h2 = true ->
          P t1 (h2 :: t2) r -> P (h1 :: t1) (h2 :: t2) (h1 :: r)) ->
      (forall (h1 h2 : A) (t1 t2 r : list A),
        f h1 h2 = false ->
          P (h1 :: t1) t2 r -> P (h1 :: t1) (h2 :: t2) (h2 :: r)) ->
      forall l1 l2 : list A, P l1 l2 (merge f l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    apply H.
    induction l2 as [| h2 t2]; cbn.
      apply H0.
      case_eq (f h1 h2); intros.
        apply H1.
          assumption.
          apply IHt1.
        apply H2.
          assumption.
          apply IHt2.
Defined.
(* end hide *)

Lemma all_merge :
  forall {A : Type} (cmp : A -> A -> bool) (p : A -> bool) (l1 l2 : list A),
    all p (merge cmp l1 l2) = all p l1 && all p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1].
    cbn. reflexivity.
    induction l2 as [| h2 t2].
      cbn. rewrite andb_true_r. reflexivity.
      rewrite merge_eq. destruct (cmp h1 h2).
        cbn. rewrite IHt1, andb_assoc. cbn. reflexivity.
        cbn [all]. rewrite IHt2. cbn. rewrite !andb_assoc.
          destruct (p h1), (p h2); cbn;
          rewrite ?andb_true_r, ?andb_false_r; cbn; reflexivity.
Qed.
(* end hide *)

Lemma any_merge :
  forall {A : Type} (cmp : A -> A -> bool) (p : A -> bool) (l1 l2 : list A),
    any p (merge cmp l1 l2) = any p l1 || any p l2.
(* begin hide *)
Proof.
  intros. rewrite any_all, all_merge, negb_andb, <- !any_all. reflexivity.
Qed.
(* end hide *)

Lemma count_merge :
  forall {A : Type} (cmp : A -> A -> bool) (p : A -> bool) (l1 l2 : list A),
    count p (merge cmp l1 l2) = count p l1 + count p l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1].
    cbn. reflexivity.
    induction l2 as [| h2 t2].
      cbn. rewrite <- plus_n_O. reflexivity.
      rewrite merge_eq. destruct (cmp h1 h2).
        cbn. rewrite IHt1. cbn. destruct (p h1), (p h2); omega.
        cbn [count]. rewrite IHt2. cbn. destruct (p h1), (p h2); omega.
Qed.
(* end hide *)

Lemma merge_filter :
  forall {A : Type} {cmp : A -> A -> bool} {p : A -> bool} {l1 l2 : list A},
    merge cmp (filter p l1) (filter p l2) =
    filter p (merge cmp l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1].
    cbn. reflexivity.
    induction l2 as [| h2 t2].
      cbn. rewrite merge_nil_r. reflexivity.
      cbn [filter] in *. rewrite (@merge_eq _ _ (h1 :: t1)).
        case_eq (cmp h1 h2); intros.
          cbn. case_eq (p h1); case_eq (p h2); intros eq2 eq1;
          cbn [filter]; rewrite ?eq1, ?eq2 in *.
            rewrite merge_eq, H, <- IHt1. cbn. rewrite eq2. reflexivity.
            rewrite <- IHt1. cbn [filter]. rewrite eq2, IHt2.
Abort.
(* end hide *)

(* begin hide *)
Definition extend
  {A B : Type} (f : A -> option B) (cmp : B -> B -> bool) (x y : A) : bool :=
match f x, f y with
    | Some b1, Some b2 => cmp b1 b2
    | _, _ => false
end.

Lemma pmap_merge :
  forall
    (A B : Type) (f : A -> option B)
    (cmp : B -> B -> bool) (l1 l2 : list A),
      merge cmp (pmap f l1) (pmap f l2) =
      pmap f (merge (extend f cmp) l1 l2).
Proof.
  induction l1 as [| h1 t1].
    cbn. reflexivity.
    induction l2 as [| h2 t2].
      cbn. destruct (f h1).
        cbn. reflexivity.
        rewrite merge_nil_r. reflexivity.
      rewrite (@merge_eq _ _ (h1 :: t1)). destruct (extend f cmp h1 h2).
        cbn [pmap] in *. destruct (f h1), (f h2).
          rewrite <- IHt1.
Abort.
(* end hide *)

Lemma Permutation_merge :
  forall {A : Type} {f : A -> A -> bool} {l1 l2 : list A},
    Permutation (merge f l1 l2) (l1 ++ l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn.
      rewrite app_nil_r. reflexivity.
      destruct (f h1 h2).
        rewrite IHt1. reflexivity.
        rewrite IHt2. rewrite perm_swap.
          constructor. rewrite Permutation_app_comm.
            rewrite (Permutation_app_comm _ t1 (h2 :: t2)). reflexivity.
Qed.
(* end hide *)

(** * Rekursja wyższego rzędu (TODO) *)

(** ACHTUNG: bardzo upośledzona wersja alfa.

    Pozostaje kwestia rekursji wyższego rzędu. Co to takiego? Ano dotychczas
    wszystkie nasze wywołania rekurencyjne były konkretne, czyli zaaplikowane
    do argumentów.

    Mogłoby się wydawać, że jest to jedyny możliwy sposób robienia wywołań
    rekurencyjnych, jednak nie jest tak. Wywołania rekurencyjne mogą mieć
    również inną, wyższorzędową postać, a mianowicie - możemy przekazać
    funkcję, którą właśnie definiujemy, jako argument do innej funkcji.

    Dlaczego jest to wywołanie rekurencyjne, skoro nie wywołujemy naszej
    funkcji? Ano dlatego, że tamta funkcja, która dostaje naszą jako
    argument, dostaje niejako możliwość robienia wywołań rekurencyjnych.
    W zależności od tego, co robi ta funkcja, wszystko może być ok (np.
    gdy ignoruje ona naszą funkcję i w ogóle jej nie używa) lub śmiertelnie
    niebezpieczne (gdy próbuje zrobić wywołanie rekurencyjne na strukturalnie
    większym argumencie).

    Sztoby za dużo nie godoć, bajszpil: *)

Inductive Tree (A : Type) : Type :=
    | Node : A -> list (Tree A) -> Tree A.

Arguments Node {A} _ _.

(** [Tree] to typ drzew niepustych, które mogą mieć dowolną (ale skończoną)
    ilość poddrzew. Spróbujmy zdefiniować funkcję, która zwraca lustrzane
    odbicie drzewa. *)

(*
Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
match t with
    | Node x ts => Node x (rev (map mirror ts))
end.
*)

(** Nie jest to zbyt trudne. Rekurencyjnie odbijamy wszystkie poddrzewa za
    pomocą [map mirror], a następnie odwracamy kolejność poddrzew z użyciem
    [rev]. Chociaż poszło gładko, to mamy tu do czynienia z czymś, czego
    wcześniej nie widzieliśmy. Nie ma tu żadnego wywołania rekurencyjnego,
    a mimo to funkcja działa ok. Dlaczego? Właśnie dlatego, że wywołania
    rekurencyjne są robione przez funkcję [map]. Mamy więc do czynienia z
    rekursją wyższego rzędu. *)

(*
Print Forall2.

Inductive mirrorG {A : Type} : Tree A -> Tree A -> Prop :=
  | mirrorG_0 :
      forall (x : A) (ts rs : list (Tree A)),
        Forall2 mirrorG ts rs -> mirrorG (Node x ts) (Node x (rev rs)).

Definition mab {A B : Type} (f : A -> B) :=
  fix mab (l : list A) : list B :=
  match l with
      | [] => []
      | h :: t => f h :: mab t
  end.
*)

(** Inny przykład: *)

Inductive Tree' (A : Type) : Type :=
    | Node' : A -> forall {B : Type}, (B -> Tree' A) -> Tree' A.

Arguments Node' {A} _ _ _.

(** Tym razem mamy drzewo, które może mieć naprawdę dowolną ilość poddrzew,
    ale jego poddrzewa są nieuporządkowane. *)

Fixpoint mirror' {A : Type} (t : Tree' A) : Tree' A :=
match t with
    | Node' x B ts => Node' x B (fun b : B => mirror' (ts b))
end.