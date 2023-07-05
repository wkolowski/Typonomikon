(** * D2bb: Rekursja monotoniczna [TODO] *)

(** * Rekursja monotoniczna *)

From Typonomikon Require Import D5.

(** Czas na omówienie pewnej ciekawej, ale średnio użytecznej formy rekursji
    (z pamięci nie jestem w stanie przytoczyć więcej niż dwóch sztampowych
    przykładów jej użycia), a jest nią rekursja monotoniczna (zwana też
    czasem rekursją zagnieżdżoną, ale nie będziemy używać tej nazwy, gdyż
    dotychczas używaliśmy jej na określenie rekursji, w której arguemntem
    wywołania rekurencyjnego jest wynik innego wywołania rekurencyjnego).

    Cóż to za zwierzątko, rekursja monotoniczna? Żeby się tego dowiedzieć,
    przypomnijmy sobie najpierw, jak technicznie w Coqu zrealizowana jest
    rekursja strukturalna. *)

Fixpoint plus (n : nat) : nat -> nat :=
match n with
| 0 => fun m : nat => m
| S n' => fun m : nat => S (plus n' m)
end.

(** Oto definicja funkcji plus, lecz zapisana nieco inaczej, niż gdy
    widzieliśmy ją ostatnim razem. Tym razem prezentujemy ją jako funkcję
    biorącą jeden argument typu [nat] i zwracającą funkcję z typu [nat] w
    typ [nat]. *)

Definition plus' : nat -> nat -> nat :=
  fix f (n : nat) : nat -> nat :=
  match n with
  | 0 => fun m : nat => m
  | S n' => fun m : nat => S (f n' m)
  end.

(** Ale komenda [Fixpoint] jest jedynie cukrem syntaktycznym - funkcję [plus]
    możemy równie dobrze zdefiniować bez niej, posługując się jedynie komendą
    [Definition], a wyrażeniem, które nam to umożliwia, jest [fix]. [fix]
    działa podobnie jak [fun], ale pozwala dodatkowo nadać definiowanej przez
    siebie funkcji nazwę, dzięki czemu możemy robić wywołania rekurencyjne.

    Czym więc jest rekursja monotoniczna? Z rekursją monotoniczną mamy do
    czynienia, gdy za pomocą [fix]a (czyli przez rekursję) definiujemy
    funkcję, która zwraca inną funkcję, i ta zwracana funkcja także jest
    zdefiniowana za pomocą [fix]a (czyli przez rekursję). Oczywiście to
    tylko pierwszy krok - wynikowa funkcja również może zwracać funkcję,
    która jest zdefiniowana za pomocą [fix]a i tak dalej.

    Widać zatem jak na dłoni, że [plus] ani [plus'] nie są przykładami
    rekursji monotonicznej. Wprawdzie definiują one za pomocą [fix]a
    (lub komendy [Fixpoint]) funkcję, która zwraca inną funkcję, ale ta
    zwracana funkcja nie jest zdefiniowana za pomocą [fix]a, lecz za
    pomocą [fun], a więc nie jest rekurencyjna.

    Podsumowując: rekursja jest monotoniczna, jeżeli w definicji
    funkcji pojawiają się co najmniej dwa wystąpienia [fix], jedno
    wewnątrz drugiego (przy czym rzecz jasna [Fixpoint] też liczy
    się jako [fix]).

    No to skoro już wiemy, czas zobaczyć przykład jakiejś funkcji, która
    jest zdefiniowana przez rekursję monotoniczną. *)

(** * Funkcja Ackermanna *)

Fail Fixpoint ack (n m : nat) : nat :=
match n, m with
| 0, m => S m
| S n', 0 => ack n' 1
| S n', S m' => ack n' (ack (S n') m')
end.

(* ===> The command has indeed failed with message:
        Cannot guess decreasing argument of fix. *)

(** Powyższa funkcja zwana jest funkcją Ackermanna, gdyż wymyślił ją...
    zgadnij kto. Jest ona całkiem sławna, choć z zupełnie innych powodów
    niż te, dla których my się jej przyglądamy. Nie oblicza ona niczego
    specjalnie użytecznego - jej wynikami są po prostu bardzo duże liczby.
    Jeżeli nie wierzysz, spróbuj policzyć ręcznie [ack 4 2] - zdziwisz się.

    Jak widać, Coq nie akceptuje powyższej definicji. Winny temu jest rzecz
    jasna kształt rekursji. Dla [n] równego [0] zwracamy [S m], co jest ok.
    Dla [n] postaci [S n'] i [m] równego [0] robimy wywołanie rekurencyjne
    na [n'] i [1], co również jest ok. Jednak jeżeli [n] i [m] odpowednio
    są postaci [S n'] i [S m'], to robimy wywołanie rekurencyjne postaci
    [ack n' (ack (S n') m')]. W wewnętrznym wywołaniu rekurencyjnym pierwszy
    argument jest taki sam jak obecny. Gdyby argumentem głównym był drugi
    argument, to jest tym bardziej źle, gdyż w zewnętrznym wywołaniu
    rekurencyjnym nie jest nim [m'], lecz [ack (S n') m']. Nie ma się więc
    co dziwić, że Coq nie może zgadnąć, który argument ma być argumentem
    głównym.

    Mimo, że Coq nie akceptuje tej definicji, to wydaje się ona być całkiem
    spoko. Żaden z argumentów nie może wprawdzie posłużyć nam za argument
    główny, ale jeżeli rozważymy ich zachowanie jako całość, to okazuje się,
    że w każdym wywołaniu rekurencyjnym mamy dwie możliwości:
    - albo pierwszy argument się zmniejsza
    - albo pierwszy argument się nie zmienia, ale drugi argument się
      zmniejsza

    Możemy z tego wywnioskować, że jeżeli wywołamy [ack] na argumentach
    [n] i [m], to w ogólności najpierw [m] będzie się zmniejszał, ale
    ponieważ musi kiedyś spaść do zera, to wtedy [n] będzie musiał się
    zmniejszyć. Oczywiście wtedy w kolejnym wywołaniu zaczynamy znowu z
    jakimś [m], które potem się zmniejsza, aż w końcu znowu zmniejszy
    się [n] i tak dalej, aż do chwili, gdy [n] spadnie do zera. Wtedy
    rekursja musi się skończyć.

    Jednym z typowych zastosowań rekursji zagnieżdżonej jest radzenie
    sobie z takimi właśnie przypadkami, w których mamy ciąg argumentów
    i pierwszy maleje, lub pierwszy stoi w miejscu a drugi maleje i tak
    dalej. Zobaczmy więc, jak techniki tej można użyć do zdefiniowania
    funkcji Ackermanna. *)

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

(** Zauważmy przede wszystkim, że nieco zmienia się wygląd typu naszej
    funkcji. Jest on wprawdzie dokładnie taki sam ([nat -> nat -> nat]),
    ale zapisujemy go inaczej. Robimy to by podkreslić, że wynikiem [ack]
    jest funkcja. W przypadku gdy [n] jest postaci [S n'] zdefiniowana
    jest ona za pomocą [fix]a tak, jak wyglądają dwie ostatnie klauzule
    dopasowania z oryginalnej definicji, ale z wywołaniem [ack (S n') m']
    zastąpionym przez [ack' m']. Tak więc funkcja [ack'] reprezentuje
    częściową aplikację [ack n]. *)

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

Lemma ack_big :
  forall n m : nat,
    m < ack n m.
Proof.
(* begin hide *)
  apply ack_ind.
    do 2 constructor.
    intros. cbn. lia.
    intros. rewrite ack_eq. lia.
Restart.
(* end hide *)
  induction n as [| n'].
    cbn. intro. apply le_n.
    induction m as [| m'].
      cbn. apply Nat.lt_trans with 1.
        apply le_n.
        apply IHn'.
      specialize (IHn' (ack (S n') m')).
        rewrite ack_eq. lia.
Qed.

Lemma ack_big' :
  forall n1 n2 : nat, n1 <= n2 ->
    forall m1 m2 : nat, m1 <= m2 ->
      ack n1 m1 <= ack n2 m2.
Proof.
  induction 1.
    induction 1.
      reflexivity.
      rewrite IHle. destruct n1.
        cbn. apply le_S, le_n.
        rewrite (ack_eq (S n1) (S m)).
          pose (ack_big n1 (ack (S n1) m)). lia.
    induction 1.
      destruct m1.
        cbn. apply IHle. do 2 constructor.
        rewrite (ack_eq (S m) (S m1)).
          rewrite (IHle (S m1) (ack (S m) m1)).
            reflexivity.
            apply ack_big.
      rewrite (ack_eq (S m)). apply IHle. apply Nat.le_trans with (S m0).
        apply le_S. exact H0.
        apply ack_big.
Qed.

(** * Scalanie posortowanych list *)

(** **** Ćwiczenie *)

Require Import Arith.

(** Zdefiniuj funkcję [merge] o typie
    [forall (A : Type) (cmp : A -> A -> bool), list A -> list A -> list A],
    która scala dwie listy posortowane według porządku wyznaczanego przez
    [cmp] w jedną posortowaną listę. Jeżeli któraś z list posortowana nie
    jest, wynik może być dowolny.

    Wskazówka: dlaczego niby to ćwiczenie pojawia się w podrozdziale o
    rekursji zagnieżdżonej? *)

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

(** Skoro już udało ci się zdefiniować [merge], to udowodnij jeszcze parę
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
Proof.
  reflexivity.
Qed.

Lemma merge_nil_r :
  forall {A : Type} {cmp : A -> A -> bool} {l : list A},
    merge cmp l [] = l.
Proof.
  destruct l; reflexivity.
Qed.

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

(* begin hide *)
Lemma merge_rev :
  forall {A : Type} {cmp : A -> A -> bool} {l1 l2 : list A},
    merge cmp l1 l2 = rev (merge (fun x y : A => cmp y x) (rev l1) (rev l2)).
Proof.
  induction l1 as [| h1 t1]; cbn.
    intros. rewrite rev_rev. reflexivity.
    induction l2 as [| h2 t2]; cbn.
      rewrite merge_eq. case_eq (snoc h1 (rev t1)); intros.
        apply (f_equal length) in H. rewrite length_snoc in H. inv H.
        rewrite <- H, snoc_rev, rev_rev. reflexivity.
      rewrite IHt1, IHt2. case_eq (cmp h1 h2); intros.
Abort.
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

Lemma merge_filter :
  forall {A : Type} {cmp : A -> A -> bool} {p : A -> bool} {l1 l2 : list A},
    merge cmp (filter p l1) (filter p l2) =
    filter p (merge cmp l1 l2).
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn.
    reflexivity.
    induction l2 as [| h2 t2]; cbn in *.
      destruct (p h1); cbn.
        reflexivity.
        rewrite merge_eq. destruct (filter p t1); reflexivity.
      case_eq (p h1); case_eq (p h2); case_eq (cmp h1 h2);
      intros eq1 eq2 eq3;
      repeat (cbn in *; rewrite ?eq1, ?eq2, ?eq3 in *); cbn.
        rewrite <- IHt1. cbn. rewrite eq2. reflexivity.
        rewrite IHt2. reflexivity.
Restart.
  intros until p.
  apply (merge_ind (fun l1 l2 r : list A =>
    merge cmp (filter p l1) (filter p l2) = filter p r));
  cbn; intros.
    reflexivity.
    rewrite merge_eq. destruct (filter p l); reflexivity.
    destruct (p h1), (p h2); cbn; rewrite ?H.
      rewrite H0. reflexivity.
      rewrite <- H0. destruct t2; cbn.
        admit.
Abort.
(* end hide *)