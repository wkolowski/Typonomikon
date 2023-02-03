Require Import List.
Import ListNotations.

(**
  Mamy normalne listy, ale chcemy mieć sklejanie w czasie stałym. No i co tera?
  Zrobimy to co matematycy lubią najbardziej, czyli założymy, że bozia dała nam
  sklejanie w czasie stałym. Założenie możemy zrealizować, dodając konstruktor
  reprezentujący sklejanie do nowego typu list.
*)

Inductive AppList (A : Type) : Type :=
| Nil
| Cons (h : A) (t : AppList A)
| App  (l1 l2 : AppList A).

Arguments Nil  {A}.
Arguments Cons {A} _ _.
Arguments App  {A} _ _.

(**
  Niestety nie ma nic za darmo - może i dostaliśmy sklejanie w czasie stałym,
  ale za to urwanie liście głowy może teraz zajmować czas liniowy. Na dodatek
  typ ten jest trochę do dupy, bo nie spełnia równań, których spodziewalibyśmy
  się po sklejaniu, jak np.
  - [app (cons h t) l = cons h (app t l)] (obliczeniowo)
  - [app (app l1 l2) l3 = app l1 (app l2 l3)] (zdaniowo)

  Zrobimy sobie smart konstruktory, które temu zaradzą.
*)

Definition nil {A : Type} : AppList A :=
  Nil.

Definition cons {A : Type} (h : A) (t : AppList A) : AppList A :=
  Cons h t.

(**
  Oczywiście chcemy, żeby smart konstruktor [app] nie był rekurencyjny -
  wszakże sklejanie miało być w czasie stałym.
*)
Definition app {A : Type} (l1 l2 : AppList A) : AppList A :=
match l1 with
| Nil         => l2
| Cons h t    => Cons h (App t l2)
| App l11 l12 => App l11 (App l12 l2)
end.

(**
  Zdefiniujemy teraz predykat [Smart], który zachodzi, gdy lista jest zrobiona
  wyłącznie za pomocą smart konstruktorów. Jeżeli ograniczymy się do operowania
  tylko na takich listach, to wtedy będziemy mogli dobrać się do głowy w czasie
  stałym.
*)

Inductive Smart {A : Type} : AppList A -> Prop :=
| Smart_Nil : Smart Nil
| Smart_Cons (h : A) (t : AppList A) : Smart t -> Smart (Cons h t)
| Smart_App  (l1 l2 : AppList A) : Smart l1 -> Smart l2 -> Smart (app l1 l2).

(**
  Udowodnijmy sobie charakteryzację predykatu [Smart], która dla co mniej
  wprawionych umysłów może być zaskakująca: listy zrobione smart konstruktorami
  nie mają na wierzchu konstruktora [App].
*)

Lemma Smart_char :
  forall {A : Type} (l : AppList A),
    Smart l -> forall l1 l2 : AppList A, l <> App l1 l2.
Proof.
  induction 1; intros.
  - now congruence.
  - now congruence.
  - destruct l1; cbn.
    + now apply IHSmart2.
    + now congruence.
    + now contradiction IHSmart1 with l1_1 l1_2.
Qed.

(**
  Lub inaczej: użycie na pałę konstruktora [App] nie jest zbyt mądre.
*)

Lemma App_not_Smart :
  forall {A : Type} (l1 l2 : AppList A),
    ~ Smart (App l1 l2).
Proof.
  intros A l1 l2 HS.
  eapply Smart_char in HS.
  now apply HS.
Qed.

(**
  Możemy teraz zdefiniować funkcję [head]. Nie musimy przejmować się przypadkiem
  [App], bo wiemy, że w smart listach i tak nie wystąpi.
*)

Definition head {A : Type} (l : AppList A) : option A :=
match l with
| Nil      => None
| Cons h _ => Some h
| App _ _  => None
end.

(**
  Ale jak udowodnić, że nasza definicja [head] jest poprawna? Nie mówiąc już
  o dowodzeniu, że działa w czasie stałym? Otóż jest pewna chytra sztuczka:
  możemy zdefiniować wersję [head] z rekursją po paliwie, a następnie pokazać,
  że jeśli argument jest smart, to jest on [Nil]em lub do znalezienia głowy
  wystarczy 1 jednostka paliwa.
*)

Definition head' {A : Type} (fuel : nat) (l : AppList A) : option A :=
match fuel, l with
| S _, Cons h _  => Some h
| _  , _         => None
end.

Lemma head'_constant_time :
  forall {A : Type} (l : AppList A),
    Smart l -> l = Nil \/ head' 1 l <> None.
Proof.
  intros A [| h t | l1 l2] HS; cbn.
  - now left.
  - now right.
  - now eapply App_not_Smart in HS.
Qed.

(**
  Tada! Zrobilim listy ze sklejaniem w czasie stałym (zachowując jednocześnie
  urywanie głowy w czasie stałym) i wcale się przy tym nie namyślelim. Można
  się domyślić, że technika ta powinna zadziałać też w bardziej wyrafinowanych
  przypadkach, choć (jeszcze) tego nie sprawdziłem. Można się też zastanawiać,
  co powstanie, gdyby taką reprezentację list zrefunkcjonalizować i co to ma
  wspólnego z listami różnicowymi (https://en.wikipedia.org/wiki/Difference_list).
*)