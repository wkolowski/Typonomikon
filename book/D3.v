(** * D3: Logika boolowska, rozstrzygalność i reflekcja [TODO] *)

(** UWAGA: ten rozdział właśnie ulega konceptualnemu przeobrażeinu i
    może być nie na miejscu, tzn. zawierać rzeczy, o których jeszcze
    nie było mowy. *)

(** * Logika boolowska *)

(** Zadania z funkcji boolowskich, sprawdzające radzenie sobie w pracy
    z enumeracjami, definiowaniem funkcji przez dopasowanie do wzorca
    i dowodzeniem przez rozbicie na przypadki.

    Chciałem, żeby nazwy twierdzeń odpowiadały tym z biblioteki standardowej,
    ale na razie nie mam siły tego ujednolicić. *)

Section boolean_functions.
Variables b b1 b2 b3 : bool.

(** * Definicje *)

(** Zdefiniuj następujące funkcje boolowskie:
    - [negb] (negacja)
    - [andb] (koniunkcja)
    - [orb] (alternatywa)
    - [implb] (implikacja)
    - [eqb] (równoważność)
    - [xorb] (alternatywa wykluczająca)
    - [nor]
    - [nand] *)

(* begin hide *)
Definition negb (b : bool) : bool :=
match b with
    | true => false
    | false => true
end.

Definition andb (b1 b2 : bool) : bool :=
match b1 with
    | true => b2
    | false => false
end.

Definition orb (b1 b2 : bool) : bool :=
match b1 with
    | true => true
    | false => b2
end.

Definition implb (b1 b2 : bool) : bool :=
match b1 with
    | true => b2
    | false => true
end.

Definition eqb (b1 b2 : bool) : bool :=
match b1, b2 with
    | true, true => true
    | false, false => true
    | _, _ => false
end.

Definition xorb (b1 b2 : bool) : bool :=
match b1, b2 with
    | true, false => true
    | false, true => true
    | _, _ => false
end.

Definition nandb (b1 b2 : bool) : bool := negb (andb b1 b2).
Definition norb (b1 b2 : bool) : bool := negb (orb b1 b2).
(* end hide *)

Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).

(** * Twierdzenia *)

(** Udowodnij, że zdefiniowane przez ciebie funkcje mają spodziewane
    właściwości. *)

(* begin hide *)
Ltac solve_bool := intros; match goal with
    | b : bool |- _ => destruct b; clear b; solve_bool
    | _ => cbn; auto
end.
(* end hide *)

(** *** Właściwości negacji *)

Theorem negb_inv : negb (negb b) = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem negb_ineq : negb b <> b.
(* begin hide *)
Proof. destruct b; discriminate. Qed.
(* end hide *)

(** *** Eliminacja *)

Theorem andb_elim_l : b1 && b2 = true -> b1 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem andb_elim_r : b1 && b2 = true -> b2 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem andb_elim : b1 && b2 = true -> b1 = true /\ b2 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_elim : b1 || b2 = true -> b1 = true \/ b2 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Elementy neutralne *)

Theorem andb_true_neutral_l : true && b = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem andb_true_neutral_r : b && true = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_false_neutral_l : false || b = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_false_neutral_r : b || false = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Anihilacja *)

Theorem andb_false_annihilation_l : false && b = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem andb_false_annihilation_r : b && false = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_true_annihilation_l :  true || b = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_true_annihilation_r :  b || true = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Łączność *)

Theorem andb_assoc : b1 && (b2 && b3) = (b1 && b2) && b3.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_assoc : b1 || (b2 || b3) = (b1 || b2) || b3.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Przemienność *)

Theorem andb_comm : b1 && b2 = b2 && b1.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_comm : b1 || b2 = b2 || b1.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Rozdzielność *)

Theorem andb_dist_orb :
  b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_dist_andb :
  b1 || (b2 && b3) = (b1 || b2) && (b1 || b3).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Wyłączony środek i niesprzeczność *)

Theorem andb_negb : b && negb b = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_negb : b || negb b = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Prawa de Morgana *)

Theorem negb_andb : negb (b1 && b2) = negb b1 || negb b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem negb_orb : negb (b1 || b2) = negb b1 && negb b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** [eqb], [xorb], [norb], [nandb] *)

Theorem eqb_spec : eqb b1 b2 = true -> b1 = b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem eqb_spec' : eqb b1 b2 = false -> b1 <> b2.
(* begin hide *)
Proof. destruct b1, b2; do 2 inversion 1. Qed.
(* end hide *)

Theorem xorb_spec :
  xorb b1 b2 = negb (eqb b1 b2).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem xorb_spec' :
  xorb b1 b2 = true -> b1 <> b2.
(* begin hide *)
Proof. destruct b1, b2; do 2 inversion 1. Qed.
(* end hide *)

Theorem norb_spec :
  norb b1 b2 = negb (b1 || b2).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem nandb_spec :
  nandb b1 b2 = negb (b1 && b2).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Różne *)

Theorem andb_eq_orb :
  b1 && b2 = b1 || b2 -> b1 = b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem all3_spec :
  (b1 && b2) || (negb b1 || negb b2) = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem noncontradiction_bool :
  negb (eqb b (negb b)) = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem excluded_middle_bool :
  b || negb b = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

End boolean_functions.

(** * Rozstrzygalność *)

Theorem excluded_middle :
  forall P : Prop, P \/ ~ P.
Proof.
  intro. left.
Restart.
  intro. right. intro.
Abort.

(** Próba udowodnienia tego twierdzenia pokazuje nam zasadniczą różnicę
    między logiką konstruktywną, która jest domyślną logiką Coqa, oraz
    logiką klasyczną, najpowszechniej znanym i używanym rodzajem logiki.

    Każde zdanie jest, w pewnym "filozoficznym" sensie, prawdziwe lub
    fałszywe i to właśnie powyższe zdanie oznacza w logice klasycznej.
    Logika konstruktywna jednak, jak już wiemy, nie jest logiką prawdy,
    lecz logiką udowadnialności i ma swoją interpretację obliczeniową.
    Powyższe zdanie w logice konstruktywnej oznacza: program komputerowy
    [exluded_middle] rozstrzyga, czy dowolne zdanie jest prawdziwe, czy
    fałszywe.

    Skonstruowanie programu o takim typie jest w ogólności niemożliwe,
    gdyż dysponujemy zbyt małą ilością informacji: nie wiemy czym jest
    zdanie [P], a nie posiadamy żadnego ogólnego sposobu dowodzenia lub
    obalania zdań o nieznanej nam postaci. Nie możemy np. użyć indukcji,
    gdyż nie wiemy, czy zdanie [P] zostało zdefiniowane induktywnie, czy
    też nie. W Coqu jedynym sposobem uzyskania termu o typie [forall
    P : Prop, P \/ ~ P] jest przyjęcie go jako aksjomat. *)

Theorem True_dec : True \/ ~ True.
Proof.
  left. trivial.
Qed.

(** Powyższe dywagacje nie przeszkadzają nam jednak w udowadnianiu,
    że reguła wyłączonego środka zachodzi dla pewnych konkretnych
    zdań. Zdanie takie będziemy nazywać zdaniami rozstrzygalnymi
    (ang. decidable). O pozostałych zdaniach będziemy mówić, że są 
    nierozstrzygalne (ang. undecidable). Ponieważ w Coqu wszystkie
    funkcje są rekurencyjne, a dowody to programy, to możemy powyższą
    definicję rozumieć tak: zdanie jest rozstrzygalne, jeżeli istnieje
    funkcja rekurencyjna o przeciwdzidzinie [bool], która sprawdza, czy
    jest ono prawdziwe, czy fałszywe.

    Przykładami zdań, predykatów czy problemów rozstrzygalnych są:
    - sprawdzanie, czy lista jest niepusta
    - sprawdzanie, czy liczba naturalna jest parzysta
    - sprawdzanie, czy dwie liczby naturalne są równe *)

(** Przykładem problemów nierozstrzygalnych są:
    - dla funkcji [f g : nat -> nat] sprawdzenie, czy
      [forall n : nat, f n = g n] — jest to w ogólności niemożliwe,
      gdyż wymaga wykonania nieskończonej ilości porównań (co nie
      znaczy, że nie da się rozwiązać tego problemu dla niektórych
      funkcji)
    - sprawdzenie, czy słowo o nieskończonej długości jest palindromem *)

(** **** Ćwiczenie *)

Theorem eq_nat_dec :
  forall n m : nat, n = m \/ ~ n = m.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m'].
    left. trivial.
    right. inversion 1.
    right. inversion 1.
    destruct (IHn' m').
      left. subst. trivial.
      right. intro. inversion H0. subst. contradiction H. trivial.
Qed.
(* end hide *)

(** ** Techniczne apekty rozstrzygalności *)

(** Podsumowując powyższe rozważania, moglibyśmy stwierdzić: zdanie [P] jest
    rozstrzygalne, jeżeli istnieje term typu [P \/ ~ P]. Stwierdzenie takie
    nie zamyka jednak sprawy, gdyż bywa czasem mocno bezużyteczne.

    Żeby to zobrazować, spróbujmy użyć twierdzenia [eq_nat_dec] do napisania
    funkcji, która sprawdza, czy liczna naturalna [n] występuje na liście
    liczb naturalnych [l]: *)

Fail Fixpoint inb_nat (n : nat) (l : list nat) : bool :=
match l with
    | nil => false
    | cons h t =>
        match eq_nat_dec n h with
            | or_introl _ => true
            | _ => inb_nat n t
        end
end.

(** Coq nie akceptuje powyższego kodu, racząc nas informacją o błędzie: *)

(* Error:
   Incorrect elimination of "eq_nat_dec n h0" in the inductive type "or":
   the return type has sort "Type" while it should be "Prop".
   Elimination of an inductive object of sort Prop
   is not allowed on a predicate in sort Type
   because proofs can be eliminated only to build proofs. *)

(** Nasza porażka wynika z faktu, że do zdefiniowania funkcji, która
    jest programem (jej dziedzina i przeciwdziedzina są sortu [Type])
    próbowaliśmy użyć termu [eq_nat_dec n h], który jest dowodem
    (konkluzją [eq_nat_dec] jest równość, która jest sortu [Prop]).

    Mimo korespondencji Curry'ego-Howarda, która odpowiada za olbrzymie
    podobieństwo specyfikacji i zdań, programów i dowodów, sortu [Type]
    i sortu [Prop], są one rozróżniane i niesie to za sobą konsekwencje:
    podczas gdy programów możemy używać wszędzie, dowodów możemy używać
    jedynie do konstruowania innych dowodów.

    Praktycznie oznacza to, że mimo iż równość liczb naturalnych jest
    rozstrzygalna, pisząc program nie mamy możliwości jej rozstrzygania
    za pomocą [eq_nat_dec]. To właśnie miałem na myśli pisząc, że termy
    typu [P \/ ~ P] są mocno bezużyteczne.

    Uszy do góry: nie wszystko stracone! Jest to tylko drobna przeszkoda,
    którą bardzo łatwo ominąć: *)

Inductive sumbool (A B : Prop) : Type :=
    | left : A -> sumbool A B
    | right : B -> sumbool A B.

(** Typ [sumbool] jest niemal dokładną kopią [or], jednak nie żyje on
    w [Prop], lecz w [Type]. Ta drobna sztuczka, że termy typu
    [sumbool A B] formalnie są programami, mimo że ich naturalna
    interpretacja jest taka sama jak [or], a więc jako dowodu
    dysjunkcji. *)

(** **** Ćwiczenie *)

(** Udowodnij twierdzenie [eq_nat_dec'] o rozstrzygalności [=] na
    liczbach naturalnych. Użyj typu [sumbool]. Następnie napisz
    funkcję [inb_nat], która sprawdza, czy liczba naturalna [n]
    jest obecna na liście [l]. *)

(** * Typy hybrydowe *)

(** Ostatnim z typów istotnych z punktu widzenia silnych specyfikacji
    jest typ o wdzięcznej nazwie [sumor]. *)

Module sumor.

Inductive sumor (A : Type) (B : Prop) : Type :=
    | inleft : A -> sumor A B
    | inright : B -> sumor A B.

(** Jak sama nazwa wskazuje, [sumor] jest hybrydą sumy rozłącznej [sum]
    oraz dysjunkcji [or]. Możemy go interpretować jako typ, którego
    elementami są elementy [A] albo wymówki w stylu "nie mam elementu [A],
    ponieważ zachodzi zdanie [B]". [B] nie zależy od [A], a więc jest to
    zwykła suma (a nie suma zależna, czyli uogólnienie produktu). [sumor]
    żyje w [Type], a więc jest to specyfikacja i liczy się konkretna
    postać jego termów, a nie jedynie fakt ich istnienia. *)

(** **** Ćwiczenie ([pred']) *)

(** Zdefiniuj funkcję [pred'], która przypisuje liczbie naturalnej jej
    poprzednik. Poprzednikiem [0] nie powinno być [0]. Mogą przydać ci
    się typ [sumor] oraz sposób definiowania za pomocą taktyk, omówiony
    w podrozdziale dotyczącym sum zależnych. *)

(* begin hide *)
Definition pred' (n : nat) : sumor nat (n = 0) :=
match n with
    | 0 => inright _ _ eq_refl
    | S n' => inleft _ _ n'
end.
(* end hide *)

End sumor.

(** * Reflekcja w małej skali, czyli jak odbijać żeby się nie zmęczyć *)

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenSS : forall n : nat, even n -> even (S (S n)).

(*
Function evenb (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => evenb n'
end.

Lemma evenb_spec :
  forall n : nat, evenb n = true -> even n.
Proof.
  intros. functional induction evenb n.
    constructor.
    congruence.
    constructor. auto.
Qed.

Goal even 666.
Proof.
  apply evenb_spec. cbn. trivial.
Qed.

Print Unnamed_thm.
Print evenb_spec.
*)

(** Wrzucić tu przykład z porządkiem leksykograficznym z bloga Mondet.
    Dać też przykład z permutacjami? *)

(** * Poradnik hodowcy, czyli jak nie rozmnażać definicji *)

(** * Metoda encode-decode, czyli o rozwiązaywaniu problemów,
      które sami sobie tworzymy *)

(** Jak powiedział śp. Stefan Kisielewski: "teoria typów bohatersko
    zwalcza problemy nieznane w żadnej innej teorii". *)