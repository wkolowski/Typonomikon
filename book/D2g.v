(** * D2g: Rekursja ogólna [TODO] *)

Require Import Lia.

From Typonomikon Require Import D5.

(** * Jaka piękna katastrofa *)

(** W Coqu rekursja ogólna nie jest dozwolona. Powód jest banalny: prowadzi
    ona do sprzeczności. W celu zobrazowania spróbujmy zdefiniować za pomocą
    taktyk następującą funkcję rekurencyjną: *)

Fixpoint loop (u : unit) : False.
Proof.
  apply loop. assumption.
Fail Qed.
Abort.

(** Przyjrzyjmy się uważnie definicji funkcji [loop]. Mimo, że udało
    nam się ujrzeć znajomy napis "No more subgoals", próba użycia
    komendy [Qed] kończy się błędem.

    Fakt, że konstruujemy funkcję za pomocą taktyk, nie ma tu żadnego
    znaczenia, lecz służy jedynie lepszemu zobrazowaniu, dlaczego rekursja
    ogólna jest grzechem. Dokładnie to samo stałoby się, gdybyśmy próbowali
    zdefiniować [loop] ręcznie: *)

Fail Fixpoint loop (u : unit) : False := loop u.

(** Gdyby tak się nie stało, możliwe byłoby skonstruowanie dowodu [False]: *)

Fail Definition the_universe_explodes : False := loop tt.

(** Aby chronić nas przed tą katastrofą, Coq nakłada na rekurencję
    ograniczenie: argument główny wywołania rekurencyjnego musi być
    strukturalnym podtermem argumentu głównego obecnego wywołania.
    Innymi słowy, dozwolona jest jedynie rekursja strukturalna.

    To właśnie napisane jest w komunikacie o błędzie, który dostajemy,
    próbując przeforsować powyższe definicje: *)

(* Recursive definition of loop is ill-formed.
   In environment
   loop : unit -> False
   u : unit
   Recursive call to loop has principal argument equal to
   "u" instead of a subterm of "u".
   Recursive definition is: "fun u : unit => loop u". *)

(** Wywołanie rekurencyjne [loop] jest nielegalne, gdyż jego argumentem
    jest [u], podczas gdy powinien być nim jakiś podterm [u].

    Zanim jednak dowiemy się, czym jest argument główny, czym są podtermy
    i jak dokładnie Coq weryfikuje poprawność naszych definicji funkcji
    rekurencyjnych, wróćmy na chwilę do indukcji. Jak się zaraz okaże,
    nielegalność rekursji ogólnej wymusza również pewne ograniczenia w
    definicjach induktywnych. *)

(** **** Ćwiczenie *)

(** Ograniczenia nakładane przez Coqa sprawiają, że wszystkie napisane
    przez nas funkcje rekurencyjne muszą się kiedyś zatrzymać i zwrócić
    ostateczny wynik swojego działania. Tak więc nie możemy w Coqu pisać
    funkcji nieterminujących, czyli takich, które się nie zatrzymują.

    Rozważ bardzo interesujące pytanie filozoficzne: czy funkcje, które
    nigdy się nie zatrzymują (lub nie zatrzymują się tylko dla niektórych
    argumentów) mogą być w ogóle do czegokolwiek przydatne?

    Nie daj się wpuścić w maliny. *)

(** * Fantastyczny termination checker i jak go wyłączyć (TODO) *)

(** * Mafia paliwowa, czyli jak oszukiwać na paliwie *)

(** Rekursja dobrze ufundowana to sirius byznys, więc zanim się nią zajmiemy
    wypadałoby nauczyć się robić robotę na odwal, byle działało. Jakkolwiek
    nie brzmi to zbyt profesjonalnie, dobrze jest mieć tego typu narzędzie
    w zanadrzu, choćby w celu szybkiego prototypowania. Czasem zdarza się
    też, że tego typu luźne podejście do problemu jest jedynym możliwym, bo
    nikt nie wie, jak to zrobić porządnie.

    Narzędziem, o którym mowa, jest coś, co ja nazywam "rekursją po paliwie".
    Pozwala ona zasymulować definicję dowolnej funkcji o typie
    [A1 -> ... -> An -> B] (w tym nawet częściowej czy nieterminującej, co
    już samo w sobie jest ciekawe) za pomocą funkcji o typie
    [nat -> A1 -> ... -> An -> option B].

    Trik jest dość banalny: argument typu [nat] jest argumentem głównym,
    po którym robimy rekursję. Jest on naszym "paliwem", które spalamy
    przy każdym wywołaniu rekurencyjnym. Jeżeli paliwo się nam skończy,
    zwracamy [None]. Jeżeli jeszcze starcza paliwa, możemy zdefiniować
    funkcję tak jak zamierzaliśmy, ale mamy też obowiązki biurokratyczne
    związane ze sprawdzaniem, czy wyniki wywołań rekurencyjnych to [None]
    czy [Some].

    Coby za dużo nie godoć, przykład. *)

Require Import Nat.

(** Będą nam potrzebne notacje dla list oraz funkcja [even], która sprawdza,
    czy liczba naturalna jest parzysta. Będziemy chcieli zdefiniować funkcję
    Collatza. Gdyby Coq wspierał rekursję ogólną, jej definicja wyglądałaby
    tak: *)

Fail Fixpoint collatz (n : nat) : list nat :=
match n with
| 0 | 1 => [n]
| _ => n :: if even n then collatz (div2 n) else collatz (1 + 3 * n)
end.

(** Jest to bardzo wesoła funkcja. Przypadki bazowe to [0] i [1] - zwracamy
    wtedy po prostu listę z jednym elementem, odpowiednio [[0]] lub [[1]].
    Ciekawiej jest dla [n] większego od 1. [n] zostaje głową listy, zaś w
    kwestii ogona mamy dwa przypadki. Jeżeli [n] jest parzyste, to argumentem
    wywołania rekurencyjnego jest [n] podzielone przez [2], zaś w przeciwnym
    przypadku jest to [1 + 3 * n].

    Funkcja ta nie ma żadnego ukrytego celu. Została wymyślona dla zabawy,
    a przyświecające jej pytanie to: czy funkcja ta kończy pracę dla każdego
    argumentu, czy może jest jakiś, dla którego się ona zapętla?

    O ile funkcja jest prosta, o tyle odpowiedź jest bardzo skomplikowana i
    dotychczas nikt nie potrafił jej udzielić. Sprawdzono ręcznie (czyli za
    pomocą komputerów) bardzo dużo liczb i funkcja ta zawsze kończyła pracę,
    ale nikt nie umie udowodnić, że dzieje się tak dla wszystkich liczb. *)

Fixpoint collatz (fuel n : nat) : option (list nat) :=
match fuel with
| 0 => None
| S fuel' =>
  match n with
  | 0 | 1 => Some [n]
  | _ =>
    if even n
    then
      match collatz fuel' (div2 n) with
      | Some l => Some (n :: l)
      | None => None
      end
    else
      match collatz fuel' (1 + 3 * n) with
      | Some l => Some (n :: l)
      | None => None
      end
  end
end.

(** Definicja funkcji [collatz] za pomocą rekursji po paliwie wygląda dość
    groźnie, ale tak naprawdę jest całkiem banalna.

    Ponieważ oryginalna funkcja była typu [nat -> list nat], to ta nowa musi
    być typu [nat -> nat -> option (list nat)]. Tym razem zamiast dopasowywać
    [n] musimy dopasować paliwo, czyli [fuel]. Dla [0] zwracamy [None], a gdy
    zostało jeszcze trochę paliwa, przechodzimy do właściwej części definicji.
    W przypadkach bazowych zwracamy [[n]], ale  musimy zawinąć je w [Some]. W
    pozostałych przypadkach sprawdzamy, czy [n] jest parzyste, a następnie
    doklejamy odpowiedni ogon, ale musimy dopasować wywołania rekurencyjne
    żeby sprawdzić, czy zwracają one [None] czy [Some]. *)

Compute collatz 10 5.
(* ===> = Some [[5; 16; 8; 4; 2; 1]]
        : option (list nat) *)

Compute collatz 2 5.
(* ===> = None
        : option (list nat) *)

(** Zaimplementowana za pomocą rekursji po paliwie funkcja oblicza się bez
    problemu, oczywiście o ile wystarczy jej paliwa. W powyższych przykładach
    [10] jednostek paliwa wystarcza, by obliczyć wynik dla [5], ale [2]
    jednostki paliwa to za mało. Jak więc widać, ilość potrzebnego paliwa
    zależy od konkretnej wartości na wejściu.

    Interpretacja tego, czym tak naprawdę jest paliwo, nie jest zbyt
    trudna. Jest to maksymalna głębokość rekursji, na jaką może pozwolić
    sobie funkcja. Czym jest głębokość rekursji? Możemy wyobrazić sobie
    drzewo, którego korzeniem jest obecne wywołanie, a poddrzewami są
    drzewa dla wywołań rekurencyjnych. Głębokość rekursji jest po prostu
    głębokością (czyli wysokością) takiego drzewa.

    W przypadku funkcji [collatz] głębokość rekursji jest równa długości
    zwróconej listy (gdy funkcja zwraca [Some]) lub większa niż ilość
    paliwa (gdy funkcja zwraca [None]).

    Powyższe rozważania prowadzą nas do techniki, która pozwala z funkcji
    zrobionej rekursją po paliwie zrobić normalną, pełnoprawną funkcję.
    Wystarczy znaleźć "funkcję tankującą"
    [fill_tank : A1 -> ... -> An -> nat], która oblicza, ile paliwa
    potrzeba dla danych argumentów wejściowych. Funkcja ta powinna mieć
    tę własność, że gdy nalejemy tyle paliwa, ile ona każe (lub więcej),
    zawsze w wyniku dostaniemy [Some].

    Trudnością, z którą nikt dotychczas w przypadku funkcji [collatz] nie
    potrafił się uporać, jest właśnie znalezienie funkcji tankującej. Jak
    więc widać, rekursja po paliwie nie zawsze jest fuszerką czy środkiem
    prototypowania, lecz czasem bywa faktycznie przydatna do reprezentowania
    funkcji, których inaczej zaimplementować się nie da. *)

(** **** Ćwiczenie *)

(** Zdefiniuj za pomocą rekursji po paliwie funkcję [divFuel], która jest
    implementacją dzielenia (takiego zwykłego, a nie sprytnego jak ostatnio,
    tzn. [divFuel fuel n 0] jest niezdefiniowane). *)

(* begin hide *)
Fixpoint divFuel (fuel n m : nat) : option nat :=
match fuel with
| 0 => None
| S fuel' =>
  if ltb n m
  then Some 0
  else
    match divFuel fuel' (n - m) m with
    | Some r => Some (S r)
    | None => None
    end
end.
(* end hide *)

(** **** Ćwiczenie *)

(** Sporą zaletą rekursji po paliwie jest to, że definicje zrobionych za
    jej pomocą funkcji są jasne i czytelne (przynajmniej w porównaniu do
    rekursji dobrze ufundowanej, o czym już niedługo się przekonamy). To
    z kolei pozwala nam w dość łatwy sposób dowodzić interesujących nas
    właściwości tych funkcji.

    Udowodnij kilka oczywistych właściwości dzielenia:
    - [divFuel ? n 1 = Some n], tzn. [n/1 = n]. Ile potrzeba paliwa?
    - [divFuel ? n n = Some 1], tzn. [n/n = 1]. Ile potrzeba paliwa?
    - przy dzieleniu przez [0] nigdy nie starcza paliwa. *)

(* begin hide *)
Require Import Arith.

Lemma divFuel_1 :
  forall n : nat,
    divFuel (S n) n 1 = Some n.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite Nat.sub_0_r. cbn in IHn'. destruct n' as [| n''].
      cbn. reflexivity.
      rewrite IHn'. reflexivity.
Qed.

Lemma divFuel_0 :
  forall fuel n : nat,
    divFuel fuel n 0 = None.
Proof.
  induction fuel as [| fuel']; cbn; intro.
    reflexivity.
    rewrite IHfuel'. reflexivity.
Qed.

Lemma divFuel_n :
  forall n : nat,
    divFuel 2 (S n) (S n) = Some 1.
Proof.
  intro n. unfold divFuel.
  rewrite Nat.ltb_irrefl.
  rewrite Nat.sub_diag.
  cbn. reflexivity.
Qed.

(* end hide *)

(** **** Ćwiczenie (lemat o tankowaniu) *)

(** Pokaż, że jeżeli wystarcza nam paliwa do obliczenia wyniku, ale
    zatankujemy jeszcze trochę, to dalej będzie nam wystarczać.
    Wniosek: tankującemu nie dzieje się krzywda. *)

(* begin hide *)

(* TODO *)

Lemma tank_filling_lemma :
  forall fuel n m r : nat,
      divFuel fuel n (S m) = Some r -> divFuel (S fuel) n (S m) = Some r.
Proof.
  induction fuel as [| fuel']; cbn.
    inversion 1.
    destruct m as [| m']; intros.
      destruct (n <=? 0).
        assumption.
        destruct n; cbn.
          cbn in H. destruct fuel'; cbn in H.
            inversion H.
            assumption.
          destruct n; cbn.
            destruct fuel'; cbn in H.
              inversion H.
              assumption.
            cbn in H. rewrite Nat.sub_0_r. admit.
      destruct (n <=? S m').
        assumption.
        cbn in *.
Abort.

Lemma tank_filling_lemma :
  forall fuel fuel',
    fuel <= fuel' -> forall n m r : nat,
      divFuel fuel n m = Some r -> divFuel fuel' n m = Some r.
Proof.
  intros fuel fuel'.
  induction 1 as [| fuel' H IH]; intros.
    assumption.
    cbn. destruct m; cbn.
      rewrite divFuel_0 in H0. inversion H0.
      destruct fuel; cbn in H0.
        inversion H0.
        case_eq (n <=? m); intros.
          rewrite H1 in H0. assumption.
          case_eq (divFuel fuel (n - S m) (S m)); intros.
            rewrite H2, H1 in H0. cbn in IH.
Abort.

(* end hide *)

(** **** Ćwiczenie *)

(** Udowodnij, że funkcji [collatz] dla wejść o postaci [pow 2 n] (czyli
    potęg dwójki) wystarczy [S n] jednostek paliwa.

    Uwaga (trochę złośliwa): jeśli napotkasz trudności w trakcie dowodzenia
    (a moje uwagi przecież nie biorą się znikąd), to pamiętaj, że mają one
    charakter arytmetyczny, tzn. są związane z użyciem w definicji funkcji
    takich jak [pow] czy [div2], nie są zaś spowodowane jakimiś problemami
    z samą techniką, jaką jest rekursja po paliwie. *)

(* begin hide *)

Lemma pow2_n_SS :
  forall n : nat, exists m : nat, pow 2 (S n) = S (S m).
Proof.
  induction n as [| n']; cbn.
    exists 0. reflexivity.
    destruct IHn' as [m IH]. cbn in IH. rewrite IH. cbn.
      exists (m + (S (S (m + 0)))). reflexivity.
Qed.

Lemma even_pow_2 :
  forall n : nat,
    even (2 ^ S n) = true.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    {
      cbn in IHn'.
      rewrite Nat.even_add,
              IHn',
              Nat.add_assoc, Nat.even_add, <- Nat.add_assoc,
              IHn'.
      cbn.
      reflexivity.
    }
Qed.

Arguments pow _ : simpl never.

Lemma div2_pow_2 :
  forall n : nat,
    div2 (2 ^ S n) = 2 ^ n.
Proof.
  intros. apply Nat.div2_double.
Qed.

Lemma collatz_pow2 :
  forall n : nat,
    exists (h : nat) (t : list nat),
      collatz (S n) (pow 2 n) = Some (h :: t).
Proof.
  cbn.
  induction n as [ | | n'] using nat_ind_2.
    compute. exists 1, []. reflexivity.
    compute. exists 2, [1]. reflexivity.
    destruct (pow2_n_SS (S n')) as [m eq]. rewrite eq, <- eq.
      rewrite even_pow_2, div2_pow_2. cbn.
        destruct (pow2_n_SS n') as [m' eq']. rewrite eq', <- eq'.
          rewrite even_pow_2, div2_pow_2.
            destruct IHn' as (h & t & IH).
              exists (2 ^ S (S n')), (2 ^ S n' :: h :: t).
                rewrite IH. reflexivity.
Qed.

(* end hide *)

(** * Monada nieterminacji *)

(** Da się zrobić kombinator punktu stałego i zamknąć go w monadę/modalność
    tak, żeby sprzeczność nie wyciekła na zewnątrz i żeby wszystko ładnie się
    liczyło, jeżeli wynik nie jest bottomem? TAK! *)

Module SafeFix.

Private Inductive Div (A : Type) : Type :=
| pure : A -> Div A.

Arguments pure {A} _.

Definition divmap {A B : Type} (f : A -> B) (x : Div A) : Div B :=
match x with
| pure a => pure (f a)
end.

Definition divbind {A B : Type} (x : Div A) (f : A -> Div B) : Div B :=
match x with
| pure a => f a
end.

Definition divjoin {A : Type} (x : Div (Div A)) : Div A :=
match x with
| pure (pure a) => pure a
end.

(** * Kombinator punktu stałego *)

Unset Guard Checking.
Fixpoint wutfix
  (u : unit) {A B : Type} (f : (A -> Div B) -> (A -> Div B)) (x : A) {struct u} : Div B :=
    f (wutfix u f) x.

Definition efix {A B : Type} (f : (A -> Div B) -> (A -> Div B)) (x : A) : Div B :=
  wutfix tt f x.
Set Guard Checking.

Arguments efix {A B} f x / : simpl nomatch.

Lemma unfix :
  forall {A B : Type} (f : (A -> Div B) -> (A -> Div B)) (x : A),
    efix f x = f (efix f) x.
Proof.
Admitted.

(** * Terminacja, nieterminacja *)

Private Inductive Terminates {A : Type} : Div A -> Prop :=
| terminates : forall x : A, Terminates (pure x).

Definition extract {A : Type} {x : Div A} (t : Terminates x) : A :=
match x with
| pure a => a
end.

Lemma Terminates_pure :
  forall {A : Type} (x : A),
    Terminates (pure x).
Proof.
  constructor.
Qed.

Lemma Terminates_divmap :
  forall {A B : Type} (f : A -> B) {x : Div A},
    Terminates x -> Terminates (divmap f x).
Proof.
  destruct 1; cbn; constructor.
Qed.

Lemma Terminates_divbind :
  forall {A B : Type} (f : A -> Div B) (x : Div A),
    Terminates x -> (forall x : A, Terminates (f x)) -> Terminates (divbind x f).
Proof.
  intros A B f x [] H. cbn. apply H.
Qed.

Private Inductive EvaluatesTo {A : Type} : Div A -> A -> Prop :=
| EvaluatesTo_pure : forall x : A, EvaluatesTo (pure x) x.

Definition eval {A : Type} {x : Div A} {y : A} (t : EvaluatesTo x y) : A :=
match x with
| pure a => a
end.

Lemma EvaluatesTo_eval :
  forall {A : Type} (da : Div A) (a : A) (e : EvaluatesTo da a),
    eval e = a.
Proof.
  now destruct e.
Qed.

Lemma EvaluatesTo_divmap :
  forall {A B : Type} (f : A -> B) {da : Div A} {a : A},
    EvaluatesTo da a -> EvaluatesTo (divmap f da) (f a).
Proof.
  now destruct 1; cbn.
Qed.

Lemma EvaluatesTo_det :
  forall {A : Type} {da : Div A} {a1 a2 : A},
    EvaluatesTo da a1 -> EvaluatesTo da a2 -> a1 = a2.
Proof.
  now do 2 inversion 1.
Qed.

Lemma Terminates_EvaluatesTo :
  forall {A : Type} (da : Div A) (a : A),
    EvaluatesTo da a -> Terminates da.
Proof.
  inversion 1; subst.
  now constructor.
Qed.

Lemma EvaluatesTo_extract :
  forall {A : Type} (da : Div A) (t : Terminates da),
    EvaluatesTo da (extract t).
Proof.
  destruct t; cbn.
  now constructor.
Qed.

End SafeFix.

(** * Przykłady *)

(** ** Algorytm Euklidesa *)

Import SafeFix.

Definition euclid (n m : nat) : Div nat :=
  efix (fun euclid '(n, m) =>
    match n with
    | 0 => pure m
    | _ => euclid (PeanoNat.Nat.modulo m n, n)
    end) (n, m).

Time Compute euclid (2 * 3 * 5 * 7) (2 * 7 * 11).

Lemma euclid_eq :
  forall n m : nat,
    euclid n m
      =
    match n with
    | 0 => pure m
    | _ => euclid (PeanoNat.Nat.modulo m n) n
    end.
Proof.
  intros.
  unfold euclid.
  rewrite unfix.
  reflexivity.
Defined.

Lemma Terminates_euclid :
  forall n m : nat, Terminates (euclid n m).
Proof.
  apply (well_founded_induction Wf_nat.lt_wf (fun n => forall m, Terminates (euclid n m))).
  intros n IH m.
  rewrite euclid_eq.
  destruct n as [| n'].
  - apply Terminates_pure.
  - apply IH. apply PeanoNat.Nat.mod_upper_bound. inversion 1.
Defined.

Definition euclid' (n m : nat) : nat :=
  extract (Terminates_euclid n m).

Compute euclid' 5 2.

Definition div (n m : nat) : Div nat :=
  efix (fun div '(n, m) =>
    if Nat.ltb n m
    then pure 0
    else divmap (plus 1) (div (n - m, m)))
  (n, m).

Compute div 51 12.

(** ** Dzielenie *)

Lemma div_eq :
  forall n m : nat,
    div n m
      =
    if Nat.ltb n m
    then pure 0
    else divmap (plus 1) (div (n - m) m).
(* begin hide *)
Proof.
  intros. unfold div. rewrite unfix. reflexivity.
Qed.
(* end hide *)

Lemma Terminates_div :
  forall n m : nat, 0 < m -> Terminates (div n m).
(* begin hide *)
Proof.
  apply (well_founded_induction Wf_nat.lt_wf
          (fun n => forall m, 0 < m -> Terminates (div n m))).
  intros n IH m Hlt.
  rewrite div_eq.
  destruct (Nat.ltb n m) eqn: Hltb.
  - apply Terminates_pure.
  - apply Terminates_divmap. apply IH.
    + apply PeanoNat.Nat.ltb_ge in Hltb. lia.
    + apply PeanoNat.Nat.ltb_nlt in Hltb. lia.
Qed.
(* end hide *)

Definition div' (n m : nat) (H : 0 < m) : nat :=
  extract (Terminates_div n m H).

(** ** Głupia funkcja... *)

Definition stupid (n : nat) : Div nat :=
  efix (fun stupid n => divmap (plus 1) (stupid (1 + n))) n.

Lemma stupid_eq :
  forall n : nat,
    stupid n
      =
    divmap (plus 1) (stupid (1 + n)).
Proof.
  intros. unfold stupid. rewrite unfix. reflexivity.
Qed.

Lemma nat_bounded_stupid :
  forall (f : nat -> nat),
    (forall n : nat, f n = 1 + f (1 + n)) ->
      forall n m : nat, n <= f m.
Proof.
  induction n as [| n']; cbn; intros m.
  - lia.
  - rewrite H. apply le_n_S. apply IHn'.
Qed.

Lemma EvaluatesTo_stupid :
  (forall n : nat, {m : nat | EvaluatesTo (stupid n) m}) -> False.
Proof.
  intros H.
  pose (e := fun n => eval (proj2_sig (H n))).
  assert (forall n : nat, n <= e 0).
  {
    intros n. apply nat_bounded_stupid.
    intros k. unfold e.
    rewrite !EvaluatesTo_eval.
    destruct (H k) eqn: I, (H (1 + k)) eqn: J; cbn.
    eapply EvaluatesTo_det; [eassumption |].
    rewrite stupid_eq.
    now apply EvaluatesTo_divmap.
  }
  specialize (H0 (1 + e 0)).
  lia.
Qed.

Lemma Terminates_stupid :
  ~ (forall n : nat, Terminates (stupid n)).
Proof.
  intros H.
  apply EvaluatesTo_stupid.
  intros n.
  exists (extract (H n)).
  now apply EvaluatesTo_extract.
Qed.

(** ** Funkcja Ackermanna *)

Definition ack' (n m : nat) : Div nat :=
  efix (fun ack' '(n, m) =>
    match n, m with
    | 0, _ => pure (1 + m)
    | Datatypes.S n', 0 => ack' (n', 1)
    | Datatypes.S n', Datatypes.S m' => divbind (ack' (n, m')) (fun r => ack' (n', r))
    end) (n, m).

Lemma ack'_eq :
  forall n m : nat,
    ack' n m
      =
    match n, m with
    | 0, _ => pure (1 + m)
    | Datatypes.S n', 0 => ack' n' 1
    | Datatypes.S n', Datatypes.S m' => divbind (ack' n m') (fun r => ack' n' r)
    end.
(* begin hide *)
Proof.
  intros. unfold ack'. rewrite unfix. reflexivity.
Qed.
(* end hide *)

Lemma Terminates_ack' :
  forall n m : nat,
    Terminates (ack' n m).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros m.
  - apply Terminates_pure.
  - induction m as [| m'].
    + rewrite ack'_eq. apply IHn'.
    + rewrite ack'_eq. apply Terminates_divbind.
      * assumption.
      * assumption.
Qed.
(* end hide *)

Definition ack (n m : nat) : nat :=
  extract (Terminates_ack' n m).

Definition stupider (n : nat) : Div nat :=
  efix (fun stupid n => stupid (1 + n)) n.

Lemma stupider_eq :
  forall n : nat,
    stupider n = stupider (1 + n).
Proof.
  intros. unfold stupider. rewrite unfix. reflexivity.
Qed.