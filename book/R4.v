(** * R4: Spis przydatnych taktyk *)

(* begin hide *)
(** TODO:
    - [evar]
    - [compare]
    - [simplify_eq]
    - [induction], [inversion], [destruct]
    - [dependent induction], [dependent inversion], [dependent destruction]
    - [dependent rewrite]
    - [easy], [elim], [elimtype], [enough]
*)
(* end hide *)

(** Stare powiedzenie głosi: nie wymyślaj koła na nowo. Aby uczynić zadość
    duchom przodków, którzy je wymyślili, w niniejszym rozdziale zapoznamy
    się z różnymi przydatnymi taktykami, które prędzej czy później i tak
    sami byśmy wymyślili, gdyby zaszła taka potrzeba.

    Aby jednak nie popaść w inny grzech i nie posługiwać się czarami, których
    nie rozumiemy, w ramach ćwiczeń część z poniżej omówionych taktyk będziemy
    mogli zaimplementować jako ćwiczenie.

    Omówimy kolejno:
    - drobne taktyki służące głównie do kontrolowania tego, co dzieje się
      w kontekście
    - "średnie" taktyki, wcielające w życie pewien konkretny sposób
      rozumowania
    - procedury decyzyjne, które potrafią zupełnie same rozwiązać cele
      należące do pewnej konkretnej klasy, np. cele dotyczące funkcji
      boolowskich albo nierówności liniowych na liczbach całkowitych *)

(** Powyższa klasyfikacja jest jedynie przybliżona i nie należy brać jej zbyt
    poważnie.

    Uwaga: przykłady użycia taktyk, których reimplementacja będzie
    ćwiczeniem, zostały połączone z testami w ćwiczeniach żeby nie pisać dwa
    razy tego samego. *)

(** * Drobne taktyki *)

(** ** [clear] *)

Goal
  forall x y : nat, x = y -> y = x -> False.
Proof.
  intros. clear H H0.
Restart.
  intros. Fail clear x. Fail clear wut.
Restart.
  intros. clear dependent x.
Restart.
  intros. clear.
Restart.
  intros.
  pose (z := 42).
  clearbody z.
Abort.

(** [clear] to niesamowicie użyteczna taktyka, dzięki której możemy zrobić
    porządek w kontekście. Można używać jej na nastepujące sposoby:
    - [clear x] usuwa [x] z kontekstu. Jeżeli [x] nie ma w kontekście lub są
      w nim jakieś rzeczy zależne od [x], taktyka zawodzi. Można usunąć wiele
      rzeczy na raz: [clear x_1 ... x_N].
    - [clear -x] usuwa z kontekstu wszystko poza [x].
    - [clear dependent x] usuwa z kontekstu [x] i wszystkie rzeczy, które od
      niego zależą. Taktyka ta zawodzi jedynie gdy [x] nie ma w kontekście.
    - [clear] usuwa z kontekstu absolutnie wszystko. Serdecznie nie polecam.
    - [clearbody x] usuwa definicję [x] (jeżeli [x] jakąś posiada). *)

(** **** Ćwiczenie (tru) *)

(** Napisz taktykę [tru], która czyści kontekst z dowodów na [True] oraz
    potrafi udowodnić cel [True].

    Dla przykładu, taktyka ta powinna przekształcać kontekst
    [a, b, c : True, p : P |- _] w [p : P |- _].

    Wskazówka: przydatna może być taktyka [clear]. *)

(* begin hide *)
Ltac tru := intros; repeat
match goal with
    | H : True |- _ => clear H
end; trivial.
(* end hide *)

Section tru.

Example tru_0 :
  forall P : Prop, True -> True -> True -> P.
Proof.
  tru. (* Kontekst: [P : Prop |- P] *)
Abort.

Example tru_1 : True.
Proof. tru. Qed.

End tru.

(** **** Ćwiczenie (satans_neighbour_not_even) *)

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenSS : forall n : nat, even n -> even (S (S n)).

(** Napisz taktykę [even], która potrafi udowodnić poniższy cel. *)

(* begin hide *)
Ltac even := unfold not; intros; repeat
match goal with
    | H : even _ |- _ => inversion H; subst; clear H
end.
(* end hide *)

Theorem satans_neighbour_not_even : ~ even 667.
(* begin hide *)
(* Proof. even. Qed. *)
Abort.
(* end hide *)

(** ** [fold] *)

(** [fold] to taktyka służąca do zwijania definicji. Jej działanie jest
    odwrotne do działania taktyki [unfold]. Niestety, z nieznanych mi
    bliżej powodów bardzo często jest ona nieskuteczna. *)

(** **** Ćwiczenie (my_fold) *)

(** Napisz taktykę [my_fold x], która działa tak jak [fold x], tj. zastępuje
    we wszystkich miejscach w celu term powstały po rozwinięciu [x] przez [x].

    Wskazówka: zapoznaj się z konstruktem [eval] — zajrzyj do 9 rozdziału
    manuala. *)

(* begin hide *)
Ltac my_fold x :=
  let body := eval unfold x in x in
match goal with
    | |- context [body] => change body with x
end.
(* end hide *)

Example fold_0 :
  forall n m : nat, n + m = m + n.
Proof.
  intros. unfold plus. fold plus.
Restart.
  intros. unfold plus. my_fold plus.
Abort.

(** ** [move] (TODO) *)

(** ** [pose] i [remember] *)

Goal 2 + 2 = 4.
Proof.
  intros.
  pose (a := 2 + 2).
  remember (2 + 2) as b.
Abort.

(** Taktyka [pose (x := t)] dodaje do kontekstu zmienną [x] (pod warunkiem,
    że nazwa ta nie jest zajęta), która zostaje zdefiniowana za pomocą termu
    [t].

    Taktyka [remember t as x] zastępuje wszystkie wystąpienia termu [t]
    w kontekście zmienną [x] (pod warunkiem, że nazwa ta nie jest zajęta) i
    dodaje do kontekstu równanie postaci [x = t].

    W powyższym przykładzie działają one następująco: [pose (a := 2 + 2)]
    dodaje do kontekstu wiązanie [a := 2 + 2], zaś [remember (2 + 2) as b]
    dodaje do kontekstu równanie [Heqb : b = 2 + 2] i zastępuje przez [b]
    wszystkie wystąpienia [2 + 2] — także to w definicji [a].

    Taktyki te przydają się w tak wielu różnych sytuacjach, że nie ma co
    próbować ich tu wymieniać. Użyjesz ich jeszcze nie raz. *)

(** **** Ćwiczenie (set) *)

(** Taktyki te są jedynie wariantami bardziej ogólnej taktyki [set].
    Przeczytaj jej dokumentację w manualu. *)

(** ** [rename] *)

Goal forall P : Prop, P -> P.
Proof.
  intros. rename H into wut.
Abort.

(** [rename x into y] zmienia nazwę [x] na [y] lub zawodzi, gdy [x] nie ma
    w kontekście albo nazwa [y] jest już zajęta *)

(** **** Ćwiczenie (satans_neighbour_not_even') *)

(** Napisz taktykę [even'], która potrafi udowodnić poniższy cel. Nie używaj
    [match]a, a jedynie kombinatora [repeat]. *)

Theorem satans_neighbour_not_even' : ~ even 667.
(* begin hide *)
(* Proof.
  intro.
  Time repeat (inversion H; clear H H0; rename H1 into H; try (clear n0)).
Qed. *)
Abort.
(* end hide *)

(** ** [admit] *)

Module admit.

Lemma forgery :
  forall P Q : Prop, P -> Q /\ P.
Proof.
  intros. split.
    admit.
    assumption.
Admitted.

Print forgery.
(* ===> *** [[ forgery : forall P : Prop, P -> ~ P /\ P ]] *)

End admit.

(** [admit] to taktyka-oszustwo, która rozwiązuje dowolny cel. Nie jest ona
    rzecz jasna wszechwiedząca i przez to rozwiązanego za jej pomocą celu
    nie można zapisać za pomocą komend [Qed] ani [Defined], a jedynie za
    pomocą komendy [Admitted], która oszukańczo udowodnione twierdzenie
    przekształca w aksjomat.

    W CoqIDE oszustwo jest dobrze widoczne, gdyż zarówno taktyka [admit]
    jak i komenda [Admitted] podświetlają się na żółto, a nie na zielono,
    tak jak prawdziwe dowody. Wyświetlenie [Print]em dowodu zakończonego
    komendą [Admitted] również pokazuje, że ma on status aksjomatu.

    Na koniec zauważmy, że komendy [Admitted] możemy użyć również bez
    wczesniejszego użycia taktyki [admit]. Różnica między tymi dwoma bytami
    jest taka, że taktyka [admit] służy do "udowodnienia" pojedynczego celu,
    a komenda [Admitted] — całego twierdzenia. *)

(** * Średnie taktyki *)

(** ** [case_eq] *)

(** [case_eq] to taktyka podobna do taktyki [destruct], ale nieco mądrzejsza,
    gdyż nie zdarza jej się "zapominać", jaka była struktura rozbitego przez
    nią termu. *)

Goal
  forall n : nat, n + n = 42.
Proof.
  intros. destruct (n + n).
Restart.
  intros. case_eq (n + n); intro.
Abort.

(** Różnice między [destruct] i [case_eq] dobrze ilustruje powyższy przykład.
    [destruct] nadaje się jedynie do rozbijania termów, które są zmiennymi.
    Jeżeli rozbijemy coś, co nie jest zmienną (np. term [n + n]), to utracimy
    część informacji na jego temat. [case_eq] potrafi rozbijać dowolne termy,
    gdyż poza samym rozbiciem dodaje też do celu dodatkową hipotezę, która
    zawiera równanie "pamiętające" informacje o rozbitym termie, o których
    zwykły [destruct] zapomina. *)

(** **** Ćwiczenie *)

(** Napisz taktykę [my_case_eq t Heq], która działa tak jak [case_eq t], ale
    nie dodaje równania jako hipotezę na początku celu, tylko bezpośrednio
    do kontekstu i nazywa je [Heq]. Użyj taktyk [remember] oraz [destruct]. *)

(* begin hide *)
Ltac my_case_eq t Heq :=
  let x := fresh "x" in remember t as x;
  match goal with
      | H : x = t |- _ => symmetry in H; rename H into Heq
  end;
  destruct x.
(* end hide *)

Goal
  forall n : nat, n + n = 42.
Proof.
  intros. destruct (n + n).
Restart.
  intros. case_eq (n + n); intro.
Restart.
  intros. my_case_eq (n + n) H.
Abort.

(** ** [contradiction] *)

(** [contradiction] to taktyka, która wprowadza do kontekstu wszystko co się
    da, a potem próbuje znaleźć sprzeczność. Potrafi rozpoznawać hipotezy
    takie jak [False], [x <> x], [~ True]. Potrafi też znaleźć dwie hipotezy,
    które są ze sobą ewidentnie sprzeczne, np. [P] oraz [~ P]. Nie potrafi
    jednak wykrywać lepiej ukrytych sprzeczności, np. nie jest w stanie
    odróżnić [true] od [false]. *)

(** **** Ćwiczenie (my_contradiction) *)

(** Napisz taktykę [my_contradiction], która działa tak jak standardowa
    taktyka [contradiction], a do tego jest w stanie udowodnić dowolny
    cel, jeżeli w kontekście jest hipoteza postaci [true = false] lub
    [false = true]. *)

(* begin hide *)
Ltac my_contradiction := intros;
match goal with
    | H : False |- _ => destruct H
    | H : ~ True |- _ => destruct (H I)
    | H : ?x <> ?x |- _ => destruct (H eq_refl)
    | H : ~ ?P, H' : ?P |- _ => destruct (H H')
    | H : true = false |- _ => inversion H
    | H : false = true |- _ => inversion H
end.
(* end hide *)

Section my_contradiction.

Example my_contradiction_0 :
  forall P : Prop, False -> P.
Proof.
  contradiction.
Restart.
  my_contradiction.
Qed.

Example my_contradiction_1 :
  forall P : Prop, ~ True -> P.
Proof.
  contradiction.
Restart.
  my_contradiction.
Qed.

Example my_contradiction_2 :
  forall (P : Prop) (n : nat), n <> n -> P.
Proof.
  contradiction.
Restart.
  my_contradiction.
Qed.

Example my_contradiction_3 :
  forall P Q : Prop, P -> ~ P -> Q.
Proof.
  contradiction.
Restart.
  my_contradiction.
Qed.

Example my_contradiction_4 :
  forall P : Prop, true = false -> P.
Proof.
  try contradiction.
Restart.
  my_contradiction.
Qed.

Example my_contradiction_5 :
  forall P : Prop, false = true -> P.
Proof.
  try contradiction.
Restart.
  my_contradiction.
Qed.

End my_contradiction.

(** **** Ćwiczenie (taktyki dla sprzeczności) *)

(** Innymi taktykami, które mogą przydać się przy rozumowaniach przez
    sprowadzenie do sprzeczności, są [absurd], [contradict] i [exfalso].
    Przeczytaj ich opisy w manualu i zbadaj ich działanie. *)

(** ** [constructor] *)

Example constructor_0 :
  forall P Q : Prop, P -> Q \/ P.
Proof.
  intros. constructor 2. assumption.
Restart.
  intros. constructor.
Restart.
  intros. constructor; assumption.
Qed.

(** [constructor] to taktyka ułatwiająca aplikowanie konstruktorów typów
    induktywnych. Jeżeli aktualnym celem jest [T], to taktyka [constructor i]
    jest równoważna wywołaniu jego i-tego konstruktora, gdzie porządek
    konstruktorów jest taki jak w definicji typu. *)

Print or.
(* ===> Inductive or (A B : Prop) : Prop :=
            or_introl : A -> A \/ B | or_intror : B -> A \/ B *)

(** W powyższym przykładzie [constructor 2] działa tak jak [apply or_intror]
    (czyli tak samo jak taktyka [right]), gdyż w definicji spójnika [or]
    konstruktor [or_intror] występuje jako drugi (licząc od góry).

    Użycie taktyki [constructor] bez liczby oznacza zaaplikowanie pierwszego
    konstruktora, który pasuje do celu, przy czym taktyka ta może wyzwalać
    backtracking. W drugim przykładzie powyżej [constructor] działa jak
    [apply or_intro] (czyli jak taktyka [left]), gdyż zaaplikowanie tego
    konstruktora nie zawodzi.

    W trzecim przykładzie [constructor; assumption] działa tak: najpierw
    aplikowany jest konstruktor [or_introl], ale wtedy [assumption] zawodzi,
    więc następuje nawrót i aplikowany jest konstruktor [or_intror], a wtedy
    [assumption] rozwiązuje cel. *)

(** **** Ćwiczenie (taktyki dla konstruktorów) *)

(** Jaki jest związek taktyki [constructor] z taktykami [split], [left],
    [right] i [exists]? *)

(** ** [decompose] *)

Example decompose_0 :
  forall P Q R S : nat -> Prop,
    (exists n : nat, P n) /\ (exists n : nat, Q n) /\
    (exists n : nat, R n) /\ (exists n : nat, S n) ->
      exists n : nat, P n \/ Q n \/ R n \/ S n.
Proof.
  intros. decompose [and ex] H. clear H. exists x. left. assumption.
Qed.

(** [decompose] to bardzo użyteczna taktyka, która potrafi za jednym zamachem
    rozbić bardzo skomplikowane hipotezy. [decompose [t_1 ... t_n] H] rozbija
    rekurencyjnie hipotezę [H] tak długo, jak jej typem jest jeden z typów
    [t_i]. W powyższym przykładzie [decompose [and ex] H] najpierw rozbija [H],
    gdyż jest ona koniunkcją, a następnie rozbija powstałe z niej hipotezy,
    gdyż są one kwantyfikacjami egzystencjalnymi ("exists" jest notacją dla
    [ex]). [decompose] nie usuwa z kontekstu hipotezy, na której działa, więc
    często następuje po niej taktyka [clear]. *)

(** ** [intros] *)

(** Dotychczas używałeś taktyk [intro] i [intros] jedynie z nazwami lub
    wzorcami do rozbijania elementów typów induktywnych. Taktyki te potrafią
    jednak dużo więcej. *)

Example intros_0 :
  forall P Q R S : Prop, P /\ Q /\ R -> S.
Proof.
  intros P Q R S [p [q r]].
Restart.
  intros ? ?P Q R. intros (p, (p0, q)).
Restart.
  intros *.
Restart.
  intros A B **.
Restart.
  intros * _.
Restart.
  Fail intros _.
Abort.

(** Pierwszy przykład to standardowe użycie [intros] — wprowadzamy cztery
    zmienne, która nazywamy kolejno [P], [Q], [R] i [S], po czym wprowadzamy
    bezimienną hipotezę typu [P /\ Q /\ R], która natychmiast rozbijamy za
    pomocą wzorca [p [q r]].

    W kolejnym przykładzie mamy już nowości: wzorzec [?] służy do nadania
    zmiennej domyślnej nazwy. W naszym przypadku wprowadzone do kontekstu
    zdanie zostaje nazwane [P], gdyż taką nazwę nosi w kwantyfikatorze,
    gdy jest jeszcze w celu.

    Wzorzec [?P] służy do nadania zmiennej domyślnej nazwy zaczynając się
    od tego, co następuje po znaku [?]. W naszym przypadku do konteksu
    wprowadzona zostaje zmienna [P0], gdyż żądamy nazwy zaczynającej się
    od "P", ale samo "P" jest już zajęte. Widzimy też wzorzec [(p, (p0, q))],
    który służy do rozbicia hipotezy. Wzorce tego rodzaju działają tak samo
    jak wzorce w kwadratowych nawiasach, ale możemy używać ich tylko na
    elementach typu induktywnego z jednym konstruktorem.

    Wzorzec [*] wprowadza do kontekstu wszystkie zmienne kwantyfikowane
    uniwersalnie i zatrzymuje sie na pierwszej nie-zależnej hipotezie. W
    naszym przykładzie uniwersalnie kwantyfikowane są [P], [Q], [R] i [S],
    więc zostają wprowadzane, ale [P /\ Q /\ R] nie jest już kwantyfikowane
    uniwersalnie — jest przesłanką implikacji — więc nie zostaje wprowadzone.

    Wzorzec [**] wprowadza do kontekstu wszystko. Wobec tego [intros **] jest
    synonimem [intros]. Mimo tego nie jest on bezużyteczny — możemy użyć go
    po innych wzorcach, kiedy nie chcemy już więcej nazywać/rozbijać naszych
    zmiennych. Wtedy dużo szybciej napisać [**] niż [; intros]. W naszym
    przypadku chcemy nazwać jedynie pierwsze dwie zmienne, a resztę wrzucamy
    do kontekstu jak leci.

    Wzorzec [_] pozwala pozbyć się zmiennej lub hipotezy. Taktyka [intros _]
    jest wobec tego równoważna [intro H; clear H] (przy założeniu, że [H]
    jest wolne), ale dużo bardziej zwięzła w zapisie. Nie możemy jednak
    usunąć zmiennych lub hipotez, od których zależą inne zmienne lub hipotezy.
    W naszym przedostatnim przykładzie bez problemu usuwamy hipotezę [P /\
    Q /\ R], gdyż żaden term od niej nie zależy. Jednak w ostatnim przykładzie
    nie możemy usunąć [P], gdyż zależy od niego hipoteza [P /\ Q /\ R]. *)

Example intros_1 :
  forall P0 P1 P2 P3 P4 P5 : Prop,
    P0 /\ P1 /\ P2 /\ P3 /\ P4 /\ P5 -> P3.
Proof.
  intros * [p0 [p1 [p2 [p3 [p4 p5]]]]].
Restart.
  intros * (p0 & p1 & p2 & p3 & p4 & p5).
Abort.

(** Wzorce postaci [(p_1 & ... & p_n)] pozwalają rozbijać termy zagnieżdżonych
    typów induktywnych. Jak widać na przykładzie, im bardziej zagnieżdżony
    jest typ, tym bardziej opłaca się użyć tego rodzaju wzorca. *)

Example intros_2 :
  forall x y : nat, x = y -> y = x.
Proof.
  intros * ->.
Restart.
  intros * <-.
Abort.

(** Wzorców [->] oraz [<-] możemy użyć, gdy chcemy wprowadzić do kontekstu
    równanie, przepisać je i natychmiast się go pozbyć. Wobec tego taktyka
    [intros ->] jest równoważna czemuś w stylu [intro H; rewrite H in *;
    clear H] (oczywiście pod warunkiem, że nazwa [H] nie jest zajęta). *)

Example intros_3 :
  forall a b c d : nat, (a, b) = (c, d) -> a = c.
Proof.
  Fail intros * [p1 p2].
Restart.
  intros * [= p1 p2].
Abort.

(** Wzorzec postaci [= p_1 ... p_n] pozwala rozbić równanie między parami
    (i nie tylko) na składowe. W naszym przypadu mamy równanie [(a, b) =
    (c, d)] — zauważmy, że nie jest ono koniunkcją dwóch równości [a = c]
    oraz [b = d], co jasno widać na przykładzie, ale można z niego ową
    koniunkjcę wywnioskować. Taki właśnie efekt ma wzorzec [= p1 p2] —
    dodaje on nam do kontekstu hipotezy [p1 : a = c] oraz [p2 : b = d]. *)

Example intros_4 :
  forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros until 2. intro p. apply H in p. apply H0 in p.
Restart.
  intros until 2. intros p %H %H0.
Abort.

(** Taktyka [intros until x] wprowadza do kontekstu wszystkie zmienne jak
    leci dopóki nie natknie się na taką, która nazywa się "x". Taktyka
    [intros until n], gdzie [n] jest liczbą, wprowadza do kontekstu wszyskto
    jak leci aż do n-tej nie-zależnej hipotezy (tj. przesłanki implikacji).
    W naszym przykładzie mamy 3 przesłanki implikacji: [(P -> Q)], [(Q -> R)]
    i [P], więc taktyka [intros until 2] wprowadza do kontekstu dwie pierwsze
    z nich oraz wszystko, co jest poprzedza.

    Wzorzec [x %H_1 ... %H_n] wprowadza do kontekstu zmienną [x], a następnie
    aplikuje do niej po kolei hipotezy [H_1], ..., [H_n]. Taki sam efekt można
    osiągnąć ręcznie za pomocą taktyki [intro x; apply H_1 in x; ... apply H_n
    in x]. *)

(** **** Ćwiczenie (intros) *)

(** Taktyka [intros] ma jeszcze trochę różnych wariantów. Poczytaj o nich
    w manualu. *)

(** ** [fix] *)

(** [fix] to taktyka służąca do dowodzenia bezpośrednio przez rekursję. W
    związku z tym nadeszła dobra pora, żeby pokazać wszystkie możliwe sposoby
    na użycie rekursji w Coqu. Żeby dużo nie pisać, przyjrzyjmy się przykładom:
    zdefiniujemy/udowodnimy regułę ndukcyjną dla liczb naturalnych, którą
    powinieneś znać ja własną kieszeń (a jeżeli nie, to marsz robić zadania
    z liczb naturalnych!). *)

Definition nat_ind_fix_term
  (P : nat -> Prop) (H0 : P 0)
  (HS : forall n : nat, P n -> P (S n))
    : forall n : nat, P n :=
      fix f (n : nat) : P n :=
      match n with
          | 0 => H0
          | S n' => HS n' (f n')
      end.

(** Pierwszy, najbardziej prymitywny sposób to użycie konstruktu [fix]. [fix]
    to podstawowy budulec Coqowej rekursji, ale ma tę wadę, że trzeba się
    trochę napisać: w powyższym przykładzie najpierw piszemy [forall n : nat,
    P n], a następnie powtarzamy niemal to samo, pisząc
    [fix f (n : nat) : P n]. *)

Fixpoint nat_ind_Fixpoint_term
  (P : nat -> Prop) (H0 : P 0)
  (HS : forall n : nat, P n -> P (S n))
  (n : nat) : P n :=
match n with
    | 0 => H0
    | S n' => HS n' (nat_ind_Fixpoint_term P H0 HS n')
end.

(** Rozwiązaniem powyższej robnej niedogodności jest komenda [Fixpoint],
    która jest skrótem dla [fix]. Oszczędza nam ona pisania dwa razy tego
    samego, dzięki czemu definicja jest o linijkę krótsza. *)

Fixpoint nat_ind_Fixpoint_tac
  (P : nat -> Prop) (H0 : P 0)
  (HS : forall n : nat, P n -> P (S n))
  (n : nat) : P n.
Proof.
  apply nat_ind_Fixpoint_tac; assumption.
  Fail Guarded.
  (* ===> Długi komunikat o błędzie. *)
   Show Proof.
  (* ===> (fix nat_ind_Fixpoint_tac
                 (P : nat -> Prop) (H0 : P 0)
                 (HS : forall n : nat, P n -> P (S n))
                 (n : nat) {struct n} : P n :=
                   nat_ind_Fixpoint_tac P H0 HS n) *)
Restart.
  destruct n as [| n'].
    apply H0.
    apply HS. apply nat_ind_Fixpoint_tac; assumption.
  Guarded.
  (* ===> The condition holds up to here *)
Defined.

(** W trzecim podejściu również używamy komendy [Fixpoint], ale tym razem,
    zamiast ręcznie wpisywać term, definiujemy naszą regułę za pomocą taktyk.
    Sposób ten jest prawie zawsze (dużo) dłuższy niż poprzedni, ale jego
    zaletą jest to, że przy skomplikowanych celach jest dużo ławiejszy do
    ogarnięcia dla człowieka.

    Korzystając z okazji rzućmy okiem na komendę [Guarded]. Jest ona przydatna
    gdy, tak jak wyżej, dowodzimy lub definiujemy bezpośrednio przez rekursję.
    Sprawdza ona, czy wszystkie dotychczasowe wywołania rekurencyjne odbyły
    się na strukturalnie mniejszych podtermach. Jeżeli nie, wyświetla ona
    wiadomość, która informuje nas, gdzie jest błąd. Niestety wiadomości te
    nie zawsze są czytelne.

    Tak właśnie jest, gdy w powyższym przykładzie używamy jej po raz pierwszy.
    Na szczęście ratuje nas komenda [Show Proof], która pokazuje, jak wygląda
    term, która póki co wygenerowały taktyki. Pokazuje on nam term postaci
    [nat_ind_Fixpoint_tac P H0 HS n := nat_ind_Fixpoint_tac P H0 HS n], który
    próbuje wywołać się rekurencyjnie na tym samym argumencie, na którym sam
    został wywołany. Nie jest więc legalny.

    Jeżeli z wywołaniami rekurencyjnymi jest wszystko ok, to komenda [Guarded]
    wyświetla przyjazny komunikat. Tak właśnie jest, gdy używamy jej po raz
    drugi — tym razem wywołanie rekurencyjne odbywa się na [n'], które jest
    podtermem [n]. *)

Definition nat_ind_fix_tac :
  forall (P : nat -> Prop) (H0 : P 0)
    (HS : forall n : nat, P n -> P (S n)) (n : nat), P n.
Proof.
  Show Proof.
  (* ===> ?Goal *)
  fix 4.
  Show Proof.
  (* ===> (fix nat_ind_fix_tac
               (P : nat -> Prop) (H0 : P 0)
               (HS : forall n : nat, P n -> P (S n))
               (n : nat) {struct n} : P n := ... *)
 destruct n as [| n'].
    apply H0.
    apply HS. apply nat_ind_fix_tac; assumption.
Defined.

(** Taktyki [fix] możemy użyć w dowolnym momencie, aby rozpocząć dowodzenie/
    definiowanie bezpośrednio przez rekursję. Jako argument musimy podać
    numer argument głównego. W powyższym przykładzie chcemy robić rekursję
    po [n], który jest czwarty z kolei (po [P], [H0] i [HS]).

    Komenda [Show Proof] pozwala nam odkryć, że użycie taktyki [fix] w
    trybie dowodzenia odpowiada po prostu użyciu konstruktu [fix] lub
    komendy [Fixpoint].

    Taktyka [fix] jest bardzo prymitywna i prawie nigdy nie jest używana,
    tak samo jak konstrukt [fix] (najbardziej poręczne są sposoby, które
    widzieliśmy w przykladach 2 i 3), ale była dobrym pretekstem, żeby
    omówić wszystkie sposoby użycia rekursji w jednym miejscu. *)

(** ** [functional induction] i [functional inversion] *)

(** Taktyki [functional induction] i [functional inversion] są związane z
    pojęciem indukcji funkcyjnej. Dość szczegółowy opis tej pierwszej jest
    w notatkach na seminarium: https://zeimer.github.io/Seminar.html#lab229

    Drugą z nich póki co pominiemy. Kiedyś z pewnością napiszę coś więcej
    o indukcji funkcyjnej lub chociaż przetłumaczę zalinkowane notatki na
    polski. *)

(** ** [generalize dependent] *)

(** [generalize dependent] to taktyka będąca przeciwieństwem [intro] — dzięki
    niej możemy przerzucić rzeczy znajdujące się w kontekście z powrotem do
    kontekstu. Nieformalnie odpowiada ona sposobowi rozumowania: aby pokazać,
    że cel zachodzi dla pewnego konkretnego [x], wystarczy czy pokazać, że
    zachodzi dla dowolnego [x].

    W rozumowaniu tym z twierdzenia bardziej ogólnego wyciągamy wniosek, że
    zachodzi twierdzenie bardziej szczegółowe. Nazwa [generalize] bierze się
    stąd, że w dedukcji naturalnej nasze rozumowania przeprowadzamy "od tyłu".
    Człon "dependent" bierze się stąd, że żeby zgeneralizować [x], musimy
    najpierw zgeneralizować wszystkie obiekty, które są od niego zależne. Na
    szczęście taktyka [generalize dependent] robi to za nas. *)

Example generalize_dependent_0 :
  forall n m : nat, n = m -> m = n.
Proof.
  intros. generalize dependent n.
Abort.

(** Użycie [intros] wprowadza do kontekstu [n], [m] i [H]. [generalize
    dependent n] przenosi [n] z powrotem do celu, ale wymaga to, aby do
    celu przenieść również [H], gdyż typ [H], czyli [n = m], zależy od [n]. *)

(** **** Ćwiczenie (generalize i revert) *)

(** [generalize dependent] jest wariantem taktyki [generalize]. Taktyką o
    niemal identycznym działaniu jest [revert dependent], wariant taktyki
    [revert]. Przeczytaj dokumentację [generalize] i [revert] w manualu i
    sprawdź, jak działają. *)

(** **** Ćwiczenie (my_rec) *)

(** Zaimplementuj taktykę [rec x], która będzie pomagała przy dowodzeniu
    bezpośrednio przez rekursję po [x]. Taktyka [rec x] ma działać jak
    [fix n; destruct x], gdzie [n] to pozycja argumentu [x] w celu. Twoja
    taktyka powinna działać tak, żeby poniższy dowód zadziałał bez potrzeby
    wprowadzania modyfikacji.

    Wskazówka: połącz taktyki [fix], [intros], [generalize dependent] i
    [destruct]. *)

(* begin hide *)
Ltac rec x :=
  intros until x; generalize dependent x; fix 1; destruct x.
(* end hide *)

Lemma plus_comm_rec :
  forall n : nat, n + 1 = S n.
Proof.
  rec n.
    reflexivity.
    cbn. f_equal. rewrite plus_comm_rec. reflexivity.
Qed.

(** ** [refine] *)

(** Fama głosi, że w zamierzchłych czasach, gdy nie było jeszcze taktyk,
    a światem Coqa rządził Chaos (objawiający się dowodzeniem przez ręczne
    wpisywanie termów), jeden z Coqowych bogów imieniem He-fait-le-stos, w
    przebłysku kreatywnego geniuszu wymyślił dedukcję naturalną i stworzył
    pierwszą taktykę, której nadał imię [refine]. Pomysł przyjał się i od
    tej pory Coqowi bogowie poczęli używać jej do tworzenia coraz to innych
    taktyk. Tak [refine] stała się matką wszystkich taktyk.

    Oczywiście legenda ta jest nieprawdziwa — deduckcję naturalną wymyślił
    Gerhard Gentzen, a podstawowe taktyki są zaimplementowane w Ocamlu. Nie
    umniejsza to jednak mocy taktyki [refine]. Jej działanie podobne jest
    do taktyki [exact], z tym że term będący jej argumentem może też zawierać
    dziury [_]. Jeżeli naszym celem jest [G], to taktyka [refine g] rozwiązuje
    cel, jeżeli [g] jest termem typu [G], i generuje taką ilość podcelów, ile
    [g] zawiera dziur, albo zawodzi, jeżeli [g] nie jest typu [G].

    Zobaczmy działanie taktyki [refine] na przykładach. *)

Example refine_0 : 42 = 42.
Proof.
  refine eq_refl.
Qed.

(** W powyższym przykładzie używamy [refine] tak jak użylibyśmy [exact]a.
    [eq_refl] jest typu [42 = 42], gdyż Coq domyśla się, że tak naprawdę
    chodzi nam o [@eq_refl nat 42]. Ponieważ [eq_refl] zawiera 0 dziur,
    [refine eq_refl] rozwiązuje cel i nie generuje podcelów. *)

Example refine_1 :
  forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  refine (fun P Q : Prop => _).
  refine (fun H => match H with | conj p q => _ end).
  refine (conj _ _ ).
    refine q.
    refine p.
Restart.
  intros P Q. intro H. elim H; intros p q. split.
    exact q.
    exact p.
Qed.

(** W tym przykładzie chcemy pokazać przemienność konunkcji. Ponieważ nasz
    cel jest kwantyfikacją uniwersalną, jego dowodem musi być jakaś funkcja
    zależna. Funkcję tę konstruujemy taktyką [refine (fun P Q : Prop => _)].
    Nie podajemy jednak ciała funkcji, zastępując je dzurą [_], bo chcemy
    podać je później. W związku z tym nasz obecny cel zostaje rozwiązany, a
    w zamian dostajemy nowy cel postaci [P /\ Q -> Q /\ P], gdyż takiego
    typu jest ciało naszej funkcji. To jednak nie wszystko: w kontekście
    pojawiają się [P Q : Prop]. Wynika to z tego, że [P] i [Q] mogą zostać
    użyte w definicji ciała naszej funkcji.

    Jako, że naszym celem jest implikacja, jej dowodem musi być funkcja.
    Taktyka [refine (fun H => match H with | conj p q => _ end)] pozwala
    nam tę funkcję skonstruować. Ciałem naszej funkcji jest dopasowanie
    zawierające dziurę. Wypełnienie jej będzie naszym kolejnym celem. Przy
    jego rozwiązywaniu będziemy mogli skorzystać z [H], [p] i [q]. Pierwsza
    z tych hipotez pochodzi o wiązania [fun H => ...], zaś [p] i [q] znajdą
    się w kontekście dzięki temu, że zostały związane podczas dopasowania
    [conj p q].

    Teraz naszym celem jest [Q /\ P]. Ponieważ dowody koniunkcji są postaci
    [conj l r], gdzie [l] jest dowodem pierwszego członu, a [r] drugiego,
    używamy taktyki [refine (conj _ _)], by osobno skonstruować oba człony.
    Tym razem nasz proofterm zawiera dwie dziury, więc wygenerowane zostaną
    dwa podcele. Obydwa zachodzą na mocy założenia, a rozwiązujemy je także
    za pomocą [refine].

    Powyższy przykład pokazuje, że [refine] potrafi zastąpić cała gamę
    przeróżnych taktyk, które dotychczas uważaliśmy za podstawowe: [intros],
    [intro], [elim] (bardzo prymitywna forma taktyki [destruct]), [split]
    oraz [exact]. Określenie "matka wszystkich taktyk" wydaje się całkiem
    uzasadnione. *)

(** **** Ćwiczenie (my_exact) *)

(** Napisz taktykę [my_exact], która działa tak, jak [exact]. Użyj taktyki
    [refine]. *)

(* begin hide *)
Ltac my_exact t := refine t.
(* end hide *)

Example my_exact_0 :
  forall P : Prop, P -> P.
Proof.
  intros. my_exact H.
Qed.

(** **** Ćwiczenie [my_intro] *)

(** Zaimplementuj taktykę [my_intro1], która działa tak, jak [intro], czyli
    próbuje wprowadzić do kontekstu zmienną o domyślnej nazwie. Zaimplementuj
    też taktykę [my_intro2 x], która działa tak jak [intro x], czyli próbuje
    wprowadzić do kontekstu zmienną o nazwie [x].

    Bonus: przeczytaj dokumentację na temat notacji dla taktyk (komenda
    [Tactic Notation]) i napisz taktykę [my_intro], która działa tak jak
    [my_intro1], gdy nie dostanie argumentu, a tak jak [my_intro2], gdy
    dostanie argument. *)

(* begin hide *)
Ltac my_intro1 := refine (fun _ => _).
Ltac my_intro2 x := refine (fun x => _).

Tactic Notation "my_intro" := my_intro1.
Tactic Notation "my_intro" ident(x) := my_intro2 x.
(* end hide *)

Example my_intro_0 :
  forall P : Prop, P -> P.
Proof.
  my_intro1. my_intro2 H. my_exact H.
Restart.
  my_intro. my_intro H. my_exact H.
Qed.

(** **** Ćwiczenie (my_apply) *)

(** Napisz taktykę [my_apply H], która działa tak jak [apply H]. *)

(* begin hide *)
Ltac my_apply H := refine (H _).
(* end hide *)

Example my_apply_0 :
  forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  my_intro P. my_intro Q. my_intro p. my_intro H.
  my_apply H. my_exact p.
Qed.

(** ** [rewrite] *)

(* begin hide *)
(** TODO:
    - [revgoals], [swap], [cycle] i inne zarządzanie celami
    - [cbn], [cbv], [simpl], [hnf], [compute], [vm_compute],
      [native_compute], [lazy], [red] i inne taktyki do redukcji.
*)
(* end hide *)

(** * Taktyki dla równości i równoważności *)

Require Import Arith.

Example reflexivity_0 :
  forall n : nat, n <= n.
Proof. reflexivity. Qed.

(** Znasz już taktykę [reflexivity]. Mogłoby się wydawać, że służy ona do
    udowadniania celów postaci [x = x] i jest w zasadzie równoważna taktyce
    [apply eq_refl], ale nie jest tak. Taktyka [reflexivity] potrafi rozwiązać
    każdy cel postaci [R x y], gdzie [R] jest relacją zwrotną, a [x] i [y] są
    konwertowalne (oczywiście pod warunkiem, że udowodnimy wcześniej, że [R]
    faktycznie jest zwrotna; w powyższym przykładzie odpowiedni fakt został
    zaimportowany z modułu [Arith]).

    Żeby zilustrować ten fakt, zdefiniujmy nową relację zwrotną i zobaczmy,
    jak użyć taktyki [reflexivity] do radzenia sobie z nią. *)

Definition eq_ext {A B : Type} (f g : A -> B) : Prop :=
  forall x : A, f x = g x.

(** W tym celu definiujemy relację [eq_ext], która głosi, że funkcja
    [f : A -> B] jest w relacji z funkcją [g : A -> B], jeżeli [f x]
    jest równe [g x] dla dowolnego [x : A]. *)

Require Import RelationClasses.

(** Moduł [RelationClasses] zawiera definicję zwrotności [Reflexive], z której
    korzysta taktyka [reflexivity]. Jeżeli udowodnimy odpowiednie twierdzenie,
    będziemy mogli używać taktyki [reflexivity] z relacją [eq_ext]. *)

Instance Reflexive_eq_ext :
  forall A B : Type, Reflexive (@eq_ext A B).
Proof.
  unfold Reflexive, eq_ext. intros A B f x. reflexivity.
Defined.

(** A oto i rzeczone twierdzenie oraz jego dowód. Zauważmy, że taktyki
    [reflexivity] nie używamy tutaj z relacją [eq_ext], a z relacją [=],
    gdyż używamy jej na celu postaci [f x = f x].

    Uwaga: żeby taktyka [reflexivity] "widziała" ten dowód, musimy skorzystać
    ze słowa kluczowego [Instance] zamiast z [Theorem] lub [Lemma]. *)

Example reflexivity_1 :
  eq_ext (fun _ : nat => 42) (fun _ : nat => 21 + 21).
Proof. reflexivity. Defined.

(** Voilà! Od teraz możemy używać taktyki [reflexivity] z relacją [eq_ext].

    Są jeszcze dwie taktyki, które czasem przydają się przy dowodzeniu
    równości (oraz równoważności). *)

Example symmetry_transitivity_0 :
  forall (A : Type) (x y z : nat), x = y -> y = z -> z = x.
Proof.
  intros. symmetry. transitivity y.
    assumption.
    assumption.
Qed.

(** Mogłoby się wydawać, że taktyka [symmetry] zamienia cel postaci [x = y]
    na [y = x], zaś taktyka [transitivity y] rozwiązuje cel postaci [x = z]
    i generuje w zamian dwa cele postaci [x = y] i [y = z]. Rzeczywistość
    jest jednak bardziej hojna: podobnie jak w przypadku [reflexivity],
    taktyki te działają z dowolnymi relacjami symetrycznymi i przechodnimi. *)

Instance Symmetric_eq_ext :
  forall A B : Type, Symmetric (@eq_ext A B).
Proof.
  unfold Symmetric, eq_ext. intros A B f g H x. symmetry. apply H.
Defined.

Instance Transitive_eq_ext :
  forall A B : Type, Transitive (@eq_ext A B).
Proof.
  unfold Transitive, eq_ext. intros A B f g h H H' x.
  transitivity (g x); auto.
Defined.

(** Użycie w dowodach taktyk [symmetry] i [transitivity] jest legalne, gdyż
    nie używamy ich z relacją [eq_ext], a z relacją [=]. *)

Example symmetry_transitivity_1 :
  forall (A B : Type) (f g h : A -> B),
    eq_ext f g -> eq_ext g h -> eq_ext h f.
Proof.
  intros. symmetry. transitivity g.
    assumption.
    assumption.
Qed.

(** Dzięki powyższym twierdzeniom możemy teraz posługiwać się taktykami
    [symmetry] i [transitivity] dowodząc faktów na temat relacji [eq_ext].
    To jednak wciąż nie wyczerpuje naszego arsenału taktyk do radzenia sobie
    z relacjami równoważności. *)

Check f_equal.
(* ===> f_equal : forall (A B : Type) (f : A -> B) (x y : A),
                    x = y -> f x = f y *)

(** [f_equal] to jedna z podstawowych właściwości relacji [eq], która głosi,
    że wszystkie funkcje zachowują równość. Innymi słowy: aby pokazać, że
    wartości zwracane przez funkcję są równe, wystarczy pokazać, że argumenty
    są równe. Ten sposób rozumowania, choć nie jest ani jedyny, ani skuteczny
    na wszystkie cele postaci [f x = f y], jest wystarczająco częsty, aby mieć
    swoją własną taktykę, którą zresztą powinieneś już dobrze znać — jest nią
    [f_equal].

    Taktyka ta sprowadza się w zasadzie do jak najsprytniejszego aplikowania
    faktu [f_equal]. Nie potrafi ona wprowadzać zmiennych do kontekstu, a z
    wygenerowanych przez siebie podcelów rozwiązuje jedynie te postaci [x = x],
    ale nie potrafi rozwiązać tych, które zachodzą na mocy założenia. *)

(** **** Ćwiczenie (my_f_equal) *)

(** Napisz taktykę [my_f_equal], która działa jak [f_equal] na sterydach, tj.
    poza standardową funkcjonalnością [f_equal] potrafi też wprowadzać zmienne
    do kontekstu oraz rozwiązywać cele prawdziwe na mocy założenia.

    Użyj tylko jednej klauzuli [match]a. Nie używaj taktyki [subst]. Bonus:
    wykorzystaj kombinator [first], ale nie wciskaj go na siłę. Z czego
    łatwiej jest skorzystać: rekursji czy iteracji? *)

(* begin hide *)
(* Odp: łatwiejsza jest iteracja. *)
Ltac my_f_equal := intros; repeat (try
match goal with
    | |- ?f ?x = ?g ?y =>
        let H1 := fresh "H" in
        let H2 := fresh "H" in
          assert (H1 : f = g); assert (H2 : x = y);
          rewrite ?H1, ?H2
end; first [reflexivity | assumption | idtac]).
(* end hide *)

Example f_equal_0 :
  forall (A : Type) (x : A), x = x.
Proof.
  intros. f_equal.
  (* Nie działa, bo [x = x] nie jest podcelem
     wygenerowanym przez [f_equal]. *)
Restart.
  my_f_equal.
Qed.

Example f_equal_1 :
  forall (A : Type) (x y : A), x = y -> x = y.
Proof.
  intros. f_equal.
Restart.
  my_f_equal.
Qed.

Example f_equal_2 :
  forall (A B C D E : Type) (f f' : A -> B -> C -> D -> E)
    (a a' : A) (b b' : B) (c c' : C) (d d' : D),
      f = f' -> a = a' -> b = b' -> c = c' -> d = d' ->
        f a b c d = f' a' b' c' d'.
Proof.
  intros. f_equal. all: assumption.
Restart.
  my_f_equal.
Qed.

(** **** Ćwiczenie (właściwości [f_equal]) *)

(** Przyjrzyj się definicjom [f_equal], [id], [compose], [eq_sym], [eq_trans],
    a następnie udowodnij poniższe lematy. Ich sens na razie niech pozostanie
    ukryty — kiedyś być może napiszę coś na ten temat. Jeżeli intrygują cię
    one, przyjrzyj się książce https://homotopytypetheory.org/book/ *)

Require Import Coq.Program.Basics.

Print f_equal.
Print eq_sym.
Print eq_trans.
Print compose.

Section f_equal_properties.

Variables
  (A B C : Type)
  (f : A -> B) (g : B -> C)
  (x y z : A)
  (p : x = y) (q : y = z).

Lemma f_equal_refl :
  f_equal f (eq_refl x) = eq_refl (f x).
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma f_equal_id :
  f_equal id p = p.
(* begin hide *)
Proof. destruct p. cbn. trivial. Qed.
(* end hide *)

Lemma f_equal_compose :
  f_equal g (f_equal f p) = f_equal (compose g f) p.
(* begin hide *)
Proof. destruct p. cbn. trivial. Qed.
(* end hide *)

Lemma eq_sym_map_distr :
  f_equal f (eq_sym p) = eq_sym (f_equal f p).
(* begin hide *)
Proof. destruct p. cbn. trivial. Qed.
(* end hide *)

Lemma eq_trans_map_distr :
  f_equal f (eq_trans p q) = eq_trans (f_equal f p) (f_equal f q).
(* begin hide *)
Proof. destruct p, q. cbn. trivial. Qed.
(* end hide *)

End f_equal_properties.

(** Ostatnią taktyką, którą poznamy w tym podrozdziale, jest [f_equiv], czyli
    pewne uogólnienie taktyki [f_equal]. Niech nie zmyli cię nazwa tej taktyki
    — bynajmniej nie przydaje się ona jedynie do rozumowań dotyczących relacji
    równoważności. *)

Require Import Classes.Morphisms.

(** Aby móc używać tej taktyki, musimy najpierw zaimportować moduł
    [Classes.Morphisms]. *)

Definition len_eq {A : Type} (l1 l2 : list A) : Prop :=
  length l1 = length l2.

(** W naszym przykładzie posłużymy się relacją [len_eq], która głosi, że
    dwie listy są w relacji gdy mają taką samą długość. *)

Instance Proper_len_eq_map {A : Type} :
  Proper (@len_eq A ==> @len_eq A ==> @len_eq A) (@app A).
Proof.
  Locate "==>".
  unfold Proper, respectful, len_eq.
  induction x as [| x xs]; destruct y; inversion 1; cbn; intros.
    assumption.
    f_equal. apply IHxs; assumption.
Qed.

(** Taktyka [f_equal] działa na celach postaci [f x = f y], gdzie [f] jest
    dowolne, albowiem wszystkie funkcje zachowują równość. Analogicznie
    taktyka [f_equiv] działa na celach postaci [R (f x) (f y)], gdzie [R]
    jest dowolną relacją, ale tylko pod warunkiem, że funkcja [f] zachowuje
    relację [R].

    Musi tak być, bo gdyby [f] nie zachowywała [R], to mogłoby jednocześnie
    zachodzić [R x y] oraz [~ R (f x) (f y)], a wtedy sposób rozumowania
    analogiczny do tego z twierdzenia [f_equal] byłby niepoprawny.

    Aby taktyka [f_equiv] "widziała", że [f] zachowuje [R], musimy znów
    posłużyć się komendą [Instance] i użyć [Proper], które służy do
    zwięzłego wyrażania, które konkretnie relacje i w jaki sposób zachowuje
    dana funkcja.

    W naszym przypadku będziemy chcieli pokazać, że jeżeli listy [l1] oraz
    [l1'] są w relacji [len_eq] (czyli mają taką samą długość) i podobnie
    dla [l2] oraz [l2'], to wtedy konkatenacja [l1] i [l2] jest w relacji
    [len_eq] z konkatenacją [l1'] i [l2']. Ten właśnie fakt jest wyrażany
    przez zapis [Proper (@len_eq A ==> @len_eq A ==> @len_eq A) (@app A)].

    Należy też zauważyć, że strzałka [==>] jest jedynie notacją dla tworu
    zwanego [respectful], co możemy łatwo sprawdzić komendą [Locate.] *)

Example f_equiv_0 :
  forall (A B : Type) (f : A -> B) (l1 l1' l2 l2' : list A),
    len_eq l1 l1' -> len_eq l2 l2' ->
      len_eq (l1 ++ l2) (l1' ++ l2').
Proof.
  intros. f_equiv.
    assumption.
    assumption.
Qed.

(** Voilà! Teraz możemy używać taktyki [f_equiv] z relacją [len_eq] oraz
    funkcją [app] dokładnie tak, jak taktyki [f_equal] z równością oraz
    dowolną funkcją.

    Trzeba przyznać, że próba użycia [f_equiv] z różnymi kombinacjami
    relacji i funkcji może zakończyć się nagłym i niekontrolowanym
    rozmnożeniem lematów mówiących o tym, że funkcje zachowują relacje.
    Niestety, nie ma na to żadnego sposobu — jak przekonaliśmy się wyżej,
    udowodnienie takiego lematu to jedyny sposób, aby upewnić się, że nasz
    sposób rozumowania jest poprawny. *)

(** **** Ćwiczenie (f_equiv_filter) *)

Require Import List.
Import ListNotations.

Definition stupid_id {A : Type} (l : list A) : list A :=
  filter (fun _ => true) l.

(** Oto niezbyt mądry sposób na zapisanie funkcji identycznościowej na
    listach typu [A]. Pokaż, że [stupid_id] zachowuje relację [len_eq],
    tak aby poniższy dowód zadziałał bez wpowadzania zmian. *)

(* begin hide *)
Instance Proper_len_eq_stupid_id {A : Type} :
  Proper (@len_eq A ==> @len_eq A) (@stupid_id A).
Proof.
  unfold Proper, respectful, len_eq.
  induction x as [| x xs]; destruct y; inversion 1; cbn; intros.
    trivial.
    f_equal. apply (IHxs _ H1).
Qed.
(* end hide *)

Example f_equiv_1 :
  forall (A : Type) (l l' : list A),
    len_eq l l' -> len_eq (stupid_id l) (stupid_id l').
Proof.
  intros. f_equiv. assumption.
Qed.

(** * Automatyzacja *)

(** ** [auto] i [trivial] (TODO) *)
(** ** [autorewrite] (TODO) *)

(** ** [btauto] *)

(** [btauto] to taktyka, która potrafi rozwiązywać równania boolowskie, czyli
    cele postaci [x = y], gdzie [x] i [y] są wyrażeniami mogącymi zawierać
    boolowskie koniunkcje, dysjunkcje, negacje i inne rzeczy (patrz manual).

    Taktykę można zaimportować komendą [Require Import Btauto]. Uwaga: nie
    potrafi ona wprowadzać zmiennych do kontekstu. *)

(** **** Ćwiczenie (my_btauto) *)

(** Napisz następujące taktyki:
    - [my_btauto] — taktyka podobna do [btauto]. Potrafi rozwiązywać cele,
      które są kwantyfikowanymi równaniami na wyrażeniach boolowskich,
      składającymi się z dowolnych funkcji boolowskich (np. [andb], [orb]).
      W przeciwieństwie do [btauto] powinna umieć wprowadzać zmienne do
      kontekstu.
    - [my_btauto_rec] — tak samo jak [my_btauto], ale bez używana
      kombinatora [repeat]. Możesz używać jedynie rekurencji.
    - [my_btauto_iter] — tak samo jak [my_btauto], ale bez używania
      rekurencji. Możesz używać jedynie kombinatora [repeat].
    - [my_btauto_no_intros] — tak samo jak [my_btauto], ale bez używania
      taktyk [intro] oraz [intros]. *)

(** Uwaga: twoja implementacja taktyki [my_btauto] będzie diametralnie różnić
    się od implementacji taktyki [btauto] z biblioteki standardowej. [btauto]
    jest zaimplementowana za pomocą reflekcji. Dowód przez reflekcję omówimy
    później. *)

(* begin hide *)
Ltac my_btauto := intros; repeat
match goal with
    | b : bool |- _ => destruct b
end; cbn; reflexivity.

Ltac my_btauto_rec := intros;
match goal with
    | b : bool |- _ => destruct b; my_btauto_rec
    | _ => cbn; reflexivity
end.

Ltac my_btauto_iter := my_btauto.

Ltac my_btauto_no_intros := repeat
match goal with
    | |- forall b : bool, _ => destruct b
end; cbn; reflexivity.
(* end hide *)

Section my_btauto.

Require Import Bool.
Require Import Btauto.

Theorem andb_dist_orb :
  forall b1 b2 b3 : bool,
    b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
Proof.
  intros. btauto.
Restart.
  my_btauto.
Restart.
  my_btauto_rec.
Restart.
  my_btauto_iter.
Restart.
  my_btauto_no_intros.
Qed.

Theorem negb_if :
  forall b1 b2 b3 : bool,
    negb (if b1 then b2 else b3) = if negb b1 then negb b3 else negb b2.
Proof.
  intros. btauto.
Restart.
  my_btauto.
Restart.
  my_btauto_rec.
Restart.
  my_btauto_iter.
Restart.
  my_btauto_no_intros.
Qed.

(** Przetestuj działanie swoich taktyk na reszcie twierdzeń z rozdziału
    o logice boolowskiej. *)

End my_btauto.

(** ** [congruence] *)

Example congruence_0 :
  forall P : Prop, true <> false.
Proof. congruence. Qed.

Example congruence_1 :
  forall (A : Type) (f : A -> A) (g : A -> A -> A) (a b : A),
    a = f a -> g b (f a) = f (f a) -> g a b = f (g b a) ->
      g a b = a.
Proof.
(* begin hide *)
  intros. rewrite H1, H at 1. rewrite H0, <- !H. trivial.
Restart.
(* end hide *)
  congruence.
Qed.

Example congruence_2 :
  forall (A : Type) (f : A -> A * A) (a c d : A),
    f = pair a -> Some (f c) = Some (f d) -> c = d.
Proof.
(* begin hide *)
  intros. inversion H0. rewrite H in H2. inversion H2. trivial.
Restart.
(* end hide *)
  congruence.
Qed.

(** [congruece] to taktyka, która potrafi rozwiązywać cele dotyczące
    nieinterpretowanych równości, czyli takie, których prawdziwość zależy
    jedynie od hipotez postaci [x = y] i które można udowodnić ręcznie za
    pomocą mniejszej lub większej ilości [rewrite]'ów. [congruence] potrafi
    też rozwiązywać cele dotyczące konstruktorów. W szczególności wie ona,
    że konstruktory są injektywne i potrafi odróżnić [true] od [false]. *)

(** **** Ćwiczenie (congruence) *)

(** Udowodnij przykłady [congruence_1] i [congruence_2] ręcznie. *)

(** **** Ćwiczenie (discriminate) *)

(** Inną taktyką, która potrafi rozróżniać konstruktory, jest [discriminate].
    Zbadaj, jak działa ta taktyka. Znajdź przykład celu, który [discriminate]
    rozwiązuje, a na którym [congruence] zawodzi. Wskazówka: [congruence]
    niebardzo potrafi odwijać definicje. *)

(* begin hide *)
Definition mytrue := true.

Goal ~ (mytrue = false).
Proof.
  Fail congruence.
  discriminate.
Qed.
(* end hide *)

(** ** [decide equality] *)

Inductive C : Type :=
    | c0 : C
    | c1 : C -> C
    | c2 : C -> C -> C
    | c3 : C -> C -> C -> C.

(** Przyjrzyjmy się powyższemu, dosć enigmatycznemu typowi. Czy posiada on
    rozstrzygalną równość? Odpowiedź jest twierdząca: rozstrzygalną równość
    posiada każdy typ induktywny, którego konstruktory nie biorą argumentów
    będących dowodami, funkcjami ani termami typów zależnych. *)

Theorem C_eq_dec :
  forall x y : C, {x = y} + {x <> y}.
(* begin hide *)
Proof.
  induction x.
    destruct y. left; trivial. 1-3: right; inversion 1.
    destruct y.
      Focus 2. destruct (IHx y); subst; auto. right. congruence.
      1-3: right; inversion 1.
    destruct y.
      Focus 3. destruct (IHx1 y1), (IHx2 y2); subst; auto.
        1-3: right; congruence.
      1-3: right; congruence.
    destruct y.
      Focus 4. destruct (IHx1 y1), (IHx2 y2), (IHx3 y3); subst; auto.
        1-7: right; congruence.
      1-3: right; congruence.
Defined.
(* end hide *)

(** Zanim przejdziesz dalej, udowodnij ręcznie powyższe twierdzenie. Przyznasz,
    że dowód nie jest zbyt przyjemny, prawda? Na szczęście nie musimy robić go
    ręcznie. Na ratunek przychodzi nam taktyka [decide equality], która umie
    udowadniać cele postaci [forall x y : T, {x = y} + {x <> y}], gdzie [T]
    spełnia warunki wymienione powyżej. *)

Theorem C_eq_dec' :
  forall x y : C, {x = y} + {x <> y}.
Proof. decide equality. Defined.


(** ** [omega] i [abstract] *)

(** [omega] to taktyka, która potrafi rozwiązywać cele dotyczące arytmetyki
    Presburgera. Jej szerszy opis można znaleźć w manualu. Na nasze potrzeby
    przez arytmetykę Presburgera możemy rozumieć równania ([=]), nie-równania
    ([<>]) oraz nierówności ([<], [<=], [>], [>=]) na typie [nat], które mogą
    zawierać zmienne, [0], [S], dodawanie i mnożenie przez stałą. Dodatkowo
    zdania tej postaci mogą być połączone spójnikami [/\], [\/], [->] oraz
    [~], ale nie mogą być kwantyfikowane — [omega] nie umie wprowadzać
    zmiennych do kontekstu. *)

Require Import Arith Omega.

Example omega_0 :
  forall n : nat, n + n = 2 * n.
Proof. intro. omega. Qed.

Example omega_1 :
  forall n m : nat, 2 * n + 1 <> 2 * m.
Proof. intros. omega. Qed.

Example omega_2 :
  forall n m : nat, n * m = m * n.
Proof. intros. try omega. Abort.

(** Jedną z wad taktyki [omega] jest rozmiar generowanych przez nią termów.
    Są tak wielkie, że wszelkie próby rozwinięcia definicji czy dowodów,
    które zostały przy jej pomocy skonstruowane, muszą z konieczności źle
    się skończyć. Zobaczmy to na przykładzie. *)

Lemma filter_length :
  forall (A : Type) (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l; cbn; try destruct (f a); cbn; omega.
Qed.

Print filter_length.
(* ===> Proofterm o długości 317 linijek. *)

(** Oto jedna ze standardowych właściwości list: filtrowanie nie zwiększa
    jej rozmiaru. Term skonstruowany powyższym dowodem, będący świadkiem
    tego faktu, liczy sobie 317 linijek długości (wypisaniu, wklejeniu do
    CoqIDE i usunięciu tego, co do termu nie należy). *)

Lemma filter_length' :
  forall (A : Type) (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l; cbn; try destruct (f a); cbn.
    trivial.
    apply le_n_S. assumption.
    eapply le_trans; eauto.
Qed.

Print filter_length'.
(* ===> Proofterm o długości 14 linijek. *)

(** Jak widać, ręczny dowód tego faktu daje w wyniku proofterm, który jest
    o ponad 300 linijk krótszy niż ten wyprodukowany przez taktykę [omega].
    Mogłoby się zdawać, że jesteśmy w sytuacji bez wyjścia: albo dowodzimy
    ręcznie, albo prooftermy będą tak wielkie, że nie będziemy mogli ich
    odwijać. Możemy jednak zjeść ciastko i mieć ciastko, a wszystko to za
    sprawą taktyki [abstract] i towarzyszącej jej komendy [Qed exporting]. *)

Lemma filter_length'' :
  forall (A : Type) (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l; cbn; try destruct (f a); cbn; abstract omega.
Qed exporting.

(* begin hide *)
(* [Qed exporting] psuje kolorowanie. Trzeba naprawić. *)

Goal False. Abort.
(* end hide *)

Print filter_length''.
(* ===> Proofterm o długości 13 linijek. *)

(** Taktyka [abstract t] działa tak jak [t], ale z tą różnicą, że ukrywa term
    wygenerowany przez [t] w zewnętrznym lemacie. Po zakończeniu dowodu możemy
    zakończyć go komendą [Qed exporting], co spowoduje zapisanie go w takiej
    skróconej postaci z odwołaniami do zewnętrznych lematów, albo standardowym
    [Qed], przez co term będzie wyglądał tak, jakbyśmy wcale nie użyli taktyki
    [abstract]. *)

(** ** [ring], [field] i tympodobne (TODO) *)

(* begin hide *)
(** TODO:
    - [ring], [ring_simplify]
    - [field], [field_simplify], [field_simplify_eq] *)

Require Import Ring.

(** Pierścień to struktura algebraiczna składająca się z pewnego typu A oraz
    działań + i *, które zachowują się mniej więcej tak, jak dodawanie i
    mnożenie liczb całkowitych. Przykładów jest sporo: liczby wymierne i
    rzeczywiste z dodawaniem i mnożeniem, wartości boolowskie z dysjunkcją i
    koniunkcją oraz wiele innych, których nie wymienię, gdyż są dla nas zbyt
    abstrakcyjne. *)

(** ** [lia]. [lra], [nia], [nra], [nsatz], [psatz] (TODO) *)

(** * Procedury decyzyjne dla logiki *)

Example tauto_0 :
  forall A B C D : Prop,
    ~ A \/ ~ B \/ ~ C \/ ~ D -> ~ (A /\ B /\ C /\ D).
Proof. tauto. Qed.

Example tauto_1 :
  forall (P : nat -> Prop) (n : nat),
    n = 0 \/ P n -> n <> 0 -> P n.
Proof. auto. tauto. Qed.

(** [tauto] to taktyka, która potrafi udowodnić każdą tautologię
    konstruktywnego rachunku zdań. Taktyka ta radzi sobie także z niektórymi
    nieco bardziej skomplikowanymi celami, w tym takimi, których nie potrafi
    udowodnić [auto]. [tauto] zawodzi, gdy nie potrafi udowodnić celu. *)

Example intuition_0 :
  forall (A : Prop) (P : nat -> Prop),
    A \/ (forall n : nat, ~ A -> P n) -> forall n : nat, ~ ~ (A \/ P n).
Proof.
  Fail tauto. intuition.
Qed.

(** [intuition] to [tauto] na sterydach — potrafi rozwiązać nieco więcej
    celów, a poza tym nigdy nie zawodzi. Jeżeli nie potrafi rozwiązać celu,
    upraszcza go.

    Może też przyjmować argument: [intuition t] najpierw upraszcza cel, a
    później próbuje go rozwiązać taktyką [t]. Tak naprawdę [tauto] jest
    jedynie synonimem dla [intuition fail], zaś samo [intuition] to synonim
    [intuition auto with *], co też tłumaczy, dlaczego [intuition] potrafi
    więcej niż [tauto]. *)

Record and3 (P Q R : Prop) : Prop :=
{
    left : P;
    mid : Q;
    right : R;
}.

Example firstorder_0 :
  forall (B : Prop) (P : nat -> Prop),
    and3 (forall x : nat, P x) B B ->
      and3 (forall y : nat, P y) (P 0) (P 0) \/ B /\ P 0.
Proof.
  Fail tauto.
  intuition.
Restart.
  firstorder.
Qed.

Example firstorder_1 :
  forall (A : Type) (P : A -> Prop),
    (exists x : A, ~ P x) -> ~ forall x : A, P x.
Proof.
  Fail tauto. intuition.
Restart.
  firstorder.
Qed.

(** Jednak nawet [intuition] nie jest w stanie sprostać niektórym prostym
    dla człowieka celom — powyższy przykład pokazuje, że nie potrafi ona
    posługiwać się niestandardowymi spójnikami logicznymi, takimi jak
    potrójna koniunkcja [and3].

    Najpotężniejszą taktyką potrafiącą dowodzić tautologii jest [firstorder].
    Nie tylko rozumie ona niestandardowe spójniki (co i tak nie ma większego
    praktycznego znaczenia), ale też świetnie radzi sobie z kwantyfikatorami.
    Drugi z powyższych przykładów pokazuje, że potrafi ona dowodzić tautologii
    konstruktywnego rachunku predykatów, z którymi problem ma [intuition]. *)

(** **** Ćwiczenie (my_tauto) *)

(** Napisz taktykę [my_tauto], która będzie potrafiła rozwiązać jak najwięcej
    tautologii konstruktywnego rachunku zdań.

    Wskazówka: połącz taktyki z poprzednich ćwiczeń. Przetestuj swoją taktykę
    na ćwiczeniach z rozdziału pierwszego — być może ujawni to problemy, o
    których nie pomyślałeś.

    Nie używaj żadnej zaawansowanej automatyzacji. Użyj jedynie [unfold],
    [intro], [repeat], [match], [destruct], [clear], [exact], [split],
    [specialize] i [apply]. *)

(* begin hide *)
Ltac my_tauto :=
  unfold not in *; repeat
multimatch goal with
    | H : ?P |- ?P => exact H
    | H : False |- _ => destruct H
    | H : True |- _ => clear H
    | |- True => exact I
    | H : _ /\ _ |- _ => destruct H
    | |- _ /\ _ => split
    | H : _ <-> _ |- _ => destruct H
    | |- _ <-> _ => split
    | H : _ \/ _ |- _ => destruct H
    | |- _ \/ _ => (left + right); my_tauto; fail
    | |- _ -> _ => intro
    | H : ?P -> ?Q, H' : ?P |- _ => specialize (H H')
    | H : _ -> _ |- _ => apply H
end.

Section my_tauto.

Hypotheses P Q R S : Prop.

Theorem and_comm : P /\ Q -> Q /\ P.
Proof. my_tauto. Qed.

Theorem or_comm : P \/ Q -> Q \/ P.
Proof. my_tauto. Qed.

Theorem and_assoc : P /\ (Q /\ R) <-> (P /\ Q) /\ R.
Proof. my_tauto. Qed.

Theorem or_assoc : P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof. my_tauto. Qed.

Theorem and_dist_or : P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof. my_tauto. Qed.

Theorem or_dist_and : P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. my_tauto. Qed.

Theorem imp_dist_imp : (P -> Q -> R) <-> ((P -> Q) -> (P -> R)).
Proof. my_tauto. Qed.

Theorem curry : (P /\ Q -> R) -> (P -> Q -> R).
Proof. intros. assert (P /\ Q). my_tauto. my_tauto. Qed.

Theorem uncurry : (P -> Q -> R) -> (P /\ Q -> R).
Proof. my_tauto. Qed.

Theorem deMorgan_1 : ~(P \/ Q) <-> ~P /\ ~Q.
Proof. my_tauto. Qed.

Theorem deMorgan_2 : ~P \/ ~Q -> ~(P /\ Q).
Proof. my_tauto. Qed.

Theorem noncontradiction' : ~(P /\ ~P).
Proof. my_tauto. Qed.

Theorem noncontradiction_v2 : ~(P <-> ~P).
Proof. my_tauto. Qed.

Theorem em_irrefutable : ~~(P \/ ~P).
Proof. my_tauto. Qed.

Theorem and_false_annihilation : P /\ False <-> False.
Proof. my_tauto. Qed.

Theorem or_false_neutral : P \/ False <-> P.
Proof. my_tauto. Qed.

Theorem and_true_neutral : P /\ True <-> P.
Proof. my_tauto. Qed.

Theorem or_true_annihilation : P \/ True <-> True.
Proof. my_tauto. Qed.

Theorem or_imp_and : (P \/ Q -> R) <-> (P -> R) /\ (Q -> R).
Proof. my_tauto. Qed.

Theorem and_not_imp : P /\ ~Q -> ~(P -> Q).
Proof. my_tauto. Qed.

Theorem or_not_imp : ~P \/ Q -> (P -> Q).
Proof. my_tauto. Qed.

Theorem contraposition : (P -> Q) -> (~Q -> ~P).
Proof. my_tauto. Qed.

Theorem absurd : ~P -> P -> Q.
Proof. my_tauto. Qed.

Theorem impl_and : (P -> Q /\ R) -> ((P -> Q) /\ (P -> R)).
Proof. my_tauto. Qed.

End my_tauto.
(* end hide *)

(** * Zmienne egzystencjalne i ich taktyki *)

(* begin hide *)
(** TODO: [eauto], [econstructor], [eexists], [edestruct] i inne *)
(* end hide *)