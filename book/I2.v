(** * I2: Spis przydatnych taktyk *)

(** Stare powiedzenie głosi: nie wymyślaj koła na nowo. Aby uczynić zadość
    duchom przodków, którzy je wymyślili (zarówno koło, jak i powiedzenie),
    w niniejszym rozdziale zapoznamy się z różnymi przydatnymi taktykami,
    które prędzej czy później i tak sami byśmy wymyślili, gdyby zaszła taka
    potrzeba.

    Aby jednak nie popaść w inny grzech i nie posługiwać się czarami, których
    nie rozumiemy, część z poniżej omówionych taktyk zaimplementujemy jako
    ćwiczenie.

    Omówimy kolejno:
    - taktykę [refine]
    - drobne taktyki służące głównie do kontrolowania tego, co dzieje się
      w kontekście
    - "średnie" taktyki, wcielające w życie pewien konkretny sposób
      rozumowania
    - taktyki służące do rozumowania na temat relacji równoważności
    - taktyki służące do przeprowadzania obliczeń
    - procedury decyzyjne
    - ogólne taktyki służące do automatyzacji *)

(** Uwaga: przykłady użycia taktyk, których reimplementacja będzie
    ćwiczeniem, zostały połączone z testami w ćwiczeniach żeby nie pisać dwa
    razy tego samego. *)

(** * [refine] — matka wszystkich taktyk *)

(** Fama głosi, że w zamierzchłych czasach, gdy nie było jeszcze taktyk,
    a światem Coqa rządził Chaos (objawiający się dowodzeniem przez ręczne
    wpisywanie termów), jeden z Coqowych bogów imieniem He-fait-le-stos, w
    przebłysku kreatywnego geniuszu wymyślił dedukcję naturalną i stworzył
    pierwszą taktykę, której nadał imię [refine]. Pomysł przyjał się i od
    tej pory Coqowi bogowie poczęli używać jej do tworzenia coraz to innych
    taktyk. Tak [refine] stała się matką wszystkich taktyk.

    Oczywiście legenda ta jest nieprawdziwa — deduckcję naturalną wymyślił
    Gerhard Gentzen, a podstawowe taktyki są zaimplementowane w Ocamlu. Nie
    umniejsza to jednak mocy taktyki [refine]. Jej działanie podobne jest
    do taktyki [exact], z tym że term będący jej argumentem może też zawierać
    dziury [_]. Jeżeli naszym celem jest [G], to taktyka [refine g] rozwiązuje
    cel, jeżeli [g] jest termem typu [G], i generuje taką ilość podcelów, ile
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
  intros P Q. intro H. destruct H as [p q]. split.
    exact q.
    exact p.
Qed.

(** W tym przykładzie chcemy pokazać przemienność konunkcji. Ponieważ nasz
    cel jest kwantyfikacją uniwersalną, jego dowodem musi być jakaś funkcja
    zależna. Funkcję tę konstruujemy taktyką [refine (fun P Q : Prop => _)].
    Nie podajemy jednak ciała funkcji, zastępując je dzurą [_], bo chcemy
    podać je później. W związku z tym nasz obecny cel zostaje rozwiązany, a
    w zamian dostajemy nowy cel postaci [P /\ Q -> Q /\ P], gdyż takiego
    typu jest ciało naszej funkcji. To jednak nie wszystko: w kontekście
    pojawiają się [P Q : Prop]. Wynika to z tego, że [P] i [Q] mogą zostać
    użyte w definicji ciała naszej funkcji.

    Jako, że naszym celem jest implikacja, jej dowodem musi być funkcja.
    Taktyka [refine (fun H => match H with | conj p q => _ end)] pozwala
    nam tę funkcję skonstruować. Ciałem naszej funkcji jest dopasowanie
    zawierające dziurę. Wypełnienie jej będzie naszym kolejnym celem. Przy
    jego rozwiązywaniu będziemy mogli skorzystać z [H], [p] i [q]. Pierwsza
    z tych hipotez pochodzi o wiązania [fun H => ...], zaś [p] i [q] znajdą
    się w kontekście dzięki temu, że zostały związane podczas dopasowania
    [conj p q].

    Teraz naszym celem jest [Q /\ P]. Ponieważ dowody koniunkcji są postaci
    [conj l r], gdzie [l] jest dowodem pierwszego członu, a [r] drugiego,
    używamy taktyki [refine (conj _ _)], by osobno skonstruować oba człony.
    Tym razem nasz proofterm zawiera dwie dziury, więc wygenerowane zostaną
    dwa podcele. Obydwa zachodzą na mocy założenia, a rozwiązujemy je także
    za pomocą [refine].

    Powyższy przykład pokazuje, że [refine] potrafi zastąpić cała gamę
    przeróżnych taktyk, które dotychczas uważaliśmy za podstawowe: [intros],
    [intro], [destruct], [split] oraz [exact]. Określenie "matka wszystkich
    taktyk" wydaje się całkiem uzasadnione. *)

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

(** **** Ćwiczenie (my_intro) *)

(** Zaimplementuj taktykę [my_intro1], która działa tak, jak [intro], czyli
    próbuje wprowadzić do kontekstu zmienną o domyślnej nazwie. Zaimplementuj
    też taktykę [my_intro2 x], która działa tak jak [intro x], czyli próbuje
    wprowadzić do kontekstu zmienną o nazwie [x]. Użyj taktyki [refine].

    Bonus: przeczytaj dokumentację na temat notacji dla taktyk (komenda
    [Tactic Notation]) i napisz taktykę [my_intro], która działa tak jak
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

(** Napisz taktykę [my_apply H], która działa tak jak [apply H]. Użyj taktyki
    [refine]. *)

(* begin hide *)
Ltac my_apply H := refine (H _).
(* end hide *)

Example my_apply_0 :
  forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  my_intro P. my_intro Q. my_intro p. my_intro H.
  my_apply H. my_exact p.
Qed.

(** **** Ćwiczenie (taktyki dla konstruktorów 1) *)

(** Napisz taktyki:
    - [my_split], która działa tak samo jak [split]
    - [my_left] i [my_right], które działają tak jak [left] i [right]
    - [my_exists], która działa tak samo jak [exists] *)

(** Użyj taktyki [refine]. *)

(* begin hide *)
Ltac my_split := refine (conj _ _).
Ltac my_left := refine (or_introl _).
Ltac my_right := refine (or_intror _).
Ltac my_exists n := refine (ex_intro _ n _).
(* end hide *)

Example my_split_0 :
  forall P Q : Prop, P -> Q -> P /\ Q.
Proof.
  my_intro P; my_intro Q; my_intro p; my_intro q.
  my_split.
    my_exact p.
    my_exact q.
Qed.

Example my_left_right_0 :
  forall P : Prop, P -> P \/ P.
Proof.
  my_intro P; my_intro p. my_left. my_exact p.
Restart.
  my_intro P; my_intro p. my_right. my_exact p.
Qed.

Example my_exists_0 :
  exists n : nat, n = 42.
Proof.
  my_exists 42. reflexivity.
Qed.

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
    porządek w kontekście. Można używać jej na nastepujące sposoby:
    - [clear x] usuwa [x] z kontekstu. Jeżeli [x] nie ma w kontekście lub są
      w nim jakieś rzeczy zależne od [x], taktyka zawodzi. Można usunąć wiele
      rzeczy na raz: [clear x_1 ... x_N].
    - [clear -x] usuwa z kontekstu wszystko poza [x].
    - [clear dependent x] usuwa z kontekstu [x] i wszystkie rzeczy, które od
      niego zależą. Taktyka ta zawodzi jedynie gdy [x] nie ma w kontekście.
    - [clear] usuwa z kontekstu absolutnie wszystko. Serdecznie nie polecam.
    - [clearbody x] usuwa definicję [x] (jeżeli [x] jakąś posiada). *)

(** **** Ćwiczenie (tru) *)

(** Napisz taktykę [tru], która czyści kontekst z dowodów na [True] oraz
    potrafi udowodnić cel [True].

    Dla przykładu, taktyka ta powinna przekształcać kontekst
    [a, b, c : True, p : P |- _] w [p : P |- _]. *)

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

(** Napisz taktykę [even], która potrafi udowodnić poniższy cel. *)

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

(** **** Ćwiczenie (my_destruct_and) *)

(** Napisz taktykę [my_destruct H p q], która działa jak [destruct H as [p q]],
    gdzie [H] jest dowodem koniunkcji. Użyj taktyk [refine] i [clear].

    Bonus 1: zaimplementuj taktykę [my_destruct_and H], która działa tak jak
    [destruct H], gdy [H] jest dowodem koniunkcji.

    Bonus 2: zastanów się, jak (albo czy) można zaimplementować taktykę
    [destruct x], gdzie [x] jest dowolnego typu induktywnego. *)

(* begin hide *)
Ltac my_destruct_and_named H p q := refine (
match H with
    | conj p q => _
end); clear H.

Ltac my_destruct_and_unnamed H :=
  let p := fresh in let q := fresh in my_destruct_and_named H p q.

Tactic Notation "my_destruct_and" ident(H) ident(p) ident(q) :=
  my_destruct_and_named H p q.
Tactic Notation "my_destruct_and" ident(H) :=
  my_destruct_and_unnamed H.
(* end hide *)

Example my_destruct_and_0 :
  forall P Q : Prop, P /\ Q -> P.
Proof.
  my_intro P; my_intro Q; my_intro H.
  my_destruct_and H p q. my_exact p.
Restart.
  my_intro P; my_intro Q; my_intro H.
  my_destruct_and H. my_exact H0.
Qed.

(** ** [fold] *)

(** [fold] to taktyka służąca do zwijania definicji. Jej działanie jest
    odwrotne do działania taktyki [unfold]. Niestety, z nieznanych mi
    bliżej powodów bardzo często jest ona nieskuteczna. *)

(** **** Ćwiczenie (my_fold) *)

(** Napisz taktykę [my_fold x], która działa tak jak [fold x], tj. zastępuje
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

(** ** [move] *)

Example move_0 :
  forall P Q R S T : Prop, P /\ Q /\ R /\ S /\ T -> T.
Proof.
  destruct 1 as [p [q [r [s t]]]].
  move p after t.
  move p before s.
  move p at top.
  move p at bottom.
Abort.

(** [move] to taktyka służąca do zmieniania kolejności obiektów w kontekście.
    Jej działanie jest tak ewidentnie oczywiste, ż nie ma zbytniego sensu,
    aby je opisywać. *)

(** **** Ćwiczenie *)

(** Przeczytaj dokładny opis działania taktyki [move] w manualu. *)

(** ** [pose] i [remember] *)

Goal 2 + 2 = 4.
Proof.
  intros.
  pose (a := 2 + 2).
  remember (2 + 2) as b.
Abort.

(** Taktyka [pose (x := t)] dodaje do kontekstu zmienną [x] (pod warunkiem,
    że nazwa ta nie jest zajęta), która zostaje zdefiniowana za pomocą termu
    [t].

    Taktyka [remember t as x] zastępuje wszystkie wystąpienia termu [t]
    w kontekście zmienną [x] (pod warunkiem, że nazwa ta nie jest zajęta) i
    dodaje do kontekstu równanie postaci [x = t].

    W powyższym przykładzie działają one następująco: [pose (a := 2 + 2)]
    dodaje do kontekstu wiązanie [a := 2 + 2], zaś [remember (2 + 2) as b]
    dodaje do kontekstu równanie [Heqb : b = 2 + 2] i zastępuje przez [b]
    wszystkie wystąpienia [2 + 2] — także to w definicji [a].

    Taktyki te przydają się w tak wielu różnych sytuacjach, że nie ma co
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
    nie można zapisać za pomocą komend [Qed] ani [Defined], a jedynie za
    pomocą komendy [Admitted], która oszukańczo udowodnione twierdzenie
    przekształca w aksjomat.

    W CoqIDE oszustwo jest dobrze widoczne, gdyż zarówno taktyka [admit]
    jak i komenda [Admitted] podświetlają się na żółto, a nie na zielono,
    tak jak prawdziwe dowody. Wyświetlenie [Print]em dowodu zakończonego
    komendą [Admitted] również pokazuje, że ma on status aksjomatu.

    Na koniec zauważmy, że komendy [Admitted] możemy użyć również bez
    wczesniejszego użycia taktyki [admit]. Różnica między tymi dwoma bytami
    jest taka, że taktyka [admit] służy do "udowodnienia" pojedynczego celu,
    a komenda [Admitted] — całego twierdzenia. *)

(** * Średnie taktyki *)

(** ** [case_eq] *)

(** [case_eq] to taktyka podobna do taktyki [destruct], ale nieco mądrzejsza,
    gdyż nie zdarza jej się "zapominać", jaka była struktura rozbitego przez
    nią termu. *)

Goal
  forall n : nat, n + n = 42.
Proof.
  intros. destruct (n + n).
Restart.
  intros. case_eq (n + n); intro.
Abort.

(** Różnice między [destruct] i [case_eq] dobrze ilustruje powyższy przykład.
    [destruct] nadaje się jedynie do rozbijania termów, które są zmiennymi.
    Jeżeli rozbijemy coś, co nie jest zmienną (np. term [n + n]), to utracimy
    część informacji na jego temat. [case_eq] potrafi rozbijać dowolne termy,
    gdyż poza samym rozbiciem dodaje też do celu dodatkową hipotezę, która
    zawiera równanie "pamiętające" informacje o rozbitym termie, o których
    zwykły [destruct] zapomina. *)

(** **** Ćwiczenie (my_case_eq) *)

(** Napisz taktykę [my_case_eq t Heq], która działa tak jak [case_eq t], ale
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
    da, a potem próbuje znaleźć sprzeczność. Potrafi rozpoznawać hipotezy
    takie jak [False], [x <> x], [~ True]. Potrafi też znaleźć dwie hipotezy,
    które są ze sobą ewidentnie sprzeczne, np. [P] oraz [~ P]. Nie potrafi
    jednak wykrywać lepiej ukrytych sprzeczności, np. nie jest w stanie
    odróżnić [true] od [false]. *)

(** **** Ćwiczenie (my_contradiction) *)

(** Napisz taktykę [my_contradiction], która działa tak jak standardowa
    taktyka [contradiction], a do tego jest w stanie udowodnić dowolny
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

(** Innymi taktykami, które mogą przydać się przy rozumowaniach przez
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
    [apply or_intro] (czyli jak taktyka [left]), gdyż zaaplikowanie tego
    konstruktora nie zawodzi.

    W trzecim przykładzie [constructor; assumption] działa tak: najpierw
    aplikowany jest konstruktor [or_introl], ale wtedy [assumption] zawodzi,
    więc następuje nawrót i aplikowany jest konstruktor [or_intror], a wtedy
    [assumption] rozwiązuje cel. *)

(** **** Ćwiczenie (taktyki dla konstruktorów 2) *)

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
    rozbić bardzo skomplikowane hipotezy. [decompose [t_1 ... t_n] H] rozbija
    rekurencyjnie hipotezę [H] tak długo, jak jej typem jest jeden z typów
    [t_i]. W powyższym przykładzie [decompose [and ex] H] najpierw rozbija [H],
    gdyż jest ona koniunkcją, a następnie rozbija powstałe z niej hipotezy,
    gdyż są one kwantyfikacjami egzystencjalnymi ("exists" jest notacją dla
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
    bezimienną hipotezę typu [P /\ Q /\ R], która natychmiast rozbijamy za
    pomocą wzorca [p [q r]].

    W kolejnym przykładzie mamy już nowości: wzorzec [?] służy do nadania
    zmiennej domyślnej nazwy. W naszym przypadku wprowadzone do kontekstu
    zdanie zostaje nazwane [P], gdyż taką nazwę nosi w kwantyfikatorze,
    gdy jest jeszcze w celu.

    Wzorzec [?P] służy do nadania zmiennej domyślnej nazwy zaczynając się
    od tego, co następuje po znaku [?]. W naszym przypadku do konteksu
    wprowadzona zostaje zmienna [P0], gdyż żądamy nazwy zaczynającej się
    od "P", ale samo "P" jest już zajęte. Widzimy też wzorzec [(p, (p0, q))],
    który służy do rozbicia hipotezy. Wzorce tego rodzaju działają tak samo
    jak wzorce w kwadratowych nawiasach, ale możemy używać ich tylko na
    elementach typu induktywnego z jednym konstruktorem.

    Wzorzec [*] wprowadza do kontekstu wszystkie zmienne kwantyfikowane
    uniwersalnie i zatrzymuje sie na pierwszej nie-zależnej hipotezie. W
    naszym przykładzie uniwersalnie kwantyfikowane są [P], [Q], [R] i [S],
    więc zostają wprowadzane, ale [P /\ Q /\ R] nie jest już kwantyfikowane
    uniwersalnie — jest przesłanką implikacji — więc nie zostaje wprowadzone.

    Wzorzec [**] wprowadza do kontekstu wszystko. Wobec tego [intros **] jest
    synonimem [intros]. Mimo tego nie jest on bezużyteczny — możemy użyć go
    po innych wzorcach, kiedy nie chcemy już więcej nazywać/rozbijać naszych
    zmiennych. Wtedy dużo szybciej napisać [**] niż [; intros]. W naszym
    przypadku chcemy nazwać jedynie pierwsze dwie zmienne, a resztę wrzucamy
    do kontekstu jak leci.

    Wzorzec [_] pozwala pozbyć się zmiennej lub hipotezy. Taktyka [intros _]
    jest wobec tego równoważna [intro H; clear H] (przy założeniu, że [H]
    jest wolne), ale dużo bardziej zwięzła w zapisie. Nie możemy jednak
    usunąć zmiennych lub hipotez, od których zależą inne zmienne lub hipotezy.
    W naszym przedostatnim przykładzie bez problemu usuwamy hipotezę [P /\
    Q /\ R], gdyż żaden term od niej nie zależy. Jednak w ostatnim przykładzie
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
    równanie, przepisać je i natychmiast się go pozbyć. Wobec tego taktyka
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
    koniunkjcę wywnioskować. Taki właśnie efekt ma wzorzec [= p1 p2] —
    dodaje on nam do kontekstu hipotezy [p1 : a = c] oraz [p2 : b = d]. *)

Example intros_4 :
  forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros until 2. intro p. apply H in p. apply H0 in p.
Restart.
  intros until 2. intros p %H %H0.
Abort.

(** Taktyka [intros until x] wprowadza do kontekstu wszystkie zmienne jak
    leci dopóki nie natknie się na taką, która nazywa się "x". Taktyka
    [intros until n], gdzie [n] jest liczbą, wprowadza do kontekstu wszyskto
    jak leci aż do n-tej nie-zależnej hipotezy (tj. przesłanki implikacji).
    W naszym przykładzie mamy 3 przesłanki implikacji: [(P -> Q)], [(Q -> R)]
    i [P], więc taktyka [intros until 2] wprowadza do kontekstu dwie pierwsze
    z nich oraz wszystko, co jest poprzedza.

    Wzorzec [x %H_1 ... %H_n] wprowadza do kontekstu zmienną [x], a następnie
    aplikuje do niej po kolei hipotezy [H_1], ..., [H_n]. Taki sam efekt można
    osiągnąć ręcznie za pomocą taktyki [intro x; apply H_1 in x; ... apply H_n
    in x]. *)

(** **** Ćwiczenie (intros) *)

(** Taktyka [intros] ma jeszcze trochę różnych wariantów. Poczytaj o nich
    w manualu. *)

(** ** [fix] *)

(** [fix] to taktyka służąca do dowodzenia bezpośrednio przez rekursję. W
    związku z tym nadeszła dobra pora, żeby pokazać wszystkie możliwe sposoby
    na użycie rekursji w Coqu. Żeby dużo nie pisać, przyjrzyjmy się przykładom:
    zdefiniujemy/udowodnimy regułę indukcyjną dla liczb naturalnych, którą
    powinieneś znać jak własną kieszeń (a jeżeli nie, to marsz robić zadania
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
    zamiast ręcznie wpisywać term, definiujemy naszą regułę za pomocą taktyk.
    Sposób ten jest prawie zawsze (dużo) dłuższy niż poprzedni, ale jego
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
    próbuje wywołać się rekurencyjnie na tym samym argumencie, na którym sam
    został wywołany. Nie jest więc legalny.

    Jeżeli z wywołaniami rekurencyjnymi jest wszystko ok, to komenda [Guarded]
    wyświetla przyjazny komunikat. Tak właśnie jest, gdy używamy jej po raz
    drugi — tym razem wywołanie rekurencyjne odbywa się na [n'], które jest
    podtermem [n]. *)

Definition nat_ind_fix_tac :
  forall (P : nat -> Prop) (H0 : P 0)
    (HS : forall n : nat, P n -> P (S n)) (n : nat), P n.
Proof.
  Show Proof.
  (* ===> ?Goal *)
  fix IH 4.
  Show Proof.
  (* ===> (fix nat_ind_fix_tac
               (P : nat -> Prop) (H0 : P 0)
               (HS : forall n : nat, P n -> P (S n))
               (n : nat) {struct n} : P n := ... *)
 destruct n as [| n'].
    apply H0.
    apply HS. apply IH; assumption.
Defined.

(** Taktyki [fix] możemy użyć w dowolnym momencie, aby rozpocząć dowodzenie/
    definiowanie bezpośrednio przez rekursję. Jej argumentami są nazwa, którą
    chcemy nadać hipotezie indukcyjnej oraz numer argument głównego. W
    powyższym przykładzie chcemy robić rekursję po [n], który jest czwarty
    z kolei (po [P], [H0] i [HS]).

    Komenda [Show Proof] pozwala nam odkryć, że użycie taktyki [fix] w
    trybie dowodzenia odpowiada po prostu użyciu konstruktu [fix] lub
    komendy [Fixpoint].

    Taktyka [fix] jest bardzo prymitywna i prawie nigdy nie jest używana,
    tak samo jak konstrukt [fix] (najbardziej poręczne są sposoby, które
    widzieliśmy w przykladach 2 i 3), ale była dobrym pretekstem, żeby
    omówić wszystkie sposoby użycia rekursji w jednym miejscu. *)

(** ** [functional induction] i [functional inversion] *)

(** Taktyki [functional induction] i [functional inversion] są związane z
    pojęciem indukcji funkcyjnej. Dość szczegółowy opis tej pierwszej jest
    w notatkach na seminarium: https://zeimer.github.io/Seminar.html##lab247

    Drugą z nich póki co pominiemy. Kiedyś z pewnością napiszę coś więcej
    o indukcji funkcyjnej lub chociaż przetłumaczę zalinkowane notatki na
    polski. *)

(** ** [generalize dependent] *)

(** [generalize dependent] to taktyka będąca przeciwieństwem [intro] — dzięki
    niej możemy przerzucić rzeczy znajdujące się w kontekście z powrotem do
    kontekstu. Nieformalnie odpowiada ona sposobowi rozumowania: aby pokazać,
    że cel zachodzi dla pewnego konkretnego [x], wystarczy czy pokazać, że
    zachodzi dla dowolnego [x].

    W rozumowaniu tym z twierdzenia bardziej ogólnego wyciągamy wniosek, że
    zachodzi twierdzenie bardziej szczegółowe. Nazwa [generalize] bierze się
    stąd, że w dedukcji naturalnej nasze rozumowania przeprowadzamy "od tyłu".
    Człon "dependent" bierze się stąd, że żeby zgeneralizować [x], musimy
    najpierw zgeneralizować wszystkie obiekty, które są od niego zależne. Na
    szczęście taktyka [generalize dependent] robi to za nas. *)

Example generalize_dependent_0 :
  forall n m : nat, n = m -> m = n.
Proof.
  intros. generalize dependent n.
Abort.

(** Użycie [intros] wprowadza do kontekstu [n], [m] i [H]. [generalize
    dependent n] przenosi [n] z powrotem do celu, ale wymaga to, aby do
    celu przenieść również [H], gdyż typ [H], czyli [n = m], zależy od [n]. *)

(** **** Ćwiczenie (generalize i revert) *)

(** [generalize dependent] jest wariantem taktyki [generalize]. Taktyką o
    niemal identycznym działaniu jest [revert dependent], wariant taktyki
    [revert]. Przeczytaj dokumentację [generalize] i [revert] w manualu i
    sprawdź, jak działają. *)

(** **** Ćwiczenie (my_rec) *)

(** Zaimplementuj taktykę [rec x], która będzie pomagała przy dowodzeniu
    bezpośrednio przez rekursję po [x]. Taktyka [rec x] ma działać jak
    [fix IH n; destruct x], gdzie [n] to pozycja argumentu [x] w celu. Twoja
    taktyka powinna działać tak, żeby poniższy dowód zadziałał bez potrzeby
    wprowadzania modyfikacji.

    Wskazówka: połącz taktyki [fix], [intros], [generalize dependent] i
    [destruct]. *)

(* begin hide *)
Ltac rec x :=
  intros until x; generalize dependent x; fix IH 1; destruct x.
(* end hide *)

Lemma plus_comm_rec :
  forall n : nat, n + 1 = S n.
Proof.
  rec n.
    reflexivity.
    cbn. f_equal. rewrite IH. reflexivity.
Qed.

(** * Taktyki dla równości i równoważności *)

(** ** [reflexivity], [symmetry] i [transitivity] *)

Require Import Arith.

Example reflexivity_0 :
  forall n : nat, n <= n.
Proof. reflexivity. Qed.

(** Znasz już taktykę [reflexivity]. Mogłoby się wydawać, że służy ona do
    udowadniania celów postaci [x = x] i jest w zasadzie równoważna taktyce
    [apply eq_refl], ale nie jest tak. Taktyka [reflexivity] potrafi rozwiązać
    każdy cel postaci [R x y], gdzie [R] jest relacją zwrotną, a [x] i [y] są
    konwertowalne (oczywiście pod warunkiem, że udowodnimy wcześniej, że [R]
    faktycznie jest zwrotna; w powyższym przykładzie odpowiedni fakt został
    zaimportowany z modułu [Arith]).

    Żeby zilustrować ten fakt, zdefiniujmy nową relację zwrotną i zobaczmy,
    jak użyć taktyki [reflexivity] do radzenia sobie z nią. *)

Definition eq_ext {A B : Type} (f g : A -> B) : Prop :=
  forall x : A, f x = g x.

(** W tym celu definiujemy relację [eq_ext], która głosi, że funkcja
    [f : A -> B] jest w relacji z funkcją [g : A -> B], jeżeli [f x]
    jest równe [g x] dla dowolnego [x : A]. *)

Require Import RelationClasses.

(** Moduł [RelationClasses] zawiera definicję zwrotności [Reflexive], z której
    korzysta taktyka [reflexivity]. Jeżeli udowodnimy odpowiednie twierdzenie,
    będziemy mogli używać taktyki [reflexivity] z relacją [eq_ext]. *)

Instance Reflexive_eq_ext :
  forall A B : Type, Reflexive (@eq_ext A B).
Proof.
  unfold Reflexive, eq_ext. intros A B f x. reflexivity.
Defined.

(** A oto i rzeczone twierdzenie oraz jego dowód. Zauważmy, że taktyki
    [reflexivity] nie używamy tutaj z relacją [eq_ext], a z relacją [=],
    gdyż używamy jej na celu postaci [f x = f x].

    Uwaga: żeby taktyka [reflexivity] "widziała" ten dowód, musimy skorzystać
    ze słowa kluczowego [#[refine]
Instance] zamiast z [Theorem] lub [Lemma]. *)

Example reflexivity_1 :
  eq_ext (fun _ : nat => 42) (fun _ : nat => 21 + 21).
Proof. reflexivity. Defined.

(** Voil� ! Od teraz możemy używać taktyki [reflexivity] z relacją [eq_ext].

    Są jeszcze dwie taktyki, które czasem przydają się przy dowodzeniu
    równości (oraz równoważności). *)

Example symmetry_transitivity_0 :
  forall (A : Type) (x y z : nat), x = y -> y = z -> z = x.
Proof.
  intros. symmetry. transitivity y.
    assumption.
    assumption.
Qed.

(** Mogłoby się wydawać, że taktyka [symmetry] zamienia cel postaci [x = y]
    na [y = x], zaś taktyka [transitivity y] rozwiązuje cel postaci [x = z]
    i generuje w zamian dwa cele postaci [x = y] i [y = z]. Rzeczywistość
    jest jednak bardziej hojna: podobnie jak w przypadku [reflexivity],
    taktyki te działają z dowolnymi relacjami symetrycznymi i przechodnimi. *)

Instance Symmetric_eq_ext :
  forall A B : Type, Symmetric (@eq_ext A B).
Proof.
  unfold Symmetric, eq_ext. intros A B f g H x. symmetry. apply H.
Defined.

Instance Transitive_eq_ext :
  forall A B : Type, Transitive (@eq_ext A B).
Proof.
  unfold Transitive, eq_ext. intros A B f g h H H' x.
  transitivity (g x); [apply H | apply H'].
Defined.

(** Użycie w dowodach taktyk [symmetry] i [transitivity] jest legalne, gdyż
    nie używamy ich z relacją [eq_ext], a z relacją [=]. *)

Example symmetry_transitivity_1 :
  forall (A B : Type) (f g h : A -> B),
    eq_ext f g -> eq_ext g h -> eq_ext h f.
Proof.
  intros. symmetry. transitivity g.
    assumption.
    assumption.
Qed.

(** Dzięki powyższym twierdzeniom możemy teraz posługiwać się taktykami
    [symmetry] i [transitivity] dowodząc faktów na temat relacji [eq_ext].
    To jednak wciąż nie wyczerpuje naszego arsenału taktyk do radzenia sobie
    z relacjami równoważności. *)

(** ** [f_equal] *)

Check f_equal.
(* ===> f_equal : forall (A B : Type) (f : A -> B) (x y : A),
                    x = y -> f x = f y *)

(** [f_equal] to jedna z podstawowych właściwości relacji [eq], która głosi,
    że wszystkie funkcje zachowują równość. Innymi słowy: aby pokazać, że
    wartości zwracane przez funkcję są równe, wystarczy pokazać, że argumenty
    są równe. Ten sposób rozumowania, choć nie jest ani jedyny, ani skuteczny
    na wszystkie cele postaci [f x = f y], jest wystarczająco częsty, aby mieć
    swoją własną taktykę, którą zresztą powinieneś już dobrze znać — jest nią
    [f_equal].

    Taktyka ta sprowadza się w zasadzie do jak najsprytniejszego aplikowania
    faktu [f_equal]. Nie potrafi ona wprowadzać zmiennych do kontekstu, a z
    wygenerowanych przez siebie podcelów rozwiązuje jedynie te postaci [x = x],
    ale nie potrafi rozwiązać tych, które zachodzą na mocy założenia. *)

(** **** Ćwiczenie (my_f_equal) *)

(** Napisz taktykę [my_f_equal], która działa jak [f_equal] na sterydach, tj.
    poza standardową funkcjonalnością [f_equal] potrafi też wprowadzać zmienne
    do kontekstu oraz rozwiązywać cele prawdziwe na mocy założenia.

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

(** Przyjrzyj się definicjom [f_equal], [id], [compose], [eq_sym], [eq_trans],
    a następnie udowodnij poniższe lematy. Ich sens na razie niech pozostanie
    ukryty — kiedyś być może napiszę coś na ten temat. Jeżeli intrygują cię
    one, przyjrzyj się książce https://homotopytypetheory.org/book/ *)

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

(** W naszym przykładzie posłużymy się relacją [len_eq], która głosi, że
    dwie listy są w relacji gdy mają taką samą długość. *)

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
    dowolne, albowiem wszystkie funkcje zachowują równość. Analogicznie
    taktyka [f_equiv] działa na celach postaci [R (f x) (f y)], gdzie [R]
    jest dowolną relacją, ale tylko pod warunkiem, że funkcja [f] zachowuje
    relację [R].

    Musi tak być, bo gdyby [f] nie zachowywała [R], to mogłoby jednocześnie
    zachodzić [R x y] oraz [~ R (f x) (f y)], a wtedy sposób rozumowania
    analogiczny do tego z twierdzenia [f_equal] byłby niepoprawny.

    Aby taktyka [f_equiv] "widziała", że [f] zachowuje [R], musimy znów
    posłużyć się komendą [Instance] i użyć [Proper], które służy do
    zwięzłego wyrażania, które konkretnie relacje i w jaki sposób zachowuje
    dana funkcja.

    W naszym przypadku będziemy chcieli pokazać, że jeżeli listy [l1] oraz
    [l1'] są w relacji [len_eq] (czyli mają taką samą długość) i podobnie
    dla [l2] oraz [l2'], to wtedy konkatenacja [l1] i [l2] jest w relacji
    [len_eq] z konkatenacją [l1'] i [l2']. Ten właśnie fakt jest wyrażany
    przez zapis [Proper (@len_eq A ==> @len_eq A ==> @len_eq A) (@app A)].

    Należy też zauważyć, że strzałka [==>] jest jedynie notacją dla tworu
    zwanego [respectful], co możemy łatwo sprawdzić komendą [Locate.] *)

Example f_equiv_0 :
  forall (A B : Type) (f : A -> B) (l1 l1' l2 l2' : list A),
    len_eq l1 l1' -> len_eq l2 l2' ->
      len_eq (l1 ++ l2) (l1' ++ l2').
Proof.
  intros. f_equiv.
    assumption.
    assumption.
Qed.

(** Voil� ! Teraz możemy używać taktyki [f_equiv] z relacją [len_eq] oraz
    funkcją [app] dokładnie tak, jak taktyki [f_equal] z równością oraz
    dowolną funkcją.

    Trzeba przyznać, że próba użycia [f_equiv] z różnymi kombinacjami
    relacji i funkcji może zakończyć się nagłym i niekontrolowanym
    rozmnożeniem lematów mówiących o tym, że funkcje zachowują relacje.
    Niestety, nie ma na to żadnego sposobu — jak przekonaliśmy się wyżej,
    udowodnienie takiego lematu to jedyny sposób, aby upewnić się, że nasz
    sposób rozumowania jest poprawny. *)

(** **** Ćwiczenie (f_equiv_filter) *)

Require Import List.
Import ListNotations.

Definition stupid_id {A : Type} (l : list A) : list A :=
  filter (fun _ => true) l.

(** Oto niezbyt mądry sposób na zapisanie funkcji identycznościowej na
    listach typu [A]. Pokaż, że [stupid_id] zachowuje relację [len_eq],
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

(** ** [rewrite] *)

(** Powinieneś być już nieźle wprawiony w używaniu taktyki [rewrite]. Czas
    najwyższy więc opisać wszystkie jej możliwości.

    Podstawowe wywołanie tej taktyki ma postać [rewrite H], gdzie [H] jest
    typu [forall (x_1 : A_1) ... (x_n : A_n), R t_1 t_2], zaś [R] to [eq]
    lub dowolna relacja równoważności. Przypomnijmy, że relacja równoważności
    to relacja, która jest zwrotna, symetryczna i przechodnia.

    [rewrite H] znajduje pierwszy podterm celu, który pasuje do [t_1] i
    zamienia go na [t_2], generując podcele [A_1], ..., [A_n], z których
    część (a często całość) jest rozwiązywana automatycznie. *)

Check plus_n_Sm.
(* ===> plus_n_Sm :
          forall n m : nat, S (n + m) = n + S m *)

Goal 2 + 3 = 6 -> 4 + 4 = 42.
Proof.
  intro.
  rewrite <- plus_n_Sm.
  rewrite plus_n_Sm.
  rewrite <- plus_n_Sm.
  rewrite -> plus_n_Sm.
  rewrite <- !plus_n_Sm.
  Fail rewrite <- !plus_n_Sm.
  rewrite <- ?plus_n_Sm.
  rewrite 4!plus_n_Sm.
  rewrite <- 3?plus_n_Sm.
  rewrite 2 plus_n_Sm.
Abort.

(** Powyższy skrajnie bezsensowny przykład ilustruje fakt, że działanie
    taktyki [rewrite] możemy zmieniać, poprzedzając hipotezę [H] następującymi
    modyfikatorami:
    - [rewrite -> H] oznacza to samo, co [rewrite H]
    - [rewrite <- H] zamienia pierwsze wystąpienie [t_2] na [t_1], czyli
      przepisuje z prawa na lewo
    - [rewrite ?H] przepisuje [H] 0 lub więcej razy
    - [rewrite n?H] przepisuje [H] co najwyżej n razy
    - [rewrite !H] przepisuje [H] 1 lub więcej razy
    - [rewrite n!H] lub [rewrite n H] przepisuje [H] dokładnie n razy *)

(** Zauważmy, że modyfikator [<-] można łączyć z modyfikatorami określającymi
    ilość przepisań. *)

Lemma rewrite_ex_1 :
  forall n m : nat, 42 = 42 -> S (n + m) = n + S m.
Proof.
  intros. apply plus_n_Sm.
Qed.

Goal 2 + 3 = 6 -> 5 + 5 = 12 -> (4 + 4) + ((5 + 5) + (6 + 6)) = 42.
Proof.
  intros.
  rewrite <- plus_n_Sm, <- plus_n_Sm.
  rewrite <- plus_n_Sm in H.
  rewrite <- plus_n_Sm in * |-.
  rewrite !plus_n_Sm in *.
  rewrite <- rewrite_ex_1. 2: reflexivity.
  rewrite <- rewrite_ex_1 by reflexivity.
Abort.

(** Pozostałe warianty taktyki [rewrite] przedstawiają się następująco:
    - [rewrite H_1, ..., H_n] przepisuje kolejno hipotezy [H_1], ..., [H_n].
      Każdą z hipotez możemy poprzedzić osobnym zestawem modyfikatorów.
    - [rewrite H in H'] przepisuje [H] nie w celu, ale w hipotezie [H']
    - [rewrite H in * |-] przepisuje [H] we wszystkich hipotezach
      różnych od [H]
    - [rewrite H in *] przepisuje [H] we wszystkich hipotezach różnych
      od [H] oraz w celu
    - [rewrite H by tac] działa jak [rewrite H], ale używa taktyki [tac] do
      rozwiązania tych podcelów, które nie mogły zostać rozwiązane
      automatycznie *)

(** Jest jeszcze wariant [rewrite H at n] (wymagający zaimportowania modułu
    [Setoid]), który zamienia n-te (licząc od lewej) wystąpienie [t_1] na
    [t_2]. Zauważmy, że [rewrite H] znaczy to samo, co [rewrite H at 1]. *)

(** * Taktyki dla redukcji i obliczeń (TODO) *)

(** * Procedury decyzyjne *)

(** Procedury decyzyjne to taktyki, które potrafią zupełnie same rozwiązywać
    cele należące do pewnej konkretnej klasy, np. cele dotyczące funkcji
    boolowskich albo nierówności liniowych na liczbach całkowitych. W tym
    podrozdziale omówimy najprzydatniejsze z nich. *)

(** ** [btauto] *)

(** [btauto] to taktyka, która potrafi rozwiązywać równania boolowskie, czyli
    cele postaci [x = y], gdzie [x] i [y] są wyrażeniami mogącymi zawierać
    boolowskie koniunkcje, dysjunkcje, negacje i inne rzeczy (patrz manual).

    Taktykę można zaimportować komendą [Require Import Btauto]. Uwaga: nie
    potrafi ona wprowadzać zmiennych do kontekstu. *)

(** **** Ćwiczenie (my_btauto) *)

(** Napisz następujące taktyki:
    - [my_btauto] — taktyka podobna do [btauto]. Potrafi rozwiązywać cele,
      które są kwantyfikowanymi równaniami na wyrażeniach boolowskich,
      składającymi się z dowolnych funkcji boolowskich (np. [andb], [orb]).
      W przeciwieństwie do [btauto] powinna umieć wprowadzać zmienne do
      kontekstu.
    - [my_btauto_rec] — tak samo jak [my_btauto], ale bez używana
      kombinatora [repeat]. Możesz używać jedynie rekurencji.
    - [my_btauto_iter] — tak samo jak [my_btauto], ale bez używania
      rekurencji. Możesz używać jedynie kombinatora [repeat].
    - [my_btauto_no_intros] — tak samo jak [my_btauto], ale bez używania
      taktyk [intro] oraz [intros]. *)

(** Uwaga: twoja implementacja taktyki [my_btauto] będzie diametralnie różnić
    się od implementacji taktyki [btauto] z biblioteki standardowej. [btauto]
    jest zaimplementowana za pomocą reflekcji. Dowód przez reflekcję omówimy
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

(** [congruece] to taktyka, która potrafi rozwiązywać cele dotyczące
    nieinterpretowanych równości, czyli takie, których prawdziwość zależy
    jedynie od hipotez postaci [x = y] i które można udowodnić ręcznie za
    pomocą mniejszej lub większej ilości [rewrite]'ów. [congruence] potrafi
    też rozwiązywać cele dotyczące konstruktorów. W szczególności wie ona,
    że konstruktory są injektywne i potrafi odróżnić [true] od [false]. *)

(** **** Ćwiczenie (congruence) *)

(** Udowodnij przykłady [congruence_1] i [congruence_2] ręcznie. *)

(** **** Ćwiczenie (discriminate) *)

(** Inną taktyką, która potrafi rozróżniać konstruktory, jest [discriminate].
    Zbadaj, jak działa ta taktyka. Znajdź przykład celu, który [discriminate]
    rozwiązuje, a na którym [congruence] zawodzi. Wskazówka: [congruence]
    niebardzo potrafi odwijać definicje. *)

(* begin hide *)
Definition mytrue := true.

Goal ~ (mytrue = false).
Proof.
  Fail congruence.
  discriminate.
Qed.
(* end hide *)

(** **** Ćwiczenie (injection i simplify_eq) *)

(** Kolejne dwie taktyki do walki z konstruktorami typów induktywnych to
    [injection] i [simplify_eq]. Przeczytaj ich opisy w manualu. Zbadaj,
    czy są one w jakikolwiek sposób przydatne (wskazówka: porównaj je z
    taktykami [inversion] i [congruence]. *)

(** ** [decide equality] *)

Inductive C : Type :=
    | c0 : C
    | c1 : C -> C
    | c2 : C -> C -> C
    | c3 : C -> C -> C -> C.

(** Przyjrzyjmy się powyższemu, dosć enigmatycznemu typowi. Czy posiada on
    rozstrzygalną równość? Odpowiedź jest twierdząca: rozstrzygalną równość
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
Restart.
  induction x; destruct y; try (right; congruence).
    left; trivial.
    destruct (IHx y); firstorder congruence.
(*    repeat match goal with
        | H : forall _, {_} + {_} |- _ =>
            let H' := fresh "H" in edestruct H as [H' | H']; clear H;
              [rewrite H'; clear H' | idtac]
    end; firstorder (try congruence).*)
    destruct (IHx1 y1), (IHx2 y2); firstorder congruence.
    destruct (IHx1 y1), (IHx2 y2), (IHx3 y3); firstorder congruence.
Restart.
  induction x; destruct y;
  repeat match goal with
      | H : forall _, {_} + {_} |- _ => edestruct H; clear H
      | H : _ = _ |- _ => rewrite H in *; clear H
  end; firstorder congruence.
  Unshelve. all: auto.
Defined.
(* end hide *)

(** Zanim przejdziesz dalej, udowodnij ręcznie powyższe twierdzenie. Przyznasz,
    że dowód nie jest zbyt przyjemny, prawda? Na szczęście nie musimy robić go
    ręcznie. Na ratunek przychodzi nam taktyka [decide equality], która umie
    udowadniać cele postaci [forall x y : T, {x = y} + {x <> y}], gdzie [T]
    spełnia warunki wymienione powyżej. *)

Theorem C_eq_dec' :
  forall x y : C, {x = y} + {x <> y}.
Proof. decide equality. Defined.

(** **** Ćwiczenie *)

(** Pokrewną taktyce [decide equality] jest taktyka [compare]. Przeczytaj
    w manualu, co robi i jak działa. *)

(** ** [omega] *)

(** [omega] to taktyka, która potrafi rozwiązywać cele dotyczące arytmetyki
    Presburgera. Jej szerszy opis można znaleźć w manualu. Na nasze potrzeby
    przez arytmetykę Presburgera możemy rozumieć równania ([=]), nie-równania
    ([<>]) oraz nierówności ([<], [<=], [>], [>=]) na typie [nat], które mogą
    zawierać zmienne, [0], [S], dodawanie i mnożenie przez stałą. Dodatkowo
    zdania tej postaci mogą być połączone spójnikami [/\], [\/], [->] oraz
    [~], ale nie mogą być kwantyfikowane — [omega] nie umie wprowadzać
    zmiennych do kontekstu.

    Uwaga: ta taktyka jest przestarzała, a jej opis znajduje się tutaj tylko
    dlatego, że jak go pisałem, to jeszcze nie była. Nie używaj jej! Zamiast
    [omega] używaj [lia]! *)

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
    tego faktu, liczy sobie 317 linijek długości (po wypisaniu, wklejeniu
    do CoqIDE i usunięciu tego, co do termu nie należy). *)

Lemma filter_length' :
  forall (A : Type) (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l; cbn; try destruct (f a); cbn.
    trivial.
    apply le_n_S. assumption.
    apply le_trans with (length l).
      assumption.
      apply le_S. apply le_n.
Qed.

Print filter_length'.
(* ===> Proofterm o długości 14 linijek. *)

(** Jak widać, ręczny dowód tego faktu daje w wyniku proofterm, który jest
    o ponad 300 linijek krótszy niż ten wyprodukowany przez taktykę [omega].
    Mogłoby się zdawać, że jesteśmy w sytuacji bez wyjścia: albo dowodzimy
    ręcznie, albo prooftermy będą tak wielkie, że nie będziemy mogli ich
    odwijać. *)

(** ** Procedury decyzyjne dla logiki *)

Example tauto_0 :
  forall A B C D : Prop,
    ~ A \/ ~ B \/ ~ C \/ ~ D -> ~ (A /\ B /\ C /\ D).
Proof. tauto. Qed.

Example tauto_1 :
  forall (P : nat -> Prop) (n : nat),
    n = 0 \/ P n -> n <> 0 -> P n.
Proof. auto. tauto. Qed.

(** [tauto] to taktyka, która potrafi udowodnić każdą tautologię
    konstruktywnego rachunku zdań. Taktyka ta radzi sobie także z niektórymi
    nieco bardziej skomplikowanymi celami, w tym takimi, których nie potrafi
    udowodnić [auto]. [tauto] zawodzi, gdy nie potrafi udowodnić celu. *)

Example intuition_0 :
  forall (A : Prop) (P : nat -> Prop),
    A \/ (forall n : nat, ~ A -> P n) -> forall n : nat, ~ ~ (A \/ P n).
Proof.
  Fail tauto. intuition.
Qed.

(** [intuition] to [tauto] na sterydach — potrafi rozwiązać nieco więcej
    celów, a poza tym nigdy nie zawodzi. Jeżeli nie potrafi rozwiązać celu,
    upraszcza go.

    Może też przyjmować argument: [intuition t] najpierw upraszcza cel, a
    później próbuje go rozwiązać taktyką [t]. Tak naprawdę [tauto] jest
    jedynie synonimem dla [intuition fail], zaś samo [intuition] to synonim
    [intuition auto with *], co też tłumaczy, dlaczego [intuition] potrafi
    więcej niż [tauto]. *)

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
    posługiwać się niestandardowymi spójnikami logicznymi, takimi jak
    potrójna koniunkcja [and3].

    Najpotężniejszą taktyką potrafiącą dowodzić tautologii jest [firstorder].
    Nie tylko rozumie ona niestandardowe spójniki (co i tak nie ma większego
    praktycznego znaczenia), ale też świetnie radzi sobie z kwantyfikatorami.
    Drugi z powyższych przykładów pokazuje, że potrafi ona dowodzić tautologii
    konstruktywnego rachunku predykatów, z którymi problem ma [intuition]. *)

(** **** Ćwiczenie (my_tauto) *)

(** Napisz taktykę [my_tauto], która będzie potrafiła rozwiązać jak najwięcej
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

(** * Ogólne taktyki automatyzacyjne *)

(** W tym podrozdziale omówimy pozostałe taktyki przydające się przy
    automatyzacji. Ich cechą wspólną jest rozszerzalność — za pomocą
    specjalnych baz podpowiedzi będziemy mogli nauczyć je radzić sobie
    z każdym celem. *)

(** ** [auto] i [trivial] *)

(** [auto] jest najbardziej ogólną taktyką służącą do automatyzacji. *)

Example auto_ex0 :
  forall (P : Prop), P -> P.
Proof. auto. Qed.

Example auto_ex1 :
  forall A B C D E : Prop,
    (A -> B) -> (B -> C) -> (C -> D) -> (D -> E) -> A -> E.
Proof. auto. Qed.

Example auto_ex2 :
  forall (A : Type) (x : A), x = x.
Proof. auto. Qed.

Example auto_ex3 :
  forall (A : Type) (x y : A), x = y -> y = x.
Proof. auto. Qed.

(** [auto] potrafi używać założeń, aplikować hipotezy i zna podstawowe
    własności równości — całkiem nieźle. Wprawdzie nie wystarczy to do
    udowodnienia żadnego nietrywialnego twierdzenia, ale przyda się z
    pewnością do rozwiązywania prostych podcelów generowanych przez
    inne taktyki. Często spotykanym idiomem jest [t; auto] — "użyj
    taktyki [t] i pozbądź się prostych podcelów za pomocą [auto]". *)

Section auto_ex4.

Parameter P : Prop.
Parameter p : P.

Example auto_ex4 : P.
Proof.
  auto.
Restart.
  auto using p.
Qed.

(** Jak widać na powyższym przykładzie, [auto] nie widzi aksjomatów (ani
    definicji/lematów/twierdzeń etc.), nawet jeżeli zostały zadeklarowane
    dwie linijki wyżej. Tej przykrej sytuacji możemy jednak łatwo zaradzić,
    pisząc [auto using t_1, ..., t_n]. Ten wariant taktyki [auto]
    widzi definicje termów [t_1], ..., [t_n].

    Co jednak w sytuacji, gdy będziemy wielokrotnie chcieli, żeby [auto]
    widziało pewne definicje? Nietrudno wyobrazić sobie ogrom pisaniny,
    którą mogłoby spowodować użycie do tego celu klauzuli [using]. Na
    szczęście możemy temu zaradzić za pomocą podpowiedzi, które bytują
    w specjalnych bazach. *)

Hint Resolve p : my_hint_db.

Example auto_ex4' : P.
Proof. auto with my_hint_db. Qed.

(** Komenda [Hint Resolve ident : db_name] dodaje lemat o nazwie [ident]
    do bazy podpowiedzi o nazwie [db_name]. Dzięki temu taktyka [auto with
    db_1 ... db_n] widzi wszystkie lematy dodane do baz [db_1], ..., [db_n].
    Jeżeli to dla ciebie wciąż zbyt wiele pisania, uszy do góry! *)

Example auto_ex4'' : P.
Proof. auto with *. Qed.

(** Taktyka [auto with *] widzi wszystkie możliwe bazy podpowiedzi. *)

Hint Resolve p.

Example auto_ex4''' : P.
Proof. auto. Qed.

(** Komenda [Hint Resolve ident] dodaje lemat o nazwie [ident] do bazy
    podpowiedzi o nazwie [core]. Taktyka [auto] jest zaś równoważna
    taktyce [auto with core]. Dzięki temu nie musimy pisać już nic ponad
    zwykłe [auto]. *)

End auto_ex4.

(** Tym oto sposobem, używając komendy [Hint Resolve], jesteśmy w stanie
    zaznajomić [auto] z różnej maści lematami i twierdzeniami, które
    udowodniliśmy. Komendy tej możemy używać po każdym lemacie, dzięki
    czemu taktyka [auto] rośnie w siłę w miarę rozwoju naszej teorii. *)

Example auto_ex5 : even 8.
Proof.
  auto.
Restart.
  auto using even0, evenSS.
Qed.

(** Kolejną słabością [auto] jest fakt, że taktyka ta nie potrafi budować
    wartości typów induktywnych. Na szczęście możemy temu zaradzić używając
    klauzuli [using c_1 ... c_n], gdzie [c_1], ..., [c_n] są konstruktorami
    naszego typu, lub dodając je jako podpowiedzi za pomocą komendy [Hint
    Resolve c_1 ... c_n : db_name]. *)

Hint Constructors even.

Example auto_ex5' : even 8.
Proof. auto. Qed.

(** Żeby jednak za dużo nie pisać (wypisanie nazw wszystkich konstruktorów
    mogłoby być bolesne), możemy posłużyć się komendą [Hint Constructors
    I : db_name], która dodaje konstruktory typu induktywnego [I] do bazy
    podpowiedzi [db_name]. *)

Example auto_ex6 : even 10.
Proof.
  auto.
Restart.
  auto 6.
Qed.

(** Kolejnym celem, wobec którego [auto] jest bezsilne, jest [even 10].
    Jak widać, nie wystarczy dodać konstruktorów typu induktywnego jako
    podpowiedzi, żeby wszystko było cacy. Niemoc [auto] wynika ze sposobu
    działania tej taktyki. Wykonuje ona przeszukiwanie w głąb z nawrotami,
    które działa mniej więcej tak:
    - zrób pierwszy lepszy możliwy krok dowodu
    - jeżeli nie da się nic więcej zrobić, a cel nie został udowodniony,
      wykonaj nawrót i spróbuj czegoś innego
    - w przeciwnym wypadku wykonaj następny krok dowodu i powtarzaj
      całą procedurę *)

(** Żeby ograniczyć czas poświęcony na szukanie dowodu, który może być
    potencjalnie bardzo długi, [auto] ogranicza się do wykonania jedynie
    kilku kroków w głąb (domyślnie jest to 5). *)

Print auto_ex5'.
(* ===> evenSS 6 (evenSS 4 (evenSS 2 (evenSS 0 even0)))
        : even 8 *)

Print auto_ex6.
(* ===> evenSS 8 (evenSS 6 (evenSS 4 (evenSS 2 (evenSS 0 even0))))
        : even 10 *)

(** [auto] jest w stanie udowodnić [even 8], gdyż dowód tego faktu wymaga
    jedynie 5 kroków, mianowicie czeterokrotnego zaaplikowania konstruktora
    [evenSS] oraz jednokrotnego zaaplikowania [even0]. Jednak 5 kroków nie
    wystarcza już, by udowodnić [even 10], gdyż tutaj dowód liczy sobie 6
    kroków: 5 użyć [evenSS] oraz 1 użycie [even0].

    Nie wszystko jednak stracone — możemy kontrolować głębokość, na jaką
    [auto] zapuszcza się, poszukując dowodu, piząc [auto n]. Zauważmy, że
    [auto] jest równoważne taktyce [auto 5]. *)

Example auto_ex7 :
  forall (A : Type) (x y z : A), x = y -> y = z -> x = z.
Proof.
  auto.
Restart.
  Fail auto using eq_trans.
Abort.

(** Kolejnym problemem taktyki [auto] jest udowodnienie, że równość jest
    relacją przechodnią. Tym razem jednak problem jest poważniejszy, gdyż
    nie pomaga nawet próba użycia klauzuli [using eq_trans], czyli wskazanie
    [auto] dokładnie tego samego twierdzenia, którego próbujemy dowieść!

    Powód znów jest dość prozaiczny i wynika ze sposobu działania taktyki
    [auto] oraz postaci naszego celu. Otóż konkluzja celu jest postaci
    [x = z], czyli występują w niej zmienne [x] i [z], zaś kwantyfikujemy
    nie tylko po [x] i [z], ale także po [A] i [y].

    Wywnioskowanie, co wstawić za [A] nie stanowi problemu, gdyż musi to
    być typ [x] i [z]. Problemem jest jednak zgadnięcie, co wstawić za [y],
    gdyż w ogólności możliwości może być wiele (nawet nieskończenie wiele).
    Taktyka [auto] działa w ten sposób, że nawet nie próbuje tego zgadywać. *)

Hint Extern 0 =>
match goal with
    | H : ?x = ?y, H' : ?y = ?z |- ?x = ?z => apply (@eq_trans _ x y z)
end : extern_db.

Example auto_ex7 :
  forall (A : Type) (x y z : A), x = y -> y = z -> x = z.
Proof. auto with extern_db. Qed.

(** Jest jednak sposób, żeby uporać się i z tym problemem: jest nim komenda
    [Hint Extern]. Jej ogólna postać to [Hint Extern n pattern => tactic : db].
    W jej wyniku do bazy podpowiedzi [db] zostanie dodana podpowiedź, która
    sprawi, że w dowolnym momencie dowodu taktyka [auto], jeżeli wypróbowała
    już wszystkie podpowiedzi o koszcie mniejszym niż [n] i cel pasuje do
    wzorca [pattern], to spróbuje użyć taktyki [tac].

    W naszym przypadku koszt podpowiedzi wynosi 0, a więc podpowiedź będzie
    odpalana niemal na samym początku dowodu. Wzorzec [pattern] został
    pominięty, a więc [auto] użyje naszej podpowiedzi niezależnie od tego,
    jak wygląda cel. Ostatecznie jeżeli w konktekście będą odpowiednie
    równania, to zaaplikowany zostanie lemat [@eq_trans _ x y z], wobec
    czego wygenerowane zostaną dwa podcele, [x = y] oraz [y = z], które
    [auto] będzie potrafiło rozwiązać już bez naszej pomocy. *)

Hint Extern 0 (?x = ?z) =>
match goal with
    | H : ?x = ?y, H' : ?y = ?z |- _ => apply (@eq_trans _ x y z)
end.

Example auto_ex7' :
  forall (A : Type) (x y z : A), x = y -> y = z -> x = z.
Proof. auto. Qed.

(** A tak wygląda wersja [Hint Extern], w której nie pominięto wzorca
    [pattern]. Jest ona rzecz jasna równoważna z poprzednią.

    Jest to dobry moment, by opisać dokładniej działanie taktyki [auto].
    [auto] najpierw próbuje rozwiązać cel za pomocą taktyki [assumption].
    Jeżeli się to nie powiedzie, to [auto] używa taktyki [intros], a
    następnie dodaje do tymczasowej bazy podpowiedzi wszystkie hipotezy.
    Następnie przeszukuje ona bazę podpowiedzi dopasowując cel do wzorca
    stowarzyszonego z każdą podpowiedzią, zaczynając od podpowiedzi o
    najmniejszym koszcie (podpowiedzi pochodzące od komend [Hint Resolve]
    oraz [Hint Constructors] są skojarzone z pewnymi domyślnymi kosztami
    i wzorcami). Następnie [auto] rekurencyjnie wywołuje się na podcelach
    (chyba, że przekroczona została maksymalna głębokość przeszukiwania —
    wtedy następuje nawrót). *)

Example trivial_ex0 :
  forall (P : Prop), P -> P.
Proof. trivial. Qed.

Example trivial_ex1 :
  forall A B C D E : Prop,
    (A -> B) -> (B -> C) -> (C -> D) -> (D -> E) -> A -> E.
Proof. trivial. Abort.

Example trivial_ex2 :
  forall (A : Type) (x : A), x = x.
Proof. trivial. Qed.

Example trivial_ex3 :
  forall (A : Type) (x y : A), x = y -> y = x.
Proof. trivial. Abort.

Example trivial_ex5 : even 0.
Proof. trivial. Qed.

Example trivial_ex5' : even 8.
Proof. trivial. Abort.

(** Taktyka [trivial], którą już znasz, działa dokładnie tak samo jak [auto],
    ale jest nierekurencyjna. To tłumaczy, dlaczego potrafi ona posługiwać
    się założeniami i zna właciwości równości, ale nie umie używać implikacji
    i nie radzi sobie z celami pokroju [even 8], mimo że potrafi udowodnić
    [even 0]. *)

(** **** Ćwiczenie (auto i trivial) *)

(** Przeczytaj w manualu dokładny opis działania taktyk [auto] oraz [trivial]:
    https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.auto *)

(** ** [autorewrite] i [autounfold] *)

(** [autorewrite] to bardzo pożyteczna taktyka umożliwiająca zautomatyzowanie
    części dowodów opierających się na przepisywaniu.

    Dlaczego tylko części? Zastanówmy się, jak zazwyczaj przebiegają dowody
    przez przepisywanie. W moim odczuciu są dwa rodzaje takich dowodów:
    - dowody pierwszego rodzaju to te, w których wszystkie przepisania mają
      charakter upraszczający i dzięki temu możemy przepisywać zupełnie
      bezmyślnie
    - dowody drugiego rodzaju to te, w których niektóre przepisania nie mają
      charakteru upraszczającego albo muszą zostać wykonane bardzo precyzyjnie.
      W takich przypadkach nie możemy przepisywać bezmyślnie, bo grozi to
      zapętleniem taktyki [rewrite] lub po prostu porażką *)

(** Dowody pierwszego rodzaju ze względu na swoją bezmyślność są dobrymi
    kandydatami do automatyzacji. Właśnie tutaj do gry wkracza taktyka
    [autorewrite]. *)

Section autorewrite_ex.

Variable A : Type.
Variable l1 l2 l3 l4 l5 : list A.

(** Zacznijmy od przykładu (a raczej ćwiczenia): udowodnij poniższe
    twierdzenie. Następnie udowodnij je w jednej linijce. *)

Example autorewrite_intro :
  rev (rev (l1 ++ rev (rev l2 ++ rev l3) ++ rev l4) ++ rev (rev l5)) =
  (rev (rev (rev l5 ++ l1)) ++ (l3 ++ rev (rev l2))) ++ rev l4.
(* begin hide *)
Proof.
  rewrite ?rev_involutive.
  rewrite <- ?app_assoc.
  rewrite ?rev_app_distr.
  rewrite ?rev_involutive.
  rewrite <- ?app_assoc.
  reflexivity.
Restart.
  rewrite ?rev_app_distr, ?rev_involutive, <- ?app_assoc. reflexivity.
Qed.
(* end hide *)

(** Ten dowód nie był zbyt twórczy ani przyjemny, prawda? Wyobraź sobie
    teraz, co by było, gdybyś musiał udowodnić 100 takich twierdzeń (i
    to w czasach, gdy jeszcze nie można było pisać [rewrite ?t_0, ..., ?t_n]).
    Jest to dość ponura wizja. *)

Hint Rewrite rev_app_distr rev_involutive : list_rw.
Hint Rewrite <- app_assoc : list_rw.

Example autorewrite_ex :
  rev (rev (l1 ++ rev (rev l2 ++ rev l3) ++ rev l4) ++ rev (rev l5)) =
  (rev (rev (rev l5 ++ l1)) ++ (l3 ++ rev (rev l2))) ++ rev l4.
Proof.
  autorewrite with list_rw. reflexivity.
Qed.

End autorewrite_ex.

(** Komenda [Hint Rewrite [<-] ident_0 ... ident_n : db_name] dodaje
    podpowiedzi [ident_0], ..., [ident_n] do bazy podpowidzi [db_nam].
    Domyślnie będą one przepisywane z lewa na prawo, chyba że dodamy
    przełącznik [<-] — wtedy wszystkie będą przepisywane z prawa na
    lewo. W szczególności znaczy to, że jeżeli chcemy niektóre lematy
    przepisywać w jedną stronę, a inne w drugą, to musimy komendy
    [Hint Rewrite] użyć dwukrotnie.

    Sama taktyka [autorewrite with db_0 ... db_n] przepisuje lematy ze
    wszystkich baz podpowiedzi [db_0], ..., [db_n] tak długo, jak to
    tylko możliwe (czyli tak długo, jak przepisywanie skutkuje dokonaniem
    postępu).

    Jest kilka ważnych cech, które powinna posiadać baza podpowiedzi:
    - przede wszystkim nie może zawierać tego samego twierdzenia do
      przepisywania w obydwie strony. Jeżeli tak się stanie, taktyka
      [autorewrite] się zapętli, gdyż przepisanie tego twierdzenia w
      jedną lub drugą stronę zawsze będzie możliwe
    - w ogólności, nie może zawierać żadnego zbioru twierdzeń, których
      przepisywanie powoduje zapętlenie
    - baza powinna być deterministyczna, tzn. jedne przepisania nie
      powinny blokować kolejnych
    - wszystkie przepisywania powinny być upraszczające *)

(** Oczywiście dwa ostatnie kryteria nie są zbyt ścisłe — ciężko sprawdzić
    determinizm systemu przepisywania, zaś samo pojęcie "uproszczenia" jest
    bardzo zwodnicze i niejasne. *)

(** **** Ćwiczenie (autorewrite) *)

(** Przeczytaj opis taktyki [autorewrite] w manualu:
    coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.autorewrite *)

Section autounfold_ex.

Definition wut : nat := 1.
Definition wut' : nat := 1.

Hint Unfold wut wut' : wut_db.

Example autounfold_ex : wut = wut'.
Proof.
  autounfold.
  autounfold with wut_db.
Restart.
  auto.
Qed.

(** Na koniec omówimy taktykę [autounfold]. Działa ona na podobnej zasadzie
    jak [autorewrite]. Za pomocą komendy [Hint Unfold] dodajemy definicje do
    do bazy podpowiedzi, dzięki czemu taktyka [autounfold with db_0, ..., db_n]
    potrafi odwinąć wszystkie definicje z baz [db_0], ..., [db_n].

    Jak pokazuje nasz głupi przykład, jest ona średnio użyteczna, gdyż taktyka
    [auto] potrafi (przynajmniej do pewnego stopnia) odwijać definicje. Moim
    zdaniem najlepiej sprawdza się ona w zestawieniu z taktyką [autorewrite]
    i kombinatorem [repeat], gdy potrzebujemy na przemian przepisywać lematy
    i odwijać definicje. *)

End autounfold_ex.

(** **** Ćwiczenie (autounfold) *)

(** Przeczytaj w manualu opis taktyki [autounfold]:
    coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.autounfold *)

(** **** Ćwiczenie (bazy podpowiedzi) *)

(** Przeczytaj w manualu dokładny opis działania systemu baz podpowiedzi
    oraz komend pozwalających go kontrolować:
    coq.inria.fr/refman/proof-engine/tactics.html#controlling-automation *)

(** * Pierścienie, ciała i arytmetyka *)

(** Pierścień (ang. ring) to struktura algebraiczna składająca się z pewnego
    typu A oraz działań + i *, które zachowują się mniej więcej tak, jak
    dodawanie i mnożenie liczb całkowitych. Przykładów jest sporo: liczby
    wymierne i rzeczywiste z dodawaniem i mnożeniem, wartości boolowskie z
    dysjunkcją i koniunkcją oraz wiele innych, których na razie nie wymienię.

    Kiedyś z pewnością napiszę coś na temat algebry oraz pierścieni, ale z
    taktykami do radzenia sobie z nimi możemy zapoznać się już teraz. W Coqu
    dostępne są dwie taktyki do radzenia sobie z pierścieniami: taktyka
    [ring_simplify] potrafi upraszczać wyrażenia w pierścieniach, zaś taktyka
    [ring] potrafi rozwiązywać równania wielomianowe w pierścieniach.

    Ciało (ang. field) to pierścień na sterydach, w którym poza dodawaniem,
    odejmowaniem i mnożeniem jest także dzielenie. Przykładami ciał są
    liczby wymierne oraz liczby rzeczywiste, ale nie liczby naturalne ani
    całkowite (bo dzielenie naturalne/całkowitoliczbowe nie jest odwrotnością
    mnożenia). Je też kiedyś pewnie opiszę.

    W Coqu są 3 taktyki pomagające w walce z ciałami: [field_simplify]
    upraszcza wyrażenia w ciałach, [field_simplify_eq] upraszcza cele,
    które są równaniami w ciałach, zaś [field] rozwiązuje równania w
    ciałach. *)

(** **** Ćwiczenie (pierścienie i ciała) *)

(** Przyczytaj w manualu opis 5 wymienionych wyżej taktyk:
    https://coq.inria.fr/refman/addendum/ring.html *)

(** * Zmienne egzystencjalne i ich taktyki (TODO) *)

(** Napisać o co chodzi ze zmiennymi egzystencjalnymi. Opisać taktykę
    [evar] i wspomnieć o taktykach takich jak [eauto], [econstructor],
    [eexists], [edestruct], [erewrite] etc., a także taktykę [shelve]
    i komendę [Unshelve]. *)

(** * Taktyki do radzenia sobie z typami zależnymi (TODO) *)

(** Opisać taktyki [dependent induction], [dependent inversion],
    [dependent destruction], [dependent rewrite] etc. *)

(** * Dodatkowe ćwiczenia *)

(** **** Ćwiczenie (assert) *)

(** Znasz już taktyki [assert], [cut] i [specialize]. Okazuje się, że dwie
    ostatnie są jedynie wariantami taktyki [assert]. Przeczytaj w manualu
    opis taktyki [assert] i wszystkich jej wariantów. *)

(** **** Ćwiczenie (easy i now) *)

(** Taktykami, których nie miałem nigdy okazji użyć, są [easy] i jej
    wariant [now]. Przeczytaj ich opisy w manualu. Zbadaj, czy są do
    czegokolwiek przydatne oraz czy są wygodne w porównaniu z innymi
    taktykami służącymi do podobnych celów. *)

(** **** Ćwiczenie (inversion_sigma) *)

(** Przeczytaj w manualu o wariantach taktyki [inversion]. Szczególnie
    interesująca wydaje się taktyka [inversion_sigma], która pojawiła
    się w wersji 8.7 Coqa. Zbadaj ją. Wymyśl jakiś przykład jej użycia. *)

(** **** Ćwiczenie (pattern) *)

(** Przypomnijmy, że podstawą wszelkich obliczeń w Coqu jest redkucja
    beta. Redukuje ona aplikację funkcji, np. [(fun n : nat => 2 * n) 42]
    betaredukuje się do [2 * 42]. Jej wykonywanie jest jednym z głównych
    zadań taktyk obliczeniowych.

    Przeciwieństwem redukcji beta jest ekspansja beta. Pozwala ona zamienić
    dowolny term na aplikację jakiejś funkcji do jakiegoś argumentu, np.
    term [2 * 42] można betaekspandować do [(fun n : nat => 2 * n) 42].

    O ile redukcja beta jest trywialna do automatycznego wykonania, o tyle
    ekspansja beta już nie, gdyż występuje tu duża dowolność. Dla przykładu,
    term [2 * 42] można też betaekspandować do [(fun n : nat => n * 42) 2].

    Ekspansję beta implementuje taktyka [pattern]. Rozumowanie za jej pomocą
    nie jest zbyt częstne, ale niemniej jednak kilka razy mi się przydało.
    Przeczytaj opis taktyki [pattern] w manuaulu.

    TODO: być może ćwiczenie to warto byłoby rozszerzyć do pełnoprawnego
    podrozdziału. *)

(** **** Ćwiczenie (arytmetyka) *)

(** Poza taktykami radzącymi sobie z pierścieniami i ciałami jest też wiele
    taktyk do walki z arytmetyką. Poza omówioną już taktyką [omega] są to
    [lia], [nia], [lra], [nra]. Nazwy taktyk można zdekodować w następujący
    sposób:
    - l — linear
    - n — nonlinar
    - i — integer
    - r — real/rational
    - a — arithmetic *)

(** Spróbuj ogarnąć, co one robią:
    https://coq.inria.fr/refman/addendum/micromega.html *)

(** **** Ćwiczenie (wyższa magia) *)

(** Spróbuj ogarnąć, co robią taktyki [nsatz], [psatz] i [fourier]. *)

(** * Inne języki taktyk *)

(** Ltac w pewnym sensie nie jest jedynym językiem taktyk, jakiego możemy
    użyć do dowodzenia w Coqu — są inne. Głównymi konkurentami Ltaca są:
    - Rtac: gmalecha.github.io/reflections/2016/rtac-technical-overview
    - Mtac: plv.mpi-sws.org/mtac/
    - ssreflect:
      https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html
      oraz https://math-comp.github.io/math-comp/ *)

(** Pierwsze dwa, [Rtac] i [Mtac], faktycznie są osobnymi językami taktyk,
    znacznie różniącymi się od Ltaca. Nie będziemy się nimi zajmować,
    gdyż ich droga do praktycznej użyteczności jest jeszcze dość długa.

    ssreflect to nieco inna bajka. Nie jest on w zasadzie osobnym językiem
    taktyk, lecz jest oparty na Ltacu. Różni się on od niego filozofią,
    podstawowym zestawem taktyk i stylem dowodzenia. Od wersji 8.7 Coqa
    język ten jet dostępny w bibliotece standardowej, mimo że nie jest z
    nią w pełni kompatybilny. *)

(** **** Ćwiczenie (ssreflect) *)

(** Najbardziej wartościowym moim zdaniem elementem języka ssreflect jest
    taktyka [rewrite], dużo potężniejsza od tej opisanej w tym rozdziale.
    Jest ona warta uwagi, gdyż:
    - daje jeszcze większą kontrolę nad przepisywaniem, niż standardowa
      taktyka [rewrite]
    - pozwala łączyć kroki przepisywania z odwijaniem definicji i wykonywaniem
      obliczeń, a więc zastępuje taktyki [unfold], [fold], [change], [replace],
      [cbn], [cbn] etc.
    - daje większe możliwości radzenia sobie z generowanymi przez siebie
      podcelami *)

(** Przeczytaj rozdział manuala opisujący język ssreflect. Jeżeli nie
    chce ci się tego robić, zapoznaj się chociaż z jego taktyką [rewrite]. *)

(** * Konkluzja *)

(** W niniejszym rozdziale przyjrzeliśmy się bliżej znacznej części Coqowych
    taktyk. Moje ich opisanie nie jest aż tak kompletne i szczegółowe jak to
    z manuala, ale nadrabia (mam nadzieję) wplecionymi w tekst przykładami i
    zadaniami. Jeżeli jednak uważasz je za upośledzone, nie jesteś jeszcze
    stracony! Alternatywne opisy niektórych taktyk dostępne są też tu:
    - pjreddie.com/coq-tactics/
    - cs.cornell.edu/courses/cs3110/2017fa/a5/coq-tactics-cheatsheet.html
    - typesofnote.com/posts/coq-cheat-sheet.html *)

(** Poznawszy podstawy Ltaca oraz całe zoo przeróżnych taktyk, do zostania
    pełnoprawnym inżynierem dowodu (ang. proof engineer, ukute przez analogię
    do software engineer) brakuje ci jeszcze tylko umiejętności dowodzenia
    przez reflekcję, którą zajmiemy się już niedługo. *)