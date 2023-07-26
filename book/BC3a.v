(** * BC3a: Programowanie funkcyjne z typami zależnymi [TODO] *)

(** * Typy zależne, czyli typowanie statyczne na sterydach *)

(** * Uniwersum (TODO) *)

(** * Funkcje zależne (TODO) *)

(** * Pary zależne i podtypy (TODO) *)

(** W Coqu, w przeciwieństwie do wielu języków imperatywnych, nie ma
    mechanizmu podtypowania, a każde dwa typy są ze sobą rozłączne.
    Nie jest to problemem, gdyż podtypowanie możemy zasymulować za
    pomocą sum zależnych, a te zdefiniować możemy induktywnie. *)

Module sigma.

Inductive sigT (A : Type) (P : A -> Type) : Type :=
| existT : forall x : A, P x -> sigT A P.

(** Typ [sigT] reprezentuje sumę zależną, której elementami są pary zależne.
    Pierwszym elementem pary jest [x], który jest typu [A], zaś drugim
    elementem pary jest term typu [P x]. Suma zależna jest wobec tego pewnym
    uogólnieniem produktu.

    Niech cię nie zmyli nazewnictwo:
    - Suma jest reprezentowana przez typ [sum A B]. Jej elementami są
      elementy [A] zawinięte w konstruktor [inl] oraz elementy [B]
      zawinięte w konstruktor [inr]. Reprezentuje ideę "lub/albo".
      Typ [B] nie może zależeć od typu [A].
    - Produkt jest reprezentowany przez typ [prod A B]. Jego elementami
      są pary elementów [A] i [B]. Reprezentuje on ideę "i/oraz". Typ
      [B] nie może zależeć od typu [A].
    - Uogólnieniem produktu jest suma zależna. Jest ona reprezentowana
      przez typ [sigT A P]. Jej elementami są pary zależne elementów
      [A] i [P x], gdzie [x : A] jest pierwszym elementem pary.
      Reprezentuje ona ideę "i/oraz", gdzie typ [P x] może zależeć od
      elementu [x] typu [A].
    - Typ funkcji jest reprezentowany przez [A -> B]. Jego elementami
      są termy postaci [fun x : A => ...]. Reprezentują ideę "daj mi
      coś typu [A], a ja oddam ci coś typu [B]". Typ [B] nie może
      zależeć od typu [A].
    - Uogólnieniem typu funkcji jest produkt zależny [forall x : A, B x].
      Jego elementami są termu postaci [fun x : A => ...]. Reprezentuje
      on ideę "daj mi [x] typu [A], a ja oddam ci coś typu [B x]". Typ
      [B x] może zależeć od typu elementu [x] typu [A]. *)

(** [sigT] jest najogólniejszą postacią pary zależnej — [A] jest typem,
    a [P] rodziną typów. Mimo swej ogólności jest używany dość rzadko,
    gdyż najbardziej przydatną postacią sumy zależnej jest typ [sig]: *)

Inductive sig (A : Type) (P : A -> Prop) : Type :=
| exist : forall x : A, P x -> sig A P.

Arguments exist {A P} _ _.

(** Typ [sig A P] można interpretować jako typ składający się z tych
    elementów [A], które spełniają predykat [P]. Formalnie jest to
    para zależna, której pierwszym elementem jest term typu [A], zaś
    drugim dowód na to, że spełnia on predykat [P]. *)

Definition big_nat : Type := sig nat (le 100).

Definition big_100 : big_nat := exist 100 (le_n 100).

(** Typ [big_nat] reprezentuje liczby naturalne większe lub równe 100,
    zaś term [big_100] to liczba [100] wraz z załączonym dowodem faktu, 
    że jest ona większa lub równa 100.

    Interpretacja typu [sig] sprawia, że jest on wykorzystywany bardzo
    często do podawania specyfikacji programów — pozwala on dodać do
    wyniku zwracanego przez funkcję informację o jego właściwościach.
    W przypadku argumentów raczej nie jest używany, gdyż prościej jest
    po prostu wymagać dowodów żądanych właściwości w osobnych argumentach
    niż pakować je w [sig] po to, żeby i tak zostały później odpakowane. *)

Definition big_101 : big_nat.
Proof.
  apply (exist 101).
  repeat constructor.
Defined.

(** Definiowanie wartości typu [sig] jest problematyczne, gdyż zawierają
    one dowody. Napisanie definicji "ręcznie", explicité podając proofterm,
    nie wchodzi w grę. Innym potencjalnym rozwiązaniem jest napisanie dowodu
    na boku, a następnie użycie go we właściwej definicji, ale jest ono
    dłuższe niż to konieczne.

    Przypomnijmy sobie, czym są taktyki. Dowody to termy, których typy są
    sortu [Prop], a taktyki służą do konstruowania tych dowodów. Ponieważ
    dowody nie różnią się (prawie) niczym od programów, taktyk można użyć
    także do pisania programów. Taktyki to metaprogramy (napisane w jęzku
    Ltac), które piszą programy (w jęzku termów Coqa, zwanym Gallina).

    Wobec tego trybu dowodzenia oraz taktyk możemy używać nie tylko do
    dowodzenia, ale także do definiowania i to właśnie uczyniliśmy w
    powyższym przykładzie. Skonstruowanie termu typu [big_nat],
    czyli parzystej liczby naturalnej, odbyło się w następujący sposób.

    Naszym celem jest początkowo [big_nat], czyli typ, którego
    element chcemy skonstrować. Używamy konstruktora [exist], który
    w naszym przypadku jest typu [forall x : nat, 100 <= n -> big_nat].
    Wobec tego [exist 101] jest typu [100 <= 101 -> big_nat], a jego
    zaaplikowanie skutkować będzie zamianą naszego celu na [100 <= 101].
    Następnie dowodzimy tego faktu, co kończy proces definiowania. *)

(** **** Ćwiczenie *)

(** Zdefiniuj predykat [sorted], który jest spełniony, gdy jego argument
    jest listą posortowaną. Następnie zdefiniuj typ list liczb naturalnych
    posortowanych według relacji [<=] i skonstruuj term tego typu
    odpowiadający liście [[42; 666; 1337]]. *)

End sigma.

(** * Indeksowane enumeracje (TODO) *)

(* begin hide *)
(*
TODO: Maszyny stanowe i type-driven design jako ćwiczenia
TODO: do (indeksowanych) enumeracji.
*)
(* end hide *)

Module index.

Inductive I : nat -> Type :=
| c0 : bool -> I 0
| c42 : nat -> I 42.

(** Ostatnią poznaną przez nas innowacją są typy indeksowane. Tutaj również
    definiujemy za jednym zamachem (ekhem...) dużo typów, ale nie są one
    niezależne jak w przypadku parametrów, lecz mogą od siebie wzajemnie
    zależeć. Słowem, tak naprawdę definiujemy przez indukcję funkcję
    typu [A_1 -> ... -> A_n -> Type/Prop], gdzie [A_i] to indeksy. *)

Definition I_case_very_nondep_type : Type :=
  forall (P : Type) (c0' : bool -> P) (c42' : nat -> P),
    forall n : nat, I n -> P.

Definition I_case_very_nondep
  (P : Type) (c0' : bool -> P) (c42' : nat -> P)
  {n : nat} (i : I n) : P :=
match i with
| c0 b => c0' b
| c42 n => c42' n
end.

(** Możliwych reguł analizy przypadków mamy tutaj trochę więcej niż w
    przypadku parametrów. W powyższej regule [P] nie zależy od indeksu
    [n : nat]... *)

Definition I_case_nondep_type : Type :=
  forall (P : nat -> Type) (c0' : bool -> P 0) (c42' : nat -> P 42),
    forall n : nat, I n -> P n.

Definition I_case_nondep
  (P : nat -> Type) (c0' : bool -> P 0) (c42' : nat -> P 42)
  {n : nat} (i : I n) : P n :=
match i with
| c0 b => c0' b
| c42 n => c42' n
end.

(** ... a w powyższej tak. Jako, że indeksy zmieniają się pomiędzy
    konstruktorami, każdy z nich musi kwantyfikować je osobno (co akurat
    nie jest potrzebne w naszym przykładzie, gdyż jest zbyt prosty). *)

Definition I_case_dep_type : Type :=
  forall (P : forall n : nat, I n -> Type)
    (c0' : forall b : bool, P 0 (c0 b))
    (c42' : forall n : nat, P 42 (c42 n)),
      forall (n : nat) (i : I n), P n i.

Definition I_case_dep
  (P : forall n : nat, I n -> Type)
  (c0' : forall b : bool, P 0 (c0 b))
  (c42' : forall n : nat, P 42 (c42 n))
  (n : nat) (i : I n) : P n i :=
match i with
| c0 b => c0' b
| c42 n => c42' n
end.

(** Ogólnie reguła jest taka: reguła niezależna (pierwsza) nie zależy od
    niczego, a zależna (trzecia) zależy od wszystkiego. Reguła druga jest
    pośrednia - ot, take ciepłe kluchy. *)

End index.

(** * Rekordy zależne *)

(** * Kwantyfikacja egzystencjalna (TODO) *)

(** Znamy już pary zależne i wiemy, że mogą służyć do reprezentowania
    podtypów, których w Coqu brak. Czas zatem uświadomić sobie kolejny
    fragment korespondencji Curry'ego-Howarda, a mianowicie definicję
    kwantyfikacji egzystencjalnej: *)

Module ex.

Inductive ex (A : Type) (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex A P.

(** [ex] to kolejne wcielenie sumy zależnej. Porównaj dokładnie tę
    definicję z definicją [sigT] oraz [sig]. [ex] jest niemal identyczne
    jak [sig]: jest to para zależna, której pierwszym elementem jest
    term [x : A], a drugim dowód na to, że [P x] zachodzi. [ex] jednak,
    w przeciwieństwie do [sig], żyje w [Prop], czyli jest zdaniem — nie
    liczą się konkretne postaci jego termów ani ich ilość, a jedynie
    fakt ich istnienia. To sprawia, że [ex] jest doskonałym kandydatem
    do reprezentowania kwantyfikacji egzystencjalnej. *)

(** **** Ćwiczenie *)

(** Udowodnij, że dla każdej liczby naturalnej n istnieje liczba od niej
    większa. Następnie zastanów się, jak działa taktyka [exists]. *)

Lemma exists_greater :
  forall n : nat, ex nat (fun k : nat => n < k).
(* begin hide *)
Proof.
  intro. apply (ex_intro _ _ (S n)). unfold lt. apply le_n.
Qed.
(* end hide *)

End ex.

(** * Równość (TODO) *)

(** * Równość a ścieżki *)

Inductive Path {A : Type} (x : A) : A -> Type :=
| idp : Path x x.

Arguments idp {A x}.

Definition eq_to_Path {A : Type} {x y : A} (e : x = y) : Path x y :=
match e with
| eq_refl => idp
end.

Definition Path_to_eq {A : Type} {x y : A} (p : Path x y) : x = y :=
match p with
| idp => eq_refl
end.

Lemma eq_to_Path_to_eq :
  forall {A : Type} {x y : A} (e : x = y),
    Path_to_eq (eq_to_Path e) = e.
Proof.
  destruct e. cbn. reflexivity.
Qed.

Lemma Path_to_eq_to_Path :
  forall {A : Type} {x y : A} (p : Path x y),
    eq_to_Path (Path_to_eq p) = p.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Lemma eq_to_Path_to_eq' :
  forall {A : Type} {x y : A} (e : x = y),
    Path (Path_to_eq (eq_to_Path e)) e.
Proof.
  destruct e. cbn. reflexivity.
Defined.

Lemma Path_to_eq_to_Path' :
  forall {A : Type} {x y : A} (p : Path x y),
    Path (eq_to_Path (Path_to_eq p)) p.
Proof.
  destruct p. cbn. reflexivity.
Defined.