(** * G8c: Punkty stałe funktorów wielomianowych [TODO] *)

From Typonomikon Require Import G8b.

(** * Najmniejsze i największe punkty stałe funktorów *)

(** TODO: To tylko wstępna notatka, trzeba porządnie wytłumaczyć co to punkt
    TODO: stały i tak dalej. Zamknąć też [Mu] i [Nu] w osobny moduł. *)

From Typonomikon Require Import D1 D1z D5 F3 F4.

Unset Positivity Checking.

(** Jeżeli wyłączymy sprawdzanie ścisłej pozytywności możemy zdefiniować rodziny
    typów [Mu] i [Nu] (po polsku wymawiane "mi" i "ni"), które reprezentują
    najmniejszy i największy punkt stały funktora. Pisząc "funktor" mam na myśli
    byt o typie [Type -> Type], zaś jego punkt stały to typ [X], który spełnia
    [F X = X]. *)

Inductive Mu (F : Type -> Type) : Type :=
| In : F (Mu F) -> Mu F.

Arguments In {F} _.

(** Spójrzmy na [Mu]. Jego jedyny konstruktor [In] ustanawia izomorfizm między
    typami [F (Mu F)] oraz [Mu F], co oznacza, że [Mu F] faktycznie jest punktem
    stałym funktora [F]. [Mu] jest typem induktywnym, co gwarantuje nam, że ten
    punkt stały jest najmniejszym punktem stałym. *)

CoInductive Nu (F : Type -> Type) : Type :=
{
  Out : F (Nu F);
}.

Arguments Out {F} _.

(** Dla [Nu] wszystko działa dokładnie dualnie. Pole [Out] ustanawia izomorfizm
    między [Nu F] i [F (Nu F)], co czyni [Nu F] punktem stałym funktora [F].
    Ponieważ [Nu] jest koinduktywne, ten punkt stały jest największym punktem
    stałym. *)

Set Positivity Checking.

(** Jak możemy użyć [Mu] i [Nu] do definiowania odpowiednio typów induktywnych
    i koinduktywnych? To proste: wystarczy zdefiniować funktor i zaaplikować do
    niego [Mu] lub [Nu]. Do definiowania funktorów najprościej zaś jest użyć
    mechanizmu definiowania typów induktywnych. *)

Inductive ListR (A X : Type) : Type :=
| NilR  : ListR A X
| ConsR : A -> X -> ListR A X.

Arguments NilR  {A X}.
Arguments ConsR {A X} _ _.

(** Typ [ListR] reprezentuje funktor wielomianowy [F(X) = 1 + A * X]. Jest to
    funktor bazowy typów [list] i [CoList], czyli że [list = Mu (ListR A)], a
    [CoList = Nu (ListR A)].

    Przyjrzyjmy się ze szczegółami, jak to dokładnie działa. *)

Module List.

Definition List (A : Type) : Type := Mu (ListR A).

(** Zdefiniowanie typu [List] jest banalne... *)

Unset Guard Checking.
Lemma List_ind' :
  forall
    {A : Type} (P : List A -> Prop)
    (HNil : P (In NilR))
    (HCons : forall (h : A) (t : List A), P t -> P (In (ConsR h t)))
    (l : List A), P l.
Proof.
  fix IH 5.
  destruct l as [[| h t]].
    exact HNil.
    apply HCons, IH; assumption.
Defined.
Set Guard Checking.

(** ... ale żeby udowodnić dla typu [List] regułę indukcji musimy wyłączyć
    termination checker. Powód tego jest prosty: [Mu] nie jest typem ściśle
    pozytywnym, a zatem Coq nie widzi, że nasza definicja faktycznie terminuje. *)

Fixpoint f {A : Type} (l : list A) : List A :=
match l with
| [] => In NilR
| h :: t => In (ConsR h (f t))
end.

(** Możemy łatwo przekształcić starą dobrą listę typu [list A] (który jest
    "zwykłym" typem induktywnym) w nową listę typu [List A] (tego zdefiniowanego
    za pomocą [Mu]. *)

Unset Guard Checking.
Fixpoint g {A : Type} (l : List A) {struct l} : list A :=
match l with
| In NilR        => []
| In (ConsR h t) => h :: g t
end.
Set Guard Checking.

(** Ale żeby przekształcić listę typu [List A] w listę typu [list A], musimy
    znowu wyłączyć termination checker (albo użyć reguły indukcji, której
    zdefiniowane również wymagało wyłączenia go). *)

Lemma fg :
  forall {A : Type} (l : list A),
    g (f l) = l.
Proof.
  induction l as [| h t]; cbn;
  rewrite ?IHt; reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (l : List A),
    f (g l) = l.
Proof.
  intros.
  induction l using List_ind'; cbn.
    reflexivity.
    rewrite IHl. reflexivity.
Qed.

(** Udowodnienie, że typy [list A] i [List A] są izomorficzne jest bardzo łatwe,
    ale cały proces jest mocno dołujący, gdyż wymaga oszukania najpierw positivity
    checkera, a potem termination checkera *)

End List.

(** Niestety, to nie drobne oszustwa są naszym największym problemem (kto nigdy
    nie nakłamał babci, że wszystko jest ok?). Problem jest znacznie bardziej
    poważny: [Mu] oraz [Nu] umożliwiają nam udowodnienie fałszu.

    Jest tak dlatego, że typy induktywne są punktami stałymi ściśle pozytywnych
    funktorów wielomianowych, podczas gdy do [Mu] możemy wstawić dowolny funktor.
    Podobnie sprawa ma się z [Nu].

    Zobaczmy, jak to wygląda w praktyce. *)

Inductive WutR (X : Type) : Type :=
| wutR : (X -> bool) -> WutR X.

Arguments wutR {X} _.

Definition Wut : Type := Mu WutR.

Definition wut (f : Wut -> bool) : Wut :=
  In (wutR f).

(** Widzieliśmy już w rozdziale o typach induktywnych, że negatywne typy
    induktywne prowadzą do sprzeczności. Właśnie tego faktu użyjemy by
    pokazać, że [Mu] również prowadzi do sprzeczności.

    Przykładem negatywnego typu induktywnego jest typ [Wut], który spełnia
    równanie [Wut = (Wut -> bool)]. Mając [Mu], możemy zdefiniować Wut] jako
    najmniejszy punkt stały funktora [F(X) = (X -> bool)] (który nazwaliśmy
    [wutR]). *)

Definition tuw (w : Wut) : Wut -> bool :=
match w with
| In (wutR f) => f
end.

(** Będziemy chcieli skorzystać z twierdzenia Cantora, więc potrzebna nam
    będzie funkcja typu [Wut -> Wut -> bool]. Zdefiniowanie takiej funkcji
    jest proste - każde [w : Wut] ma w środku funkcję [Wut -> bool]. *)

(* begin hide *)
(* TODO: czemu brakuje definicje surjective? *)
Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall b : B, exists a : A, f a = b.
(* end hide *)

Lemma surjective_tuw :
  surjective tuw.
Proof.
  unfold Wut, surjective.
  intro f. exists (In (wutR f)).
  cbn. reflexivity.
Qed.

(** Funkcja [tuw] jest surjekcją - ponieważ każdą funkcję [Wut -> bool] można
    za pomocą konstruktora [wut] "włożyć" do typu [Wut], to każdą taką funkcję
    można również wyjąć z jakiegoś elementu typu [Wut]. *)

Lemma not_surjective_tuw :
  ~ surjective tuw.
Proof.
  apply (Cantor' tuw negb).
  destruct b; inversion 1.
Qed.

(** Ale twierdzenie Cantora mówi nam, że [tuw] nie może być surjekcją - typ
    funkcji z [Wut] w [bool] jest "większy" niż typ [Wut]. *)

Lemma Mu_illegal : False.
Proof.
  apply not_surjective_tuw.
  apply surjective_tuw.
Qed.

(** Ponieważ [tuw] jednocześnie jest i nie jest surjekcją, dostajemy sprzeczność
    i jest pozamiatane - typ [Mu] jest nielegalny. *)

Definition CoWut : Type := Nu WutR.

Definition tuw' (x y : CoWut) : bool :=
match Out x with
| wutR f => f y
end.

Lemma surjective_tuw' :
  surjective tuw'.
Proof.
  unfold surjective.
  intro f. exists {| Out := wutR f |}.
  unfold tuw'. cbn. reflexivity.
Qed.

Lemma not_surjective_tuw' :
  ~ surjective tuw'.
Proof.
  apply (Cantor' tuw' negb).
  destruct b; inversion 1.
Qed.

Lemma Nu_illegal : False.
Proof.
  apply not_surjective_tuw'.
  apply surjective_tuw'.
Qed.

(** Sprawa z [Nu] ma się zupełnie dualnie. Definiujemy typ [CoWut], który jest
    dualny do [Wut], tzn. jest największym punktem stałym funktora [WutR]. Mając
    element [w : CoWut] możemy z niego wyjąć dowolną funkcję [CoWut -> bool], a
    zatem mamy surjekcję [CoWut -> CoWut -> bool]. Z twierdzenia Cantora wiemy
    jednak, że jest to niemożliwe, a zatem mamy sprzeczność.

    Skoro wiemy już, że [Mu] i [Nu] nie są dobrym pomysłem, spróbujmy za Tym razem bez oszukiwania  *)

Module List'.

Inductive List (A : Type) : Type :=
| In : ListR A (List A) -> List A.

Arguments In {A} _.

(** Dużo lepiej jest "zawiązać węzeł" (w ten sposób często nazywane bywają
    techniki oparte o punkty stałe) ręcznie, bez używania [Mu] ani [Nu], dzięki
    czemu nie musimy oszukiwać i wyłączać positivity/termination checkera. Żeby
    to zrobić, wystarczy zdefiniować typ wyglądający jak [Mu]/[Nu], ale za to z
    podstawionym za [F] konkretnym funktorem.

    To właśnie robimy w powyższej, alternatywnej definicji typu [List A]: mamy
    jeden konstruktor [In], jak w [Mu], ale zamiast [F (Mu F)] bierze on dużo
    bardziej konkretny argument o typie [ListR A (List A)]. Dzięki temu Coq
    akceptuje powyższy typ jako poprawny. *)

Lemma List_ind' :
  forall
    {A : Type} (P : List A -> Prop)
    (HNil : P (In NilR))
    (HCons : forall (h : A) (t : List A), P t -> P (In (ConsR h t)))
    (l : List A), P l.
Proof.
  fix IH 5.
  destruct l as [[| h t]].
    exact HNil.
    apply HCons, IH; assumption.
Defined.

(** Teraz regułę indukcji możemy udowodnić bez większych problemów oraz bez
    oszukiwania. *)

Fixpoint f {A : Type} (l : list A) : List A :=
match l with
| [] => In NilR
| h :: t => In (ConsR h (f t))
end.

Fixpoint g {A : Type} (l : List A) : list A :=
match l with
| In NilR => []
| In (ConsR h t) => h :: g t
end.

(** Także funkcja zamieniająca nową listę w starą nie wymaga żadnych oszustw -
    możemy teraz normalnie programować z wykorzystaniem dopasowań i rekursji,
    nie musząc się martwić o termination checker. *)

Lemma fg :
  forall {A : Type} (l : list A),
    g (f l) = l.
Proof.
  induction l as [| h t]; cbn;
  rewrite ?IHt; reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (l : List A),
    f (g l) = l.
Proof.
  intros.
  induction l using List_ind'; cbn.
    reflexivity.
    rewrite IHl. reflexivity.
Qed.

(** Dowody pozostają równie proste jak poprzednio. *)

End List'.

(** * Funktory bazowe często używanych typów *)

(** ** Zwykłe typy induktywne *)

(** Z wiedzą, którą dotychczas zdobyliśmy, nie trudno wyobrazić sobie, jak wygląda
    funktor bazowy typu [nat]. *)

Module NatF.

Inductive NatF (X : Type) : Type :=
| Zero : NatF X
| Succ : X -> NatF X.

Arguments Zero {X}.
Arguments Succ {X} _.

Inductive Nat : Type :=
| In : NatF Nat -> Nat.

Fixpoint f (n : nat) : Nat :=
match n with
| 0 => In Zero
| Datatypes.S n' => In (Succ (f n'))
end.

Fixpoint g (n : Nat) : nat :=
match n with
| In Zero => 0
| In (Succ n') => Datatypes.S (g n')
end.

Lemma fg :
  forall n : nat,
    g (f n) = n.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    f_equal. assumption.
Qed.

Lemma gf :
  forall n : Nat,
    f (g n) = n.
Proof.
  fix IH 1.
  destruct n as [[| n']]; cbn.
    reflexivity.
    do 2 f_equal. apply IH.
Qed.

End NatF.

(** ** Typy sparametryzowane *)

(** Widzieliśmy już funktor bazowy dla list, rzućmy więc jeszcze szybko okiem
    na funkctor bazowy typu drzew binarnych. *)

Module BTree.

Inductive BTree (A : Type) : Type :=
| E : BTree A
| N : A -> BTree A -> BTree A -> BTree A.

Arguments E {A}.
Arguments N {A} _ _ _.

Module BTreeR.

Inductive BTreeR (A R : Type) : Type :=
| ER : BTreeR A R
| NR : A -> R -> R -> BTreeR A R.

Arguments ER {A R}.
Arguments NR {A R} _ _ _.

Inductive BTree' (A : Type) : Type :=
| In : BTreeR A (BTree' A) -> BTree' A.

Arguments In {A} _.

Fixpoint f {A : Type} (t : BTree A) : BTree' A :=
match t with
| E       => In ER
| N v l r => In (NR v (f l) (f r))
end.

Fixpoint g {A : Type} (t : BTree' A) : BTree A :=
match t with
| In ER         => E
| In (NR v l r) => N v (g l) (g r)
end.

Lemma fg :
  forall {A : Type} (t : BTree A), g (f t) = t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : BTree' A), f (g t) = t.
Proof.
  fix IH 2.
  destruct t as [[]]; cbn.
    reflexivity. rewrite !IH. reflexivity.
Qed.

End BTreeR.

(** W środowiskach Haskellowych powyższy sposób definiowania funktorów bazowych
    zowie się "schematami rekursji" (ang. recursion schemes). W Coqu możliwy
    jest też nieco inny sposób, który zobaczymy poniżej. *)

Module BTreeF.

Inductive BTreeF (F : Type -> Type) (A : Type) : Type :=
| EF : BTreeF F A
| NF : A -> F A -> F A -> BTreeF F A.

Arguments EF {F A}.
Arguments NF {F A} _ _ _.

(** Tym razem naszymi parametrami nie są już dwa typy [A] i [R], lecz funktor
    [F : Type -> Type] oraz typ [A]. Przez to poddrzewa reprezentujemy jako
    [F A] zamiast [R]. Poza tymi dwoma drobnymi różnicami, wszystko inne pozostaje
    niezmienione. *)

Inductive BTree' (A : Type) : Type :=
| In : BTreeF BTree' A -> BTree' A.

Arguments In {A} _.

Fixpoint f {A : Type} (t : BTree A) : BTree' A :=
match t with
| E       => In EF
| N v l r => In (NF v (f l) (f r))
end.

Fixpoint g {A : Type} (t : BTree' A) : BTree A :=
match t with
| In EF => E
| In (NF v l r) => N v (g l) (g r)
end.

Lemma fg :
  forall {A : Type} (t : BTree A), g (f t) = t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : BTree' A), f (g t) = t.
Proof.
  fix IH 2.
  destruct t as [[]]; cbn.
    reflexivity. rewrite !IH. reflexivity.
Qed.

End BTreeF.

End BTree.

(** ** Typy wzajemnie induktywne *)

Module FinitaryTreeF.

Inductive Tree (A : Type) : Type :=
| Empty : Tree A
| Node  : A -> Forest A -> Tree A

with Forest (A : Type) : Type :=
| Nil  : Forest A
| Cons : Tree A -> Forest A -> Forest A.

Arguments Empty {A}.
Arguments Node  {A} _ _.

Arguments Nil   {A}.
Arguments Cons  {A} _ _.

Inductive TreeR (A F : Type) : Type :=
| EmptyR : TreeR A F
| NodeR  : A -> F -> TreeR A F.

Inductive ForestR (A F T : Type) : Type :=
| NilR  : ForestR A F T
| ConsR : T -> F -> ForestR A F T.

Arguments EmptyR {A F}.
Arguments NodeR  {A F} _ _.

Arguments NilR   {A F T}.
Arguments ConsR  {A F T} _ _.

Module TreeR.

Inductive Tree' (A : Type) : Type :=
| InT : TreeR A (Forest' A) -> Tree' A

with Forest' (A : Type) : Type :=
| InF : ForestR A (Forest' A) (Tree' A) -> Forest' A.

Arguments InT {A} _.

Arguments InF {A} _.

Fixpoint f {A : Type} (t : Tree A) : Tree' A :=
match t with
| Empty     => InT EmptyR
| Node x ts => InT (NodeR x (fs ts))
end

with fs {A : Type} (ts : Forest A) : Forest' A :=
match ts with
| Nil        => InF NilR
| Cons t ts' => InF (ConsR (f t) (fs ts'))
end.

Fixpoint g {A : Type} (t : Tree' A) : Tree A :=
match t with
| InT EmptyR       => Empty
| InT (NodeR x ts) => Node x (gs ts)
end

with gs {A : Type} (ts : Forest' A) : Forest A :=
match ts with
| InF NilR  => Nil
| InF (ConsR t ts') => Cons (g t) (gs ts')
end.

Lemma fg :
  forall {A : Type} (t : Tree A),
    g (f t) = t

with fsgs :
  forall {A : Type} (ts : Forest A),
    gs (fs ts) = ts.
Proof.
  destruct t as [| x ts]; cbn.
    reflexivity.
    rewrite fsgs. reflexivity.

  destruct ts as [| t ts']; cbn.
    reflexivity.
    rewrite fg, fsgs. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : Tree' A),
    f (g t) = t

with gsfs :
  forall {A : Type} (ts : Forest' A),
    fs (gs ts) = ts.
Proof.
  destruct t as [[| x ts]]; cbn.
    reflexivity.
    rewrite gsfs. reflexivity.

  destruct ts as [[| t ts']]; cbn.
    reflexivity.
    rewrite gf, gsfs. reflexivity.
Qed.

End TreeR.

Module TreeF.

Inductive TreeF (F : Type -> Type) (A : Type) : Type :=
| EmptyF : TreeF F A
| NodeF  : A -> F A -> TreeF F A.

Inductive ForestF (T F : Type -> Type) (A : Type) : Type :=
| NilF  : ForestF T F A
| ConsF : T A -> F A -> ForestF T F A.

Arguments EmptyF {F A}.
Arguments NodeF  {F A} _ _.

Arguments NilF   {T F A}.
Arguments ConsF  {T F A} _ _.

Inductive Tree' (A : Type) : Type :=
| InT : TreeF Forest' A -> Tree' A

with Forest' (A : Type) : Type :=
| InF : ForestF Tree' Forest' A -> Forest' A.

Arguments InT {A} _.

Arguments InF {A} _.

Fixpoint f {A : Type} (t : Tree A) : Tree' A :=
match t with
| Empty     => InT EmptyF
| Node x ts => InT (NodeF x (fs ts))
end

with fs {A : Type} (ts : Forest A) : Forest' A :=
match ts with
| Nil        => InF NilF
| Cons t ts' => InF (ConsF (f t) (fs ts'))
end.

Fixpoint g {A : Type} (t : Tree' A) : Tree A :=
match t with
| InT EmptyF       => Empty
| InT (NodeF x ts) => Node x (gs ts)
end

with gs {A : Type} (ts : Forest' A) : Forest A :=
match ts with
| InF NilF  => Nil 
| InF (ConsF t ts') => Cons (g t) (gs ts')
end.

Lemma fg :
  forall {A : Type} (t : Tree A),
    g (f t) = t

with fsgs :
  forall {A : Type} (ts : Forest A),
    gs (fs ts) = ts.
Proof.
  destruct t as [| x ts]; cbn.
    reflexivity.
    rewrite fsgs. reflexivity.

  destruct ts as [| t ts']; cbn.
    reflexivity.
    rewrite fg, fsgs. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : Tree' A),
    f (g t) = t

with gsfs :
  forall {A : Type} (ts : Forest' A),
    fs (gs ts) = ts.
Proof.
  destruct t as [[| x ts]]; cbn.
    reflexivity.
    rewrite gsfs. reflexivity.

  destruct ts as [[| t ts']]; cbn.
    reflexivity.
    rewrite gf, gsfs. reflexivity.
Qed.

End TreeF.

End FinitaryTreeF.

(** ** Rodziny indeksowane (TODO) *)

Require Import List.
Import ListNotations.

From Typonomikon Require Import F3 F4.

Module ListCoList.

Module CoList.

Import F4.

Module CoList_ForallF.

Inductive ForallF
  {A : Type} (R : A -> A -> Prop)
  (F : (A -> A -> Prop) -> CoList A -> CoList A -> Prop)
  : CoList A -> CoList A -> Prop :=
| Nils  :
    forall l1 l2 : CoList A,
      uncons l1 = NilF -> uncons l2 = NilF -> ForallF R F l1 l2
| Conss :
    forall (l1 l2 : CoList A) (h1 h2 : A) (t1 t2 : CoList A),
      uncons l1 = ConsF h1 t1 -> uncons l2 = ConsF h2 t2 ->
        R h1 h2 -> F R t1 t2 -> ForallF R F l1 l2.

CoInductive CoForall {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
{
  uncons' : ForallF R CoForall l1 l2
}.

End CoList_ForallF.

End CoList.

End ListCoList.

(** ** Rodziny indeksowane za pomocą typów parametryzowanych i równości (TODO) *)

Module ListCoList2.

Inductive ListR (A R : Type) : Type :=
| NilR  : ListR A R
| ConsR : A -> R -> ListR A R.

Arguments NilR  {A R}.
Arguments ConsR {A R} _ _.

Inductive List (A : Type) : Type :=
| In : ListR A (List A) -> List A.

Arguments In {A} _.

CoInductive CoList (A : Type) : Type :=
{
  uncons : ListR A (CoList A);
}.

Arguments uncons {A} _.

(** TODO: Możemy zmniejszyć o połowę ilość pracy do potrzebnej do zdefiniowania
    wielu użytecznych rodzin typów, po prostu ponownie wykorzystując szablony
    operujące na "funktorze bazowym", jak poniżej. *)

Inductive ForallR
  {A R : Type}
  (Unwrap : R -> ListR A R)
  (RA : A -> A -> Prop)
  (RR : R -> R -> Prop)
  (l1 l2 : R)
  : Prop :=
| Nils  :
    Unwrap l1 = NilR -> Unwrap l2 = NilR -> ForallR Unwrap RA RR l1 l2
| Conss :
    forall (h1 h2 : A) (t1 t2 : R),
      Unwrap l1 = ConsR h1 t1 -> Unwrap l2 = ConsR h2 t2 ->
        RA h1 h2 -> RR t1 t2 -> ForallR Unwrap RA RR l1 l2.

Definition uncons' {A : Type} (l : List A) : ListR A (List A) :=
match l with
| In x => x
end.

Inductive Forall {A : Type} (R : A -> A -> Prop) (l1 l2 : List A) : Prop :=
| InForall : ForallR uncons' R (Forall R) l1 l2 -> Forall R l1 l2.

CoInductive CoForall {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
{
  uncons'' : ForallR uncons R (CoForall R) l1 l2
}.

Inductive ExistsR
  {A L : Type}
  (Uncons : L -> ListR A L)
  (RA : A -> A -> Prop)
  (RL : L -> L -> Prop)
  (l1 l2 : L)
  : Prop :=
| Here  :
    forall (h1 h2 : A) (t1 t2 : L),
      Uncons l1 = ConsR h1 t1 -> Uncons l2 = ConsR h2 t2 ->
        RA h1 h2 -> ExistsR Uncons RA RL l1 l2
| There :
    forall (h1 h2 : A) (t1 t2 : L),
      Uncons l1 = ConsR h1 t1 -> Uncons l2 = ConsR h2 t2 ->
        RL t1 t2 -> ExistsR Uncons RA RL l1 l2.

Inductive Exists {A : Type} (R : A -> A -> Prop) (l1 l2 : List A) : Prop :=
| InExists : ExistsR uncons' R (Exists R) l1 l2 -> Exists R l1 l2.

Inductive CoExists {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
| InCoExists : ExistsR uncons R (CoExists R) l1 l2 -> CoExists R l1 l2.

(** TODO: Może możemy zdefiniować funkcje generyczne? *)

Fixpoint cata {A R : Type} (f : ListR A R -> R) (l : List A) : R :=
match l with
| In NilR        => f NilR
| In (ConsR h t) => f (ConsR h (cata f t))
end.

CoFixpoint ana {A R : Type} (f : R -> ListR A R) (r : R) : CoList A :=
{|
  uncons :=
    match f r with
    | NilR      => NilR
    | ConsR h t => ConsR h (ana f t)
    end
|}.

End ListCoList2.