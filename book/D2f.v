(** * D2f: Rekursja wyższego rzędu [TODO] *)

From Typonomikon Require Import D5.

(** * Rząd rżnie głupa, czyli o pierwszym i wyższym rzędzie (TODO) *)

(** * Rekursja wyższego rzędu (TODO) *)

(** Pozostaje kwestia rekursji wyższego rzędu. Co to takiego? Ano dotychczas
    wszystkie nasze wywołania rekurencyjne były konkretne, czyli zaaplikowane
    do argumentów.

    Mogłoby się wydawać, że jest to jedyny możliwy sposób robienia wywołań
    rekurencyjnych, jednak nie jest tak. Wywołania rekurencyjne mogą mieć
    również inną, wyższorzędową postać, a mianowicie - możemy przekazać
    funkcję, którą właśnie definiujemy, jako argument do innej funkcji.

    Dlaczego jest to wywołanie rekurencyjne, skoro nie wywołujemy naszej
    funkcji? Ano dlatego, że tamta funkcja, która dostaje naszą jako
    argument, dostaje niejako możliwość robienia wywołań rekurencyjnych.
    W zależności od tego, co robi tamta funkcja, wszystko może być ok (np.
    gdy ignoruje ona naszą funkcję i w ogóle jej nie używa) lub śmiertelnie
    niebezpieczne (gdy próbuje zrobić wywołanie rekurencyjne na strukturalnie
    większym argumencie).

    Sztoby za dużo nie godoć, bajszpil: *)

Inductive Tree (A : Type) : Type :=
| Node : A -> list (Tree A) -> Tree A.

Arguments Node {A} _ _.

(** [Tree] to typ drzew niepustych, które mogą mieć dowolną (ale skończoną)
    ilość poddrzew. Spróbujmy zdefiniować funkcję, która zwraca lustrzane
    odbicie drzewa. *)

Unset Guard Checking.
Fixpoint mirror {A : Type} (t : Tree A) {struct t} : Tree A :=
match t with
| Node x ts => Node x (map mirror (rev ts))
end.
Set Guard Checking.

(** Nie jest to zbyt trudne. Rekurencyjnie odbijamy wszystkie poddrzewa za
    pomocą [map mirror], a następnie odwracamy kolejność poddrzew z użyciem
    [rev]. Chociaż poszło gładko, to mamy tu do czynienia z czymś, czego
    wcześniej nie widzieliśmy. Nie ma tu żadnego wywołania rekurencyjnego,
    a mimo to funkcja działa ok. Dlaczego? Właśnie dlatego, że wywołania
    rekurencyjne są robione przez funkcję [map]. Mamy więc do czynienia z
    rekursją wyższego rzędu. *)

Inductive mirrorG {A : Type} : Tree A -> Tree A -> Prop :=
| mirrorG_0 :
    forall (x : A) (ts rs : list (Tree A)),
      mirrorsG ts rs -> mirrorG (Node x ts) (Node x (rev rs))

with mirrorsG {A : Type} : list (Tree A) -> list (Tree A) -> Prop :=
| mirrorsG_nil :
    mirrorsG [] []
| mirrorsG_cons :
    forall (t t' : Tree A) (ts ts' : list (Tree A)),
      mirrorG t t' -> mirrorsG ts ts' ->
        mirrorsG (t :: ts) (t' :: ts').

Require Import Equality.

Lemma mirrorG_correct :
  forall {A : Type} (t : Tree A),
    mirrorG t (mirror t).
Proof.
  fix IH 2.
  destruct t. cbn. rewrite map_rev. constructor.
  induction l as [| t ts].
    cbn. constructor.
    cbn. constructor.
      apply IH.
      apply IHts.
Qed.

Compute mirror (Node 0 [Node 1 [Node 5 []; Node 6 []; Node 7 []]; Node 2 []; Node 3 []]).

Module mirror.

Inductive mirrorD {A : Type} : Tree A -> Type :=
| mirrorD' :
    forall (x : A) (ts : list (Tree A)),
      mirrorsD (rev ts) -> mirrorD (Node x ts)

with mirrorsD {A : Type} : list (Tree A) -> Type :=
| mirrorsD_nil : mirrorsD []
| mirrorsD_cons :
    forall (t : Tree A) (ts : list (Tree A)),
      mirrorD t -> mirrorsD ts -> mirrorsD (t :: ts).

Inductive mapG
  {A B : Type} (f : A -> B -> Type) : list A -> list B -> Type :=
| mapG_nil  : mapG f [] []
| mapG_cons :
    forall (a : A) (b : B) (la : list A) (lb : list B),
      f a b -> mapG f la lb -> mapG f (a :: la) (b :: lb).

Inductive mirrorG2 {A : Type} : Tree A -> Tree A -> Prop :=
| mirrorG2' :
    forall (x : A) (ts ts' : list (Tree A)),
      mapG mirrorG2 ts ts' -> mirrorG2 (Node x ts) (Node x (rev ts')).

Lemma mirrorG2_correct :
  forall {A : Type} (t : Tree A),
    mirrorG2 t (mirror t).
Proof.
  fix IH 2.
  destruct t. cbn. rewrite map_rev. constructor.
  induction l as [| t ts].
    cbn. constructor.
    cbn. constructor.
      apply IH.
      apply IHts.
Qed.

End mirror.

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