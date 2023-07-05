(** * D2cz: Głęboka indukcja [TODO] *)

Require Import List.
Import ListNotations.

(** * Głęboka indukcja (TODO) *)

(** Zacznijmy od krótkiego podsumowania naszej dotychczasowej podróży przez
    świat reguł indukcji.

    Standardowe reguły indukcji dla danego typu to te, które kształtem
    odpowiadają dokładnie kształtowi tego typu. Dla [nat] jest to reguła
    z przypadkiem bazowym zero oraz przypadkiem indukcyjnym (czyli "krokiem")
    następnikowym. Dla list jest to reguły z przypadkiem bazowym [nil] i
    "krokiem" [cons]. Zazwyczaj dostajemy je od Coqa za darmo po zdefiniowaniu
    typu, ale dla typów zagnieżdżonych musimy zdefiniować je sobie sami.

    Niestandardowe reguły indukcji to te, których kształt różni się od kształtu
    typu - w zależności od potrzeb i problemu, który próbujemy rozwiązać. Dla
    [nat] może to być np. reguła z bazowymi przypadkami 0 i 1 oraz krokiem
    "co 2". Definiujemy je ręcznie, przez dopasowanie do wzorca i rekursję
    strukturalną.

    Proste, prawda? Otóż nie do końca.
*)

Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
| ForallT_nil  : ForallT P []
| ForallT_cons :
    forall {h : A} {t : list A},
      P h -> ForallT P t -> ForallT P (h :: t).

Fixpoint list_ind_deep
  {A : Type} (P : list A -> Type) (Q : A -> Type)
  (nil : P [])
  (cons : forall {h : A} {t : list A}, Q h -> P t -> P (h :: t))
  (l : list A) (l' : ForallT Q l) {struct l'} : P l.
Proof.
  destruct l' as [| h t Qh FQh].
  - exact nil.
  - apply cons.
    + exact Qh.
    + apply (list_ind_deep _ P Q); assumption.
Defined.

Module RecursiveDeepInd.

Fixpoint ForallT' {A : Type} (P : A -> Type) (l : list A) : Type :=
match l with
| [] => unit
| h :: t => P h * ForallT' P t
end.

Fixpoint list_ind_deep'
  {A : Type} (P : list A -> Type) (Q : A -> Type)
  (nil : P [])
  (cons : forall (h : A) (t : list A),
            Q h -> P t -> P (h :: t))
  (l : list A) (l' : ForallT' Q l) {struct l} : P l.
Proof.
  destruct l as [| h t].
  - exact nil.
  - destruct l' as [Qh FQh].
    apply cons.
    + exact Qh.
    + apply (list_ind_deep' _ P Q); assumption.
Defined.

End RecursiveDeepInd.

(*
(** Dla drzewek różanych. *)

Inductive RoseTree' {A : Type} (P : A -> Type) : RoseTree A -> Type :=
| E' : RoseTree' P E
| N' : forall (x : A) (ts : list (RoseTree A)),
         P x -> ForallT (RoseTree' P) ts -> RoseTree' P (N x ts).

Arguments E' {A P}.
Arguments N' {A P x ts} _ _.

Fixpoint RoseTree_ind_deep'
  {A : Type} (P : RoseTree A -> Type) (Q : A -> Type)
  (e : P E)
  (n : forall (x : A) (ts : list (RoseTree A)),
         Q x -> ForallT P ts -> P (N x ts))
  {t : RoseTree A} (t' : RoseTree' Q t) {struct t'} : P t.
Proof.
  destruct t' as [| x l Qx FQt].
    exact e.
    apply n.
      exact Qx.
      induction FQt as [| hFQt tFQt]; constructor.
        apply (RoseTree_ind_deep' _ P Q); assumption.
        apply IHFQt.
Defined.
*)