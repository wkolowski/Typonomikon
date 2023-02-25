Inductive AList (A : Type) : Type :=
| Single : A -> AList A
| Append : AList A -> AList A -> AList A.

Arguments Single {A} _.
Arguments Append {A} _ _.

Inductive CList (A : Type) : Type :=
| Nil    : CList A
| NotNil : AList A -> CList A.

Arguments Nil    {A}.
Arguments NotNil {A} _.

Definition append {A : Type} (l1 l2 : CList A) : CList A :=
match l1, l2 with
| Nil       , _          => l2
| _         , Nil        => l1
| NotNil l1', NotNil l2' => NotNil (Append l1' l2')
end.

Fixpoint hd {A : Type} (l : AList A) : A :=
match l with
| Single h    => h
| Append l' _ => hd l'
end.

Fixpoint last {A : Type} (l : AList A) : A :=
match l with
| Single x    => x
| Append _ l' => last l'
end.

Require Import List.
Import ListNotations.

Fixpoint toListA {A : Type} (l : AList A) : list A :=
match l with
| Single x     => [x]
| Append l1 l2 => toListA l1 ++ toListA l2
end.

Definition toListC {A : Type} (l : CList A) : list A :=
match l with
| Nil       => []
| NotNil l' => toListA l'
end.

Lemma append_spec :
  forall {A : Type} (l1 l2 : CList A),
    toListC (append l1 l2) = toListC l1 ++ toListC l2.
Proof.
  destruct l1 as [| [|]], l2 as []; cbn; try reflexivity.
  symmetry. apply app_nil_r.
Qed.