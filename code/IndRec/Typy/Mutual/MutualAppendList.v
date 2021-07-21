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

Fixpoint toList {A : Type} (l : AList A) : list A :=
match l with
    | Single x     => [x]
    | Append l1 l2 => toList l1 ++ toList l2
end.

Definition toList' {A : Type} (l : CList A) : list A :=
match l with
    | Nil       => []
    | NotNil l' => toList l'
end.