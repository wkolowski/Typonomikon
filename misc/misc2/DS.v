Require Import List.
Import ListNotations.

Class stack (stack_type : Type) (elem_type : Type) : Type :=
{
    push : elem_type -> stack_type -> stack_type;
    pop : stack_type -> option elem_type
}.

Instance list_is_stack (A : Type) : stack (list A) A := {}.
Proof.
  intros h t. exact (cons h t).
  destruct 1.
    exact None.
    exact (Some a).
Defined.

Class stack' (stack_type : Type) (elem_type : Type) : Type :=
{
    push' : elem_type -> stack_type -> stack_type;
    pop' : stack_type -> option (elem_type * stack_type)
}.

Instance list_is_stack' (A : Type) : stack' (list A) A := {}.
Proof.
  exact (@cons A).
  destruct 1 as [| h t].
    exact None.
    exact (Some (h, t)).
Defined.

(*Variable Queue : Type -> Type.*)
Require Import List.
Import ListNotations.

Definition Queue := list.

Definition inject {A : Type} (q : Queue A) (x : A) := cons x q.

Fixpoint init {A : Type} (l : list A) : option (list A) :=
match l with
    | nil => None
    | h :: nil => Some nil
    | h :: t => match init t with
        | None => Some (h :: nil)
        | Some l' => Some (h :: l')
    end
end.

Eval compute in init [1; 2; 3; 4; 5].

Fixpoint last {A : Type} (l : list A) : option A :=
match l with
    | nil => None
    | h :: nil => Some h
    | h :: t => last t
end.

Eval compute in last [1; 2].

Definition pop {A : Type} (q : Queue A) : option (A * Queue A) :=
match last q, init q with
    | Some x, Some q' => Some (x, q')
    | _, _ => None
end.

Eval compute in pop (1 :: 2 :: 3 :: nil).

Inductive CatQueue (A : Type) : Type :=
    | E : CatQueue A
    | N : A -> Queue (CatQueue A) -> CatQueue A.

Arguments E [A].
Arguments N [A] _ _.

Definition empty_queue (A : Type) : Queue A := nil.

Definition singleton {A : Type} (a : A) : CatQueue A :=
    N a (empty_queue (CatQueue A)).

Definition pair {A : Type} (x y : A) : CatQueue A :=
    N x (inject (empty_queue (CatQueue A)) (singleton y)).

Fixpoint cat {A : Type} (cq cq' : CatQueue A) : CatQueue A :=
match cq, cq' with
    | E, _ => cq'
    | _, E => cq
    | (N a q), x => N a (inject q x)
end.

(*Fixpoint link {A : Type} (cq : CatQueue A) *)
Require Import Coq.Program.Wf.

Program Fixpoint linkAll {A : Type} (cq : CatQueue A) (qcq : Queue (CatQueue A))
    {measure (length qcq)} : CatQueue A :=
match pop qcq with
    | None => cq
    | Some (d, q) => cat cq (linkAll d q)
end.
Next Obligation. admit. Defined.
Next Obligation. admit. Defined.

Fixpoint rebuild {A : Type} (qcq : Queue (CatQueue A)) : CatQueue A :=
match pop qcq with
    | None => E
    | Some (c, q) => linkAll c q
end.

Definition uncons {A : Type} (cq : CatQueue A) : option (A * CatQueue A) :=
match cq with
    | E => None
    | N x q => Some (x, rebuild q)
end.




    
