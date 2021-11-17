Inductive TreeF (A X : Type) : Type :=
    | E : TreeF A X
    | N : A -> TreeF A X -> X -> TreeF A X.

Arguments E {A X}.
Arguments N {A X} _ _ _.

CoInductive Tree (A : Type) : Type :=
{
    Out : TreeF A (Tree A);
}.

Arguments Out {A} _.

Fixpoint inums (n : nat) : TreeF nat (Tree nat) :=
match n with
    | 0 => E
    | S n' => N n' (inums n') {| Out := E |}
end.

CoFixpoint nums (n : nat) : Tree nat :=
{|
    Out := N n (inums n) (nums (S n));
|}.

Fixpoint leftmostF {A X : Type} (t : TreeF A X) : option A :=
match t with
    | E => None
    | N v l _ =>
        match leftmostF l with
            | None   => Some v
            | Some x => Some x
        end
end.

Definition leftmost {A : Type} (t : Tree A) : option A :=
match Out t with
    | E => None
    | N v l _ =>
        match leftmostF l with
            | None   => Some v
            | Some x => Some x
        end
end.

Fixpoint mapF {A B X Y : Type} (f : A -> B) (g : X -> Y) (t : TreeF A X) {struct t} : TreeF B Y :=
match t with
    | E       => E
    | N x l r => N (f x) (mapF f g l) (g r)
end.

CoFixpoint map {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
{|
    Out :=
      match Out t with
          | E => E
          | N x l r => N (f x) (mapF f (map f) l) (map f r)
      end;
|}.