(** * X4: Listy niepuste *)
(* begin hide *)

Inductive nel (A : Type) : Type :=
    | singl : A -> nel A
    | nel_cons : A -> nel A -> nel A.

Arguments singl [A] _.
Arguments nel_cons [A] _ _.

Notation "[ x ]" := (singl x).
Notation "h :: t" := (nel_cons h t).

Fixpoint foldr {A B : Type} (f : A -> B -> B) (b : B) (l : nel A) : B :=
match l with
    | [a] => f a b
    | h :: t => f h (foldr f b t)
end.

Definition len {A : Type} := foldr (fun (_ : A) n => S n) 0.

Fixpoint map {A B : Type} (f : A -> B) (l : nel A) : nel B :=
match l with
    | [a] => singl (f a)
    | h :: t => nel_cons (f h) (map f t)
end.

(* Definition map' {A B : Type} (f : A -> B) := fold (fun a b => f a :: b). *)

Eval compute in len (nel_cons 5 (singl 2)).

Definition hd {A : Type} (l : nel A) : A :=
match l with
    | singl a => a
    | nel_cons a _ => a
end.

Fixpoint last {A} (l : nel A) : A :=
match l with
    | [a] => a
    | nel_cons _ t => last t
end.

Eval compute in (hd [2]).

Definition tl {A : Type} (l : nel A) : option (nel A) :=
match l with
    | singl _ => None
    | nel_cons _ t => Some t
end.

Theorem map_pres_len : forall {A B : Type} (f : A -> B) (l : nel A),
    len l = len (map f l).
Proof.
  induction l; unfold len in *; cbn; auto.
Qed.

Fixpoint app {A} (l1 l2 : nel A) : nel A :=
match l1 with
    | singl a => nel_cons a l2
    | nel_cons h t => nel_cons h (app t l2)
end.

Notation "l1 ++ l2" := (app l1 l2).

Hint Unfold len.

Theorem app_length : forall {A} (l1 l2 : nel A),
    len (l1 ++ l2) = len l1 + len l2.
Proof.
  induction l1; destruct l2; unfold len in *; cbn;
  try rewrite IHl1; auto.
Qed.

Fixpoint nth {A} (n : nat) (l : nel A) : option A :=
match n with
    | 0 => Some (hd l)
    | S n' => match l with
        | [_] => None
        | _ :: t => nth n' t
    end
end.

Inductive inb {A} : A -> nel A -> Prop :=
    | inb_singl : forall a : A, inb a [a]
    | inb_cons : forall (a h : A) (t : nel A),
        inb a t -> inb a (h :: t).

Fixpoint rev {A} (l : nel A) : nel A :=
match l with
    | [a] => [a]
    | h :: t =>
        (fix aux (l acc : nel A) : nel A :=
        match l with
            | [a] => a :: acc
            | h :: t => aux t (h :: acc)
        end) t (singl h)
end.

Eval compute in rev (2 :: 3 :: 4 :: 5 :: [6]).

Fixpoint zip {A B : Type} (l1 : nel A) (l2 : nel B) : nel (A * B) :=
match l1, l2 with
    | [a], [b] => singl (a, b)
    | [a], h' :: _ => singl (a, h')
    | h :: _, [b] => singl (h, b)
    | h :: t, h' :: t' => (h, h') :: zip t t'
end.

(* end hide *)