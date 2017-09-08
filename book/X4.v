(** * X4: Listy niepuste *)
(* begin hide *)

Inductive Nel (A : Type) : Type :=
    | singl : A -> Nel A
    | nel_cons : A -> Nel A -> Nel A.

Arguments singl [A] _.
Arguments nel_cons [A] _ _.

Notation "[ x ]" := (singl x).
Notation "h :: t" := (nel_cons h t).
Notation "[ x ; y ]" := (nel_cons x (singl y)).
Notation "[ x ; .. ; z ; w ]" :=
    (nel_cons x .. (nel_cons z (singl w)) ..).

Fixpoint fold {A B : Type} (f : A -> B -> B) (b : B) (l : Nel A) : B :=
match l with
    | [a] => f a b
    | h :: t => f h (fold f b t)
end.

Definition len {A : Type} := fold (fun (_ : A) n => S n) 0.

Fixpoint map {A B : Type} (f : A -> B) (l : Nel A) : Nel B :=
match l with
    | [a] => singl (f a)
    | h :: t => nel_cons (f h) (map f t)
end.

(* Definition map' {A B : Type} (f : A -> B) := fold (fun a b => f a :: b). *)

Eval compute in len (nel_cons 5 (singl 2)).

Definition hd {A : Type} (l : Nel A) : A :=
match l with
    | singl a => a
    | nel_cons a _ => a
end.

Fixpoint last {A} (l : Nel A) : A :=
match l with
    | [a] => a
    | nel_cons _ t => last t
end.

Eval compute in (hd [2]).

Definition tl {A : Type} (l : Nel A) : option (Nel A) :=
match l with
    | singl _ => None
    | nel_cons _ t => Some t
end.

Theorem map_pres_len : forall {A B : Type} (f : A -> B) (l : Nel A),
    len l = len (map f l).
Proof.
  induction l; unfold len in *; simpl; auto.
Qed.

Fixpoint app {A} (l1 l2 : Nel A) : Nel A :=
match l1 with
    | singl a => nel_cons a l2
    | nel_cons h t => nel_cons h (app t l2)
end.

Notation "l1 ++ l2" := (app l1 l2).

Hint Unfold len.

Theorem app_length : forall {A} (l1 l2 : Nel A),
    len (l1 ++ l2) = len l1 + len l2.
Proof.
  induction l1; destruct l2; unfold len in *; simpl;
  try rewrite IHl1; auto.
Qed.

Fixpoint nth {A} (n : nat) (l : Nel A) : option A :=
match n with
    | 0 => Some (hd l)
    | S n' => match l with
        | [_] => None
        | _ :: t => nth n' t
    end
end.

Inductive inb {A} : A -> Nel A -> Prop :=
    | inb_singl : forall a : A, inb a [a]
    | inb_cons : forall (a h : A) (t : Nel A),
        inb a t -> inb a (h :: t).

Fixpoint rev {A} (l : Nel A) : Nel A :=
match l with
    | [a] => [a]
    | h :: t =>
        (fix aux (l acc : Nel A) : Nel A :=
        match l with
            | [a] => a :: acc
            | h :: t => aux t (h :: acc)
        end) t (singl h)
end.

Eval compute in rev (2 :: 3 :: 4 :: 5 :: [6]).

Fixpoint zip {A B : Type} (l1 : Nel A) (l2 : Nel B) : Nel (A * B) :=
match l1, l2 with
    | [a], [b] => singl (a, b)
    | [a], h' :: _ => singl (a, h')
    | h :: _, [b] => singl (h, b)
    | h :: t, h' :: t' => (h, h') :: zip t t'
end.

(* end hide *)

