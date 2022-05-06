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

Definition leftmost' {A : Type} (t : Tree A) : option A :=
  leftmostF (Out t).

Lemma leftmost_leftmost' :
  forall {A : Type} (t : Tree A),
    leftmost t = leftmost' t.
Proof.
  destruct t as [[]]; cbn; reflexivity.
Qed.

Fixpoint mapF {A B X Y : Type} (f : A -> B) (g : X -> Y) (t : TreeF A X) {struct t} : TreeF B Y :=
match t with
    | E       => E
    | N x l r => N (f x) (mapF f g l) (g r)
end.

(* CoFixpoint map {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
{|
    Out :=
      match Out t with
          | E => E
          | N x l r => N (f x) (mapF f (map f) l) (map f r)
      end;
|}. *)

Fixpoint complete {A : Type} (n : nat) (x : A) (t : Tree A) : TreeF A (Tree A) :=
match n with
    | 0    => E
    | S n' => N x (complete n' x t) t
end.

Fail CoFixpoint complete' {A : Type} (n : nat) (x : A) : Tree A :=
{|
    Out :=
      N x
        ((fix aux (n : nat) : TreeF A (Tree A) :=
          match n with
              | 0 => E
              | S n' => N x (aux n') (complete' n x)
          end) n)
        (complete' n x);
|}.

Require Import F2.

Definition max (n : nat) (m : conat) : conat := max (from_nat n) m.

(* #<a class='link' href='https://www.cse.chalmers.se/~nad/publications/danielsson-docent.pdf'>
   Sprawdź to</a>#. *)

(* Fixpoint max (n : nat) (m : conat) : conat :=
match n, out m with
    | 0   , _ => m
    | S n', S m' => S (max n' m')
 *)

(*Parameter elem : forall A : Type, A -> BTree A -> Prop.*)




(** Basic observers *)
(* Parameter isEmpty : forall A : Type, BTree A -> bool. *)

(* Parameter root : forall A : Type, BTree A -> option A. *)
(* Parameter left : forall A : Type, BTree A -> option (BTree A). *)
(* Parameter right : forall A : Type, BTree A -> option (BTree A). *)

(* Parameter unN : forall A : Type, BTree A -> option (A * BTree A * BTree A). *)

(*
CoFixpoint size {A : Type} (t : Tree A) : conat :=
{|
    out :=
      match Out t with
          | E => Z
          | N _ l r => S (size l) (size r)
      end;
|}.
*)

(* TODO: zdefiniować wincyj funkcji *)
(*
Parameter height : forall A : Type, BTree A -> nat.

Parameter rightmost : forall A : Type, BTree A -> option A.

Parameter inorder : forall A : Type, BTree A -> list A.
Parameter preorder : forall A : Type, BTree A -> list A.
Parameter postorder : forall A : Type, BTree A -> list A.

Parameter bfs_aux :
  forall A : Type, list (BTree A) -> list A -> list A.

Parameter bfs : forall A : Type, BTree A -> list A.

(** Basic operations *)
Parameter mirror' : forall A : Type, BTree A -> BTree A.

Fixpoint mirror {A : Type} (t : BTree A) : BTree A :=
match t with
    | E => E
    | N v l r => N v (mirror r) (mirror l)
end.

(*
Require Import H2.

Lemma mirror_bijective :
  forall A : Type, bijective (@mirror A).
Proof.
  unfold bijective, injective, surjective. split.
    induction x; destruct x'; cbn; inversion 1; subst; clear H.
      reflexivity.
      rewrite (IHx1 _ H3), (IHx2 _ H2). reflexivity.
    induction b.
      exists E. cbn. reflexivity.
      destruct IHb1 as [r Hr], IHb2 as [l Hl].
        exists (N a l r). cbn. rewrite Hl, Hr. reflexivity.
Qed.
*)

Parameter iterate : forall A : Type, (A -> A) -> nat -> A -> BTree A.

Parameter index : forall A : Type, list bool -> BTree A -> option A.
Parameter nth : forall A : Type, nat -> BTree A -> option A.

Parameter take : forall A : Type, nat -> BTree A -> BTree A.
Parameter drop : forall A : Type, nat -> BTree A -> list (BTree A).
Parameter takedrop :
  forall A : Type, nat -> BTree A -> BTree A * list (BTree A).

Parameter intersperse : forall A : Type, A -> BTree A -> BTree A.

Parameter insertAtLeaf :
  forall A : Type, list bool -> BTree A -> BTree A.

(** Operacje z predykatem boolowskim. *)
Parameter any : forall A : Type, (A -> bool) -> BTree A -> bool.
Parameter all : forall A : Type, (A -> bool) -> BTree A -> bool.

Parameter find : forall A : Type, (A -> bool) -> BTree A -> option A.
Parameter findIndex :
  forall A : Type, (A -> bool) -> BTree A -> option (list bool).

Parameter count : forall A : Type, (A -> bool) -> BTree A -> nat.

Parameter takeWhile : forall A : Type, (A -> bool) -> BTree A -> BTree A.

Parameter findIndices :
  forall A : Type, (A -> bool) -> BTree A -> list (list bool).

(** Operacje z funkcją. *)
Parameter map : forall A B : Type, (A -> B) -> BTree A -> BTree B.

Parameter zipWith :
  forall A B C : Type, (A -> B -> C) -> BTree A -> BTree B -> BTree C.

Parameter unzipWith :
 forall A B C : Type, (A -> B * C) -> BTree A -> BTree B * BTree C.

(** foldy i scany *)

(** Predykaty *)

Parameter Elem : forall A : Type, A -> BTree A -> Prop.

Parameter Any : forall A : Type, (A -> Prop) -> BTree A -> Prop.
Parameter All : forall A : Type, (A -> Prop) -> BTree A -> Prop.

Parameter Dup : forall A : Type, BTree A -> Prop.

Parameter Exactly : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtLeast : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtMost : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.

Parameter SameStructure : forall A B : Type, BTree A -> BTree B -> Prop.
Parameter SameShape : forall A B : Type, BTree A -> BTree B -> Prop.

Parameter subtree : forall A : Type, BTree A -> BTree A -> Prop.
Parameter Subterm : forall A : Type, BTree A -> BTree A -> Prop.
*)