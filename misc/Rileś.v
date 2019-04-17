(** Rileś: Koindukcja *)

(** TODO: napisać coś *)

(** * Koindukcja *)

(** TODO: przykład z manuala Agdy *)

CoInductive Stream (A : Type) : Type :=
{
    hd : A;
    tl : Stream A;
}.

Arguments hd {A}.
Arguments tl {A}.

CoInductive bisim {A : Type} (s1 s2 : Stream A) : Prop :=
{
    hds : hd s1 = hd s2;
    tls : bisim (tl s1) (tl s2);
}.

CoFixpoint even {A : Type} (s : Stream A) : Stream A :=
{|
    hd := hd s;
    tl := even (tl (tl s));
|}.

CoFixpoint odd {A : Type} (s : Stream A) : Stream A :=
{|
    hd := hd (tl s);
    tl := odd (tl (tl s));
|}.

Definition split {A : Type} (s : Stream A) : Stream A * Stream A :=
  (even s, odd s).

CoFixpoint merge {A : Type} (ss : Stream A * Stream A) : Stream A :=
{|
    hd := hd (fst ss);
    tl := merge (snd ss, tl (fst ss));
|}.

Lemma merge_split :
  forall (A : Type) (s : Stream A),
    bisim (merge (split s)) s.
Proof.
  cofix CH.
  intros. constructor.
    cbn. reflexivity.
    cbn. constructor.
      cbn. reflexivity.
      cbn. apply CH.
Qed.

(** TODO: kawałek rozdziału 14 z Coq'Art *)

CoInductive Conat : Type :=
{
    pred : option Conat;
}.

CoInductive LList (A : Type) : Type :=
{
    uncons : option (A * LList A);
}.

Arguments uncons {A}.

CoInductive LBTree (A : Type) : Type :=
{
    lbtree' : option (A * LBTree A * LBTree A);
}.

Arguments lbtree' {A}.

(*
Require Export Setoid.

Require Import Coq.Classes.Morphisms.
*)

Require Import List.
Import ListNotations.

Fixpoint toLList {A : Type} (l : list A) : LList A :=
{|
    uncons :=
    match l with
        | [] => None
        | h :: t => Some (h, toLList t)
    end
|}.

Lemma toLList_inj :
  forall {A : Set} (l1 l2 : list A),
    toLList l1 = toLList l2 -> l1 = l2.
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; inversion 1.
    reflexivity.
    f_equal. apply IHt1. assumption.
Defined.

(*
Definition isEmpty {A : Set} (t : LBTree A) : Prop :=

Definition L_root {A : Set} (t : LBTree A) : option A := match t with
    | LEmpty => None
    | LNode v _ _ => Some v
end.

Definition L_left_son {A : Set} (t : LBTree A) : option (LBTree A) :=
match t with
    | LEmpty => None
    | LNode _ l _ => Some l
end.

Definition L_right_son {A : Set} (t : LBTree A) : option (LBTree A) :=
match t with
    | LEmpty => None
    | LNode _ _ r => Some r
end.


Inductive dir : Set := L | R.

Fixpoint L_subtree {A : Set} (l : list dir) (t : LBTree A) : option (LBTree A) :=
match t, l with
    | LEmpty, _ => None
    | t', nil => Some t'
    | LNode v l r, cons L dirs => L_subtree dirs l
    | LNode v l r, cons R dirs => L_subtree dirs r
end.

Fixpoint L_tree_label {A : Set} (l : list dir) (t : LBTree A)
    : option A := match t, l with
    | LEmpty, _ => None
    | LNode v l r, nil => Some v
    | LNode v l r, cons L dirs => L_tree_label dirs l
    | LNode v l r, cons R dirs => L_tree_label dirs r
end.
    (*| LEmpty => None
    | LNode v l r => match l with
        | nil => Some v
        | cons Left dirs => L_tree_label dirs l
        | cons Right dirs => L_tree_label dirs r*)
*)

CoFixpoint from (n : nat) : LList nat :=
{|
    uncons := Some (n, from (S n));
|}.

Definition lhead {A : Type} (l : LList A) : option A :=
match uncons l with
    | Some (a, _) => Some a
    | _ => None
end.

Definition ltail {A : Type} (l : LList A) : option (LList A) :=
match uncons l with
    | Some (_, t) => Some t
    | _ => None
end.

Fixpoint lnth {A : Type} (n : nat) (l : LList A) : option A :=
match n, uncons l with
    | _, None => None
    | 0, Some (x, _) => Some x
    | S n', Some (_, l') => lnth n' l'
end.

Eval compute in lnth 511 (from 0).

Definition nats := from 0.

(*
Definition isEmpty {A : Set} (l : LList A) : Prop := match l with
    | LNil => True
    | _ => False
end.

Definition LTail' {A : Set} (l : LList A) : option (LList A) := match l with
    | LNil => None
    | LCons _ t => Some t
end.

Eval simpl in isEmpty Nats.
Eval compute in from 3.
Eval simpl in LHead (LTail (from 3)).
Eval simpl in LNth 191 (from 341).
*)

CoFixpoint repeat {A : Type} (x : A) : LList A :=
{|
    uncons := Some (x, repeat x);
|}.

Eval simpl in lnth 123 (repeat 5).

CoFixpoint lapp {A : Type} (l1 l2 : LList A) : LList A :=
match uncons l1 with
    | None => l2
    | Some (h, t) => {| uncons := Some (h, lapp t l2) |}
end.



(*
CoFixpoint general_omega {A : Set} (l1 l2 : LList A) : LList A :=
match l1, l2 with
    | _, LNil => l1
    | LNil, LCons h' t' => LCons h' (general_omega t' l2)
    | LCons h t, _ => LCons h (general_omega t l2)
end.
*)

CoFixpoint lmap {A B : Type} (f : A -> B) (l : LList A) : LList B :=
{|
    uncons :=
    match uncons l with
        | None => None
        | Some (h, t) => Some (f h, lmap f t)
    end
|}.

Inductive Finite {A : Type} : LList A -> Prop :=
    | Finite_nil : Finite {| uncons := None |}
    | Finite_cons :
        forall (h : A) (t : LList A),
          Finite t -> Finite {| uncons := Some (h, t) |}.

CoInductive bisim2 {A : Type} (l1 l2 : LList A) : Prop :=
{
    bisim2' :
    match uncons l1, uncons l2 with
        | Some (h1, t1), Some (h2, t2) => h1 = h2
        | _, _ => False
    end;
}.

(*
CoInductive Infinite {A : Type} (l : LList A) : Prop :=
{
    infinite :
    match uncons l with
        | None => False
        | Some (_, t) => Infinite t
    end
}.
*)

(*
Lemma lmap_Infinite :
  forall (A B : Type) (f : A -> B) (l : LList A),
    Infinite l -> Infinite {| uncons := @None (A * LList A) |}. (*(lmap f l).*)
Proof.
  intros.
  inversion H.
  destruct l as [[[h t] |]]; cbn in *.
  Focus 2.

 cbn in *.
 inversion H. cbn in infinite0.
    compute. constructor.
    constructor.
Qed.
    unfold lmap. cbv.

Lemma lmap_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : LList A),
    lmap g (lmap f l) = lmap (fun x => g (f x)) l.
Proof.
  intros.
*)