(** * D2d: Rekursja wyższego rzędu [TODO] *)

Require Import Equality Eqdep FunctionalExtensionality.

(** * Rząd rżnie głupa, czyli o pierwszym i wyższym rzędzie (TODO) *)

(** * Przykładowy typ *)

Module ExampleType.

Inductive Tree (A : Type) : Type :=
| Node : A -> forall {B : Type}, (B -> Tree A) -> Tree A.

Arguments Node {A} _ _ _.

(** Tym razem mamy drzewo, które może mieć naprawdę dowolną ilość poddrzew,
    ale jego poddrzewa są nieuporządkowane. *)

Definition compose {A B C : Type} (f : A -> B) (g : B -> C) : A -> C :=
  fun x : A => g (f x).

Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
match t with
| Node x B ts => Node x B (fun b : B => mirror (ts b))
end.

Fixpoint mirror' {A : Type} (t : Tree A) : Tree A :=
match t with
| Node x B ts => Node x B (compose ts mirror')
end.

Lemma mirror_mirror' :
  forall {A : Type} (t : Tree A),
    mirror t = mirror' t.
Proof.
  reflexivity.
Qed.

End ExampleType.

(** * Szerokie drzewka (TODO) *)

Module WideTree.

Inductive WideTree (A : Type) : Type :=
| E
| N (v : A) (ts : nat -> WideTree A).

End WideTree.

(** * Szerokie wisienki (TODO) *)

Module WideRoseTree.

Inductive WideRoseTree (A : Type) : Type :=
| L (x : A)
| N (ts : nat -> WideRoseTree A).

End WideRoseTree.

(** * Drzewka z nieskończonym rozgałęzieniem (TODO) *)

Module InfTree.

Inductive InfTree (B A : Type) : Type :=
| E : InfTree B A
| N : A -> (B -> InfTree B A) -> InfTree B A.

Arguments E {B A}.
Arguments N {B A} _ _.

Definition leaf {A : Type} (x : A) : InfTree False A :=
  N x (fun e : False => match e with end).

Definition isEmpty {B A : Type} (t : InfTree B A) : bool :=
match t with
| E => true
| _ => false
end.

Definition root {B A : Type} (t : InfTree B A) : option A :=
match t with
| E => None
| N x _ => Some x
end.

Definition unN {B A : Type} (t : InfTree B A)
  : option (A * {B : Type & B -> InfTree B A}) :=
match t with
| E => None
| N x f => Some (x, @existT Type _ B f)
end.

(** Zagadka, że o ja jebie: udowodnij, że funkcji [size] i [height] nie da
    się zaimplementować. *)

(*
Parameter size : forall A : Type, BTree A -> nat.
Parameter height : forall A : Type, BTree A -> nat.
*)

(*
Parameter leftmost : forall A : Type, BTree A -> option A.
Parameter rightmost : forall A : Type, BTree A -> option A.

Parameter inorder : forall A : Type, BTree A -> list A.
Parameter preorder : forall A : Type, BTree A -> list A.
Parameter postorder : forall A : Type, BTree A -> list A.

Parameter bfs_aux :
  forall A : Type, list (BTree A) -> list A -> list A.

Parameter bfs : forall A : Type, BTree A -> list A.
*)

(*
Parameter mirror' : forall A : Type, BTree A -> BTree A.
*)

Fixpoint complete {B A : Type} (n : nat) (x : A) : InfTree B A :=
match n with
| 0 => E
| S n' => N x (fun _ => complete n' x)
end.

Fixpoint iterate
  {B A : Type} (f : A -> A) (n : nat) (x : A) : InfTree B A :=
match n with
| 0 => E
| S n' => N x (fun _ => iterate f n' (f x))
end.

Fixpoint take {B A : Type} (n : nat) (t : InfTree B A) : InfTree B A :=
match n, t with
| 0, _ => E
| _, E => E
| S n', N x f => N x (fun b : B => take n' (f b))
end.

(*
Parameter index : forall A : Type, list bool -> BTree A -> option A.
Parameter nth : forall A : Type, nat -> BTree A -> option A.
*)

(*
Parameter drop : forall A : Type, nat -> BTree A -> list (BTree A).
Parameter takedrop :
  forall A : Type, nat -> BTree A -> BTree A * list (BTree A).
*)

Fixpoint intersperse {B A : Type} (v : A) (t : InfTree B A) : InfTree B A :=
match t with
| E => E
| N x f => N x (fun _ => N v (fun b => intersperse v (f b)))
end.

(*
Parameter insertAtLeaf :
  forall A : Type, list bool -> BTree A -> BTree A.
*)

(*
Parameter any : forall A : Type, (A -> bool) -> BTree A -> bool.
Parameter all : forall A : Type, (A -> bool) -> BTree A -> bool.
*)

(*
Parameter find : forall A : Type, (A -> bool) -> BTree A -> option A.
Parameter findIndex :
  forall A : Type, (A -> bool) -> BTree A -> option (list bool).
*)

(*
Parameter count : forall A : Type, (A -> bool) -> BTree A -> nat.
*)


Fixpoint takeWhile
  {B A : Type} (p : A -> bool) (t : InfTree B A) : InfTree B A :=
match t with
| E => E
| N x f => if p x then N x (fun b : B => takeWhile p (f b)) else E
end.

(*
Parameter findIndices :
  forall A : Type, (A -> bool) -> BTree A -> list (list bool).
*)

Fixpoint map {A B C : Type} (f : B -> C) (t : InfTree A B) : InfTree A C :=
match t with
| E => E
| N x g => N (f x) (fun a : A => map f (g a))
end.

Fixpoint zipWith
  {A B C D : Type} (f : B -> C -> D)
  (t1 : InfTree A B) (t2 : InfTree A C) : InfTree A D :=
match t1, t2 with
| E, _ => E
| _, E => E
| N x g, N y h => N (f x y) (fun a : A => zipWith f (g a) (h a))
end.

(*
Parameter unzipWith :
 forall A B C : Type, (A -> B * C) -> BTree A -> BTree B * BTree C.
*)

(** Predykaty *)

Inductive Elem {B A : Type} (x : A) : InfTree B A -> Prop :=
| Elem_here :
    forall f : B -> InfTree B A, Elem x (N x f)
| Elem_there :
    forall (f : B -> InfTree B A) (b : B),
      Elem x (f b) -> Elem x (N x f).

Inductive Exists {B A : Type} (P : A -> Prop) : InfTree B A -> Prop :=
| Exists_here :
    forall (x : A) (f : B -> InfTree B A),
      P x -> Exists P (N x f)
| Exists_there :
    forall (x : A) (f : B -> InfTree B A) (b : B),
      Exists P (f b) -> Exists P (N x f).

Inductive Forall {B A : Type} (P : A -> Prop) : InfTree B A -> Prop :=
| Forall_E : Forall P E
| Forall_N :
    forall (x : A) (f : B -> InfTree B A),
      (forall b : B, Forall P (f b)) -> Forall P (N x f).

(*
Parameter Dup : forall A : Type, BTree A -> Prop.

Parameter Exactly : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtLeast : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtMost : forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
*)

Inductive SameShape
  {A B C : Type} : InfTree A B -> InfTree A C -> Prop :=
| SS_E : SameShape E E
| SS_N :
    forall
      (x : B) (y : C)
      (f : A -> InfTree A B) (g : A -> InfTree A C),
        (forall a : A, SameShape (f a) (g a)) ->
          SameShape (N x f) (N y g).

Inductive InfTreeDirectSubterm
  {B A : Type} : InfTree B A -> InfTree B A -> Prop :=
| ITDS_E :
    forall (x : A) (f : B -> InfTree B A) (b : B),
      InfTreeDirectSubterm (f b) (N x f).

Inductive InfTreeSubterm
  {B A : Type} : InfTree B A -> InfTree B A -> Prop :=
| ITS_refl :
    forall t : InfTree B A, InfTreeSubterm t t
| ITS_step :
    forall t1 t2 t3 : InfTree B A,
      InfTreeDirectSubterm t1 t2 -> InfTreeSubterm t2 t3 ->
        InfTreeSubterm t1 t3.

Inductive InfTreeEq
  {B A : Type} : InfTree B A -> InfTree B A -> Prop :=
| ITE_E : InfTreeEq E E
| ITE_N :
    forall (v1 v2 : A) (f1 f2 : B -> InfTree B A),
      v1 = v2 -> (forall b : B, InfTreeEq (f1 b) (f2 b)) ->
        InfTreeEq (N v1 f1) (N v2 f2).

Lemma decode :
  forall {B A : Type} {t1 t2 : InfTree B A},
    InfTreeEq t1 t2 -> t1 = t2.
Proof.
  induction 1.
    reflexivity.
    f_equal.
      assumption.
      apply functional_extensionality. intro x. apply H1.
Restart.
  fix IH 5.
  destruct 1.
    reflexivity.
    f_equal.
      assumption.
      apply functional_extensionality. intro. apply IH, H0.
Defined.

Lemma encode :
  forall {B A : Type} {t1 t2 : InfTree B A},
    t1 = t2 -> InfTreeEq t1 t2.
Proof.
  destruct 1.
  induction t1; constructor.
    reflexivity.
    assumption.
Restart.
  fix IH 3.
  destruct t1, 1.
  - constructor.
  - constructor.
    + congruence.
    + intros; apply IH; congruence.
Defined.

Lemma encode_decode :
  forall {B A : Type} {t1 t2 : InfTree B A} (p : t1 = t2),
    decode (encode p) = p.
Proof.
  destruct p.
  induction t1; cbn.
  - reflexivity.
  - rewrite eq_trans_refl_l.
    generalize (functional_extensionality i i (fun x : B => decode
      (InfTree_ind B A (fun t1 : InfTree B A => InfTreeEq t1 t1) ITE_E
        (fun (a0 : A) (i0 : B -> InfTree B A) (H0 : forall b : B, InfTreeEq (i0 b) (i0 b)) =>
        ITE_N a0 a0 i0 i0 eq_refl H0) (i x)))).
Abort.

Scheme InfTreeEq_ind' := Induction for InfTreeEq Sort Prop.

Lemma decode_encode :
  forall {B A : Type} {t1 t2 : InfTree B A} (c : InfTreeEq t1 t2),
    encode (decode c) = c.
Proof.
  induction c using InfTreeEq_ind'; cbn.
  - reflexivity.
  - destruct e; cbn.
    rewrite eq_trans_refl_l.
    generalize (functional_extensionality f1 f2 (fun x : B => decode (i x))).
    destruct e; cbn.
    f_equal.
    extensionality y.
    rewrite <- H.
Abort.

End InfTree.

(** * Drzewka z bardzo nieskończonym rozgałęzieniem (TODO) *)

Module VeryInfTree.

Inductive InfTree (A : Type) : Type :=
| E : InfTree A
| N : A -> forall (B : Type), (B -> InfTree A) -> InfTree A.

Arguments E {A}.
Arguments N {A} _ _ _.

Definition leaf {A : Type} (x : A) : InfTree A :=
  N x False (fun e => match e with end).

(** Basic observers *)
Definition isEmpty {A : Type} (t : InfTree A) : bool :=
match t with
| E => true
| _ => false
end.

Definition root {A : Type} (t : InfTree A) : option A :=
match t with
| E => None
| N x _ _ => Some x
end.

Definition unN {A : Type} (t : InfTree A)
  : option (A * {B : Type & B -> InfTree A}) :=
match t with
| E => None
| N x B f => Some (x, @existT Type _ B f)
end.

(** Zagadka, że o ja jebie: udowodnij, że funkcji [size] i [height] nie da
    się zaimplementować. *)

(*
Parameter size : forall A : Type, BTree A -> nat.
Parameter height : forall A : Type, BTree A -> nat.
*)

(*
Parameter leftmost : forall A : Type, BTree A -> option A.
Parameter rightmost : forall A : Type, BTree A -> option A.

Parameter inorder : forall A : Type, BTree A -> list A.
Parameter preorder : forall A : Type, BTree A -> list A.
Parameter postorder : forall A : Type, BTree A -> list A.

Parameter bfs_aux :
  forall A : Type, list (BTree A) -> list A -> list A.

Parameter bfs : forall A : Type, BTree A -> list A.
*)

(*
Parameter mirror' : forall A : Type, BTree A -> BTree A.
*)

Fixpoint complete {A : Type} (B : Type) (n : nat) (x : A) : InfTree A :=
match n with
| 0 => E
| S n' => N x B (fun _ => complete B n' x)
end.

Fixpoint iterate
  {A : Type} (B : Type) (f : A -> A) (n : nat) (x : A) : InfTree A :=
match n with
| 0 => E
| S n' => N x B (fun _ => iterate B f n' (f x))
end.

Fixpoint take {A : Type} (n : nat) (t : InfTree A) : InfTree A :=
match n, t with
| 0, _ => E
| _, E => E
| S n', N x B f => N x B (fun b : B => take n' (f b))
end.

(*
Parameter index : forall A : Type, list bool -> BTree A -> option A.
Parameter nth : forall A : Type, nat -> BTree A -> option A.
*)

(*
Parameter drop : forall A : Type, nat -> BTree A -> list (BTree A).
Parameter takedrop :
  forall A : Type, nat -> BTree A -> BTree A * list (BTree A).
*)

Definition intersperse {A : Type} (v : A) (t : InfTree A) : InfTree A :=
match t with
| E => N v False (fun e => match e with end)
| N x B f => N x B (fun _ => N v B f)
end.

(*
Parameter insertAtLeaf :
  forall A : Type, list bool -> BTree A -> BTree A.
*)

(*
Parameter any : forall A : Type, (A -> bool) -> BTree A -> bool.
Parameter all : forall A : Type, (A -> bool) -> BTree A -> bool.
*)

(*
Parameter find : forall A : Type, (A -> bool) -> BTree A -> option A.
Parameter findIndex :
  forall A : Type, (A -> bool) -> BTree A -> option (list bool).
*)

(*
Parameter count : forall A : Type, (A -> bool) -> BTree A -> nat.
*)

Fixpoint takeWhile {A : Type} (p : A -> bool) (t : InfTree A) : InfTree A :=
match t with
| E => E
| N x B f => if p x then N x B (fun b : B => takeWhile p (f b)) else E
end.

(*
Parameter findIndices :
  forall A : Type, (A -> bool) -> BTree A -> list (list bool).
*)

Fixpoint map {A B : Type} (f : A -> B) (t : InfTree A) : InfTree B :=
match t with
| E => E
| N x C g => N (f x) C (fun c : C => map f (g c))
end.

(*
Fixpoint zipWith
  {A B C : Type} (f : A -> B -> C)
  (t1 : InfTree A) (t2 : InfTree B) : InfTree C :=
match t1, t2 with
| E, _ => E
| _, E => E
| N a D f, N b E g => N (f a b) (fun 
*)

(*
Parameter unzipWith :
 forall A B C : Type, (A -> B * C) -> BTree A -> BTree B * BTree C.
*)

(** Predykaty *)

(** [Elem] jest głupie - po co ma istnieć, skoro jest [Exists]? *)
Inductive Elem {A : Type} (x : A) : InfTree A -> Prop :=
| Elem_here :
    forall (B : Type) (f : B -> InfTree A),
      Elem x (N x B f)
| Elem_there :
    forall (B : Type) (f : B -> InfTree A) (b : B),
      Elem x (f b) -> Elem x (N x B f).

Inductive Exists {A : Type} (P : A -> Prop) : InfTree A -> Prop :=
| Exists_here :
    forall (x : A) (B : Type) (f : B -> InfTree A),
      P x -> Exists P (N x B f)
| Exists_there :
    forall (x : A) (B : Type) (f : B -> InfTree A) (b : B),
      Exists P (f b) -> Exists P (N x B f).

Inductive Forall {A : Type} (P : A -> Prop) : InfTree A -> Prop :=
| Forall_E : Forall P E
| Forall_N :
    forall (x : A) (B : Type) (f : B -> InfTree A),
      (forall b : B, Forall P (f b)) -> Forall P (N x B f).

Inductive Dup {A : Type} (P : A -> Prop) : InfTree A -> Prop :=
| Dup_here :
    forall v : A, P v ->
      forall (B : Type) (f : B -> InfTree A) (b : B),
        Exists P (f b) -> Dup P (N v B f)
| Dup_subtrees :
    forall (v : A) (B : Type) (f : B -> InfTree A) (b1 b2 : B),
      Exists P (f b1) -> Exists P (f b2) ->
        b1 <> b2 -> Dup P (N v B f)
| Dup_deeper :
    forall (v : A) (B : Type) (f : B -> InfTree A) (b : B),
      Dup P (f b) -> Dup P (N v B f).

(*
Parameter Exactly :
  forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtLeast :
  forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
Parameter AtMost :
  forall A : Type, (A -> Prop) -> nat -> BTree A -> Prop.
*)

Inductive SameStructure {A B : Type} : InfTree A -> InfTree B -> Prop :=
| SS_E : SameStructure E E
| SS_N :
    forall
      (x : A) (y : B) (C : Type)
      (f : C -> InfTree A) (g : C -> InfTree B),
        (forall c : C, SameStructure (f c) (g c)) ->
          SameStructure (N x C f) (N y C g).

(*
Parameter SameShape : forall A B : Type, BTree A -> BTree B -> Prop.
*)

Inductive InfTreeDirectSubterm
  {A : Type} : InfTree A -> InfTree A -> Prop :=
| ITDS :
    forall (x : A) (B : Type) (f : B -> InfTree A) (b : B),
      InfTreeDirectSubterm (f b) (N x B f).

Inductive InfTreeSubterm
  {A : Type} : InfTree A -> InfTree A -> Prop :=
| ITS_refl :
    forall t : InfTree A, InfTreeSubterm t t
| ITS_step :
    forall t1 t2 t3 : InfTree A,
      InfTreeDirectSubterm t1 t2 -> InfTreeSubterm t2 t3 ->
        InfTreeSubterm t1 t3.

Inductive InfTreeEq {A : Type} : InfTree A -> InfTree A -> Prop :=
| ITE_E : InfTreeEq E E
| ITE_N :
    forall {v1 v2 : A} {B : Type} {f1 f2 : B -> InfTree A},
      v1 = v2 -> (forall b : B, InfTreeEq (f1 b) (f2 b)) ->
        InfTreeEq (N v1 B f1) (N v2 B f2).

Arguments ITE_E {A}.
Arguments ITE_N {A v1 v2 B f1 f2} _ _.

Fixpoint encode_aux {A : Type} (t : InfTree A) : InfTreeEq t t :=
match t with
| E => ITE_E
| N v B f =>
        ITE_N eq_refl (fun b => encode_aux (f b))
end.

Definition encode
  {A : Type} {t1 t2 : InfTree A} (p : t1 = t2) : InfTreeEq t1 t2 :=
match p with
| eq_refl => encode_aux t1
end.

Fixpoint decode
  {A : Type} {t1 t2 : InfTree A} (c : InfTreeEq t1 t2) : t1 = t2.
Proof.
  destruct c.
    reflexivity.
    f_equal.
      assumption.
      apply functional_extensionality. intro. apply decode.
        apply H0.
Defined.

Lemma encode_decode :
  forall {A : Type} {t1 t2 : InfTree A} (p : t1 = t2),
    decode (encode p) = p.
Proof.
  destruct p; cbn.
  induction t1; cbn; intros.
    reflexivity.
    rewrite eq_trans_refl_l.
Admitted.

Scheme InfTreeEq_ind' := Induction for InfTreeEq Sort Prop.

Lemma decode_encode :
  forall {A : Type} {t1 t2 : InfTree A} (c : InfTreeEq t1 t2),
    encode (decode c) = c.
Proof.
  induction c using InfTreeEq_ind'; cbn.
    reflexivity.
    destruct e. rewrite eq_trans_refl_l.
Admitted.

Lemma isProp_InfTreeEq :
  forall {A : Type} {t1 t2 : InfTree A} (c1 c2 : InfTreeEq t1 t2),
    c1 = c2.
Proof.
  induction c1 using InfTreeEq_ind';
  dependent destruction c2.
    reflexivity.
    f_equal. apply functional_extensionality_dep_good.
      intro. apply H.
Qed.

Inductive InfTreeNeq {A : Type} : InfTree A -> InfTree A -> Prop :=
| InfTreeNeq_EN :
    forall (v : A) {B : Type} (f : B -> InfTree A),
      InfTreeNeq E (N v B f)
| InfTreeNeq_NE :
    forall (v : A) {B : Type} (f : B -> InfTree A),
      InfTreeNeq (N v B f) E
| InfTreeNeq_NN_here :
    forall (v1 v2 : A) {B : Type} (f1 f2 : B -> InfTree A),
      v1 <> v2 -> InfTreeNeq (N v1 B f1) (N v2 B f2)
| InfTreeNeq_NN_there :
    forall (v1 v2 : A) {B : Type} (f1 f2 : B -> InfTree A) (b : B),
      InfTreeNeq (f1 b) (f2 b) -> InfTreeNeq (N v1 B f1) (N v2 B f2)
| InfTreeNeq_branching :
    forall
      (v1 v2 : A) (B1 B2 : Type) (f1 : B1 -> InfTree A) (f2 : B2 -> InfTree A),
        B1 <> B2 -> InfTreeNeq (N v1 B1 f1) (N v2 B2 f2).

Lemma InfTreeNeq_neq :
  forall {A : Type} {t1 t2 : InfTree A},
    InfTreeNeq t1 t2 -> t1 <> t2.
Proof.
  induction 1; inversion 1; subst; try contradiction.
  apply inj_pair2 in H3. subst. contradiction.
Qed.

End VeryInfTree.

(** * Wisienki z bardzo nieskończonym rozgałęzieniem (TODO) *)

Inductive InfWisienka (A : Type) : Type :=
| L1 : A -> InfWisienka A
| N1 : forall {B : Type}, (B -> InfWisienka A) -> InfWisienka A.