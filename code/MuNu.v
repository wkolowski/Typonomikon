Require Import List.
Import ListNotations.

Require Import F3 F4.

(*
Inductive Mu (F : Type -> Type) : Type :=
    | In : F (Mu F) -> Mu F.
*)

(*
CoInductive Nu (F : Type -> Type) : Type :=
{
    Out : F (Nu F);
}.
*)

Inductive ListF (F : Type -> Type) (A : Type) : Type :=
    | NilF : ListF F A
    | ConsF : A -> F A -> ListF F A.

Arguments NilF  {F A}.
Arguments ConsF {F A} _ _.

Inductive List (A : Type) : Type :=
    | In : ListF List A -> List A.

Arguments In {A} _.

Lemma List_ind' :
  forall
    {A : Type} (P : List A -> Prop)
    (HNil : P (In NilF))
    (HCons : forall (h : A) (t : List A), P t -> P (In (ConsF h t)))
    (l : List A), P l.
Proof.
  fix IH 5.
  destruct l as [[| h t]].
    exact HNil.
    apply HCons, IH; assumption.
Qed.

Fixpoint list_List {A : Type} (l : list A) : List A :=
match l with
    | [] => In NilF
    | h :: t => In (ConsF h (list_List t))
end.

Fixpoint List_list {A : Type} (l : List A) : list A :=
match l with
    | In NilF => []
    | In (ConsF h t) => h :: List_list t
end.

Lemma list_List_list :
  forall {A : Type} (l : list A),
    List_list (list_List l) = l.
Proof.
  induction l as [| h t]; cbn;
  rewrite ?IHt; reflexivity.
Qed.

Lemma List_list_List :
  forall {A : Type} (l : List A),
    list_List (List_list l) = l.
Proof.
  intros.
  induction l using List_ind'; cbn.
    reflexivity.
    rewrite IHl. reflexivity.
Qed.

CoInductive CoList (A : Type) : Type :=
{
    Out : ListF CoList A;
}.

Arguments Out {A} _.

CoFixpoint coList_CoList {A : Type} (l : coList A) : CoList A :=
{|
    Out :=
      match uncons l with
          | None        => NilF
          | Some (h, t) => ConsF h (coList_CoList t)
      end
|}.

CoFixpoint CoList_coList {A : Type} (l : CoList A) : coList A :=
{|
    uncons :=
      match Out l with
          | NilF      => None
          | ConsF h t => Some (h, CoList_coList t)
      end
|}.

Lemma coList_CoList_coList :
  forall {A : Type} (l : coList A),
    lsim (CoList_coList (coList_CoList l)) l.
Proof.
  cofix CH.
  destruct l as [[[h t] |]];
  constructor; cbn.
    right. do 4 eexists. do 3 (split; try reflexivity). apply CH.
    left. split; reflexivity.
Qed.

CoInductive CoList_sim {A : Type} (l1 l2 : CoList A) : Prop :=
{
    CoList_sim' :
      (Out l1 = NilF /\ Out l2 = NilF)
        \/
      exists h1 t1 h2 t2,
        Out l1 = ConsF h1 t1 /\
        Out l2 = ConsF h2 t2 /\
          CoList_sim t1 t2
}.

Lemma CoList_coList_CoList :
  forall {A : Type} (l : CoList A),
    CoList_sim (coList_CoList (CoList_coList l)) l.
Proof.
  cofix CH.
  destruct l as [[| h t]];
  constructor; cbn.
    left. split; reflexivity.
    right. do 4 eexists. do 2 (split; try reflexivity). apply CH.
Qed.