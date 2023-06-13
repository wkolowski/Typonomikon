Module AczelTPolymorphic.

Set Universe Polymorphism.

Inductive AczelT@{u} : Type@{u+1} :=
| AczT : forall {X : Type@{u}}, (X -> AczelT) -> AczelT.

Definition AtomicT : AczelT :=
  AczT (fun e : Empty_set => match e with end).

Definition PairT (t1 t2 : AczelT) : AczelT :=
  AczT (fun b : bool => if b then t1 else t2).

Definition InfiniteT : AczelT :=
  AczT (fun _ : nat => AtomicT).

Fail Definition UniversalT : AczelT :=
  @AczT AczelT (fun t : AczelT => t).

End AczelTPolymorphic.

Module AczelTMonomorphic.

Set Universe Polymorphism.

Inductive AczelT : Type :=
| AczT : forall {X : Set}, (X -> AczelT) -> AczelT.

Definition AtomicT : AczelT :=
  AczT (fun e : Empty_set => match e with end).

Definition PairT (t1 t2 : AczelT) : AczelT :=
  AczT (fun b : bool => if b then t1 else t2).

Definition InfiniteT : AczelT :=
  AczT (fun _ : nat => AtomicT).

Fail Definition UniversalT : AczelT :=
  @AczT AczelT (fun t : AczelT => t).

Definition SubtreeT (s t : AczelT) : Prop :=
match t with
| AczT f => exists x, f x = s
end.

Lemma Irreflexive_SubtreeT :
  forall t : AczelT, ~ SubtreeT t t.
Proof.
  induction t as [X f IH]; cbn.
  intros [x Hfx].
  apply (IH x); red.
  rewrite Hfx.
  exists x. assumption.
Qed.

End AczelTMonomorphic.