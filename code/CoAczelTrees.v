CoInductive CoAczelT@{u} : Type@{u+1} :=
{
  branchingT : Type@{u};
  subtreesT : branchingT -> CoAczelT;
}.

Definition AtomicT : CoAczelT :=
{|
  subtreesT := fun e : Empty_set => match e with end
|}.

Definition PairT (t1 t2 : CoAczelT) : CoAczelT :=
{|
  subtreesT := fun b : bool => if b then t1 else t2
|}.

Definition InfiniteT : CoAczelT :=
{|
  subtreesT := fun _ : nat => AtomicT
|}.

Fail Definition UniversalT : CoAczelT :=
{|
  branchingT := CoAczelT;
  subtreesT := fun t : CoAczelT => t
|}.

Definition SubtreeT (t1 t2 : CoAczelT) : Prop :=
  exists x, subtreesT t2 x = t1.

Set Warnings "-cannot-define-projection".
CoInductive CoAczel : Prop :=
{
  branching : Prop;
  subtrees : branching -> CoAczel;
}.
Set Warnings "cannot-define-projection".

Fail Definition Subtree (t1 t2 : CoAczel) : Prop :=
  exists x, subtrees t2 x = t1.