Set Universe Polymorphism.

Definition BushC (A : Type) : Type :=
  forall
    (F : Type -> Type)
    (leaf : forall R : Type, F R)
    (node : forall R : Type, R -> F (F R) -> F R)
    (* (R : Type) *), F A.

Definition leaf {A : Type} : BushC A :=
  fun F leaf node (* R *) => leaf A.

Definition node {A : Type} (x : A) (b : BushC (BushC A)) : BushC A.
Proof.
  intros F leaf node (* R *).
  unfold BushC in b.
  
  (* fun F leaf node R =>
    node R x (b F leaf (fun R' x' t' => x' F leaf node R') (F R)).
 *)
Abort.

(* Definition mapC {A B : Type} (f : A -> B) (b : BushC A) : BushC B :=
  fun F leaf node R =>
    b F leaf (fun R a t => node R (f a) t) R.
 *)

(* Fixpoint B2BC {A : Type} (b : Bush A) {struct b} : BushC A :=
match b with
| Leaf => leaf
| Node x b' => node x (B2BC (map B2BC b'))
end.

Definition BC2B {A : Type} (b : BushC A) : Bush A.
Proof.
  unfold BushC in b.
  specialize (b Bush (@Leaf) (@Node)).
 *)