CoInductive Tree (A : Type) : Type :=
{
    root : option (Tree A * A * Tree A)
}.

Arguments root {A} _.

CoFixpoint fmap {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
{|
    root :=
    match root t with
        | None => None
        | Some (l, v, r) => Some (fmap f l, f v, fmap f r)
    end
|}.

CoFixpoint ns (n : nat) : Tree nat :=
{|
    root := Some (ns n, n, ns n)
|}.

Definition Tree_comp {A : Type} (t : Tree A) : Tree A :=
match root t with
    | None => {| root := None |}
    | Some p => {| root := Some p |}
end.

Lemma Tree_comp_eq :
  forall (A : Type) (t : Tree A),
    t = Tree_comp t.
Proof.
  intros. unfold Tree_comp. destruct t, root0; reflexivity.
Defined.

Lemma fmap_S_ns :
  forall n : nat,
    fmap S (ns n) = ns (S n).
Proof.
  induction n as [| n'].
    rewrite (Tree_comp_eq _ (ns 0)). unfold Tree_comp.
      destruct (ns 0), root0; cbn. 
    destruct (ns 0). destruct root0 as [[[l v] r] |]. cbn.
Restart.