Set Universe Polymorphism.

Inductive BushF (F : Type -> Type) (A : Type) : Type :=
| Leaf : BushF F A
| Node : A -> F (F A) -> BushF F A.

Arguments Leaf {F A}.
Arguments Node {F A} _ _.


Unset Positivity Checking.
CoInductive CoBush (A : Type) : Type :=
{
  Out : BushF CoBush A;
}.
Set Positivity Checking.

Arguments Out {A} _.

Unset Guard Checking.
CoFixpoint map {A B : Type} (f : A -> B) (b : CoBush A) : CoBush B :=
{|
    Out :=
      match Out b with
      | Leaf => Leaf
      | Node x b' => Node (f x) (map (map f) b')
      end;
|}.
Set Guard Checking.