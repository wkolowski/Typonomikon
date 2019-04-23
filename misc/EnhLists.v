Class Monoid : Type :=
{
    carrier :> Type;
    op : carrier -> carrier -> carrier;
    neutr : carrier;
    assoc : forall x y z : carrier, op x (op y z) = op (op x y) z;
    neutr_l : forall x : carrier, op neutr x = x;
    neutr_r : forall x : carrier, op x neutr = x
}.

Coercion carrier : Monoid >-> Sortclass.

Inductive EList (A : Monoid) : A -> Type :=
    | enil : EList A neutr
    | econs : forall h s : A, EList A s -> EList A (op h s).

Arguments EList [A] _.
Arguments enil [A].
Arguments econs [A] _ [s] _.

Print econs.

Definition get {A : Monoid} {s : A} (el : EList s) : A := s.

Class MonHom (X Y : Monoid) : Type :=
{
    func : X -> Y;
    pres_op : forall a b : X, func (op a b) = op (func a) (func b);
    pres_neutr : func neutr = neutr
}.

Coercion func : MonHom >-> Funclass.

Fixpoint fmap {X Y : Monoid} (f : MonHom X Y) (x : X)
    (el : EList x) : EList (f x).
Proof.
  destruct el.
    rewrite pres_neutr. exact enil.
    rewrite pres_op. constructor. apply fmap. assumption.
Defined.





Inductive ListF (A : Set) (f : A -> A -> A) : A -> Set :=
    | nil_F : forall a : A, ListF A f a
    | cons_F : forall acc : A,
        forall a : A, ListF A f acc -> ListF A f (f a acc).

Print nil_F.

Arguments nil_F [A] _ _.
Arguments cons_F [A] [f] [acc] _ _.

Definition extract {A : Set} {f : A -> A -> A} {a : A} (l : ListF A f a) := a.

Eval compute in extract (cons_F 6 (nil_F max 5)).
