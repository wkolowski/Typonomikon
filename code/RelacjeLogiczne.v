(** * Na listach *)

Module LogicalRelations_List.

Record ListAlgebra (A : Type) : Type :=
{
  L : Type;
  n : L;
  c : A -> L -> L;
}.

Coercion L : ListAlgebra >-> Sortclass.

Arguments L {A l}.
Arguments n {A l}.
Arguments c {A l} _ _.

Record ListAlgebraHom {A : Type} (L1 L2 : ListAlgebra A) : Type :=
{
  f   : L1 -> L2;
  f_n : f n = n;
  f_c : forall (h : A) (t : L1), f (c h t) = c h (f t);
}.

Record ListAlgebraRel {A : Type} (L1 L2 : ListAlgebra A) : Type :=
{
  R   : L1 -> L2 -> Prop;
  R_n : R n n;
  R_c : forall (h : A) (t1 : L1) (t2 : L2), R t1 t2 -> R (c h t1) (c h t2);
}.

Record ListAlgebraPred {A : Type} (L : ListAlgebra A) : Type :=
{
  P   : L -> Prop;
  P_n : P n;
  P_c : forall (h : A) (t : L), P t -> P (c h t);
}.

End LogicalRelations_List.

(** * Na monoidach *)

Module LogicalRelations_Monoid.

Record Monoid : Type :=
{
  A : Type;
  op : A -> A -> A;
  op_assoc : forall x y z, op (op x y) z = op x (op y z);
  id : A;
  op_id_l : forall x, op id x = x;
  op_id_r : forall x, op x id = x;
}.

Coercion A : Monoid >-> Sortclass.

Arguments op {m} _.
Arguments id {m}.

Record MonoidHom (M1 M2 : Monoid) : Type :=
{
  f    : M1 -> M2;
  f_op : forall x y, f (op x y) = op (f x) (f y);
  f_id : f id = id;
}.

Record MonoidRel (M1 M2 : Monoid) : Type :=
{
  R    : M1 -> M2 -> Prop;
  R_op : forall x1 x2 y1 y2, R x1 x2 -> R y1 y2 -> R (op x1 y1) (op x2 y2);
  R_id : R id id;
}.

Record MonoidPred (M : Monoid) : Type :=
{
  P    : M -> Prop;
  P_op : forall {x y}, P x -> P y -> P (op x y);
  P_id : P id;
}.

End LogicalRelations_Monoid.