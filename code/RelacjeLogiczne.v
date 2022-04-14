(** * Na listach *)

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