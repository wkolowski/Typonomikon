Class Antirelator (F : Type -> Type) : Type :=
{
  antirelate :
    forall {A : Type}, (A -> A -> Prop) -> (F A -> F A -> Prop);
  antirelate_spec :
    forall {A : Type} (x y : F A), antirelate (fun x y => x <> y) x y <-> x <> y;
}.

Class Antibirelator (F : Type -> Type -> Type) : Type :=
{
  antibirelate :
    forall {A B : Type}, (A -> A -> Prop) -> (B -> B -> Prop) -> (F A B -> F A B -> Prop);
  neq_antibirelate :
    forall {A B : Type} (x y : F A B),
      antibirelate (fun a1 a2 => a1 <> a2) (fun b1 b2 => b1 <> b2) x y -> x <> y;
  antirelate_neq :
    forall {A B : Type} (x y : F A B),
      x <> y -> ~ ~ antibirelate (fun a1 a2 => a1 <> a2) (fun b1 b2 => b1 <> b2) x y;
}.

#[export, refine] Instance Antibirelator_prod : Antibirelator prod :=
{
  antibirelate A B RA RB '(a1, b1) '(a2, b2) :=
    RA a1 a2 \/ RB b1 b2;
}.
Proof.
  - now intros A B [a1 b1] [a2 b2] [neq | neq] [= -> ->].
  - intros A B [a1 b1] [a2 b2] neq nor.
    apply nor.
    left; intros ->.
    apply nor.
    right; intros ->.
    now apply neq.
Defined.