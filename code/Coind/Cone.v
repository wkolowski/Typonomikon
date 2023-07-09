Set Primitive Projections.

Inductive ConeF (X A : Type) : Type :=
| Z : A -> ConeF X A
| S : X -> ConeF X A.

Arguments Z {X A} _.
Arguments S {X A} _.

CoInductive Cone (A : Type) : Type := MkCone
{
  Out : ConeF (Cone A) A;
}.

Arguments MkCone {A} _.
Arguments Out {A} _.