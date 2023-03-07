Inductive BushF (F : Type -> Type) (A : Type) : Type :=
| E : BushF F A
| N : A -> F (F A) -> BushF F A.

Arguments E {F A}.
Arguments N {F A} _ _.

Fail Inductive Bush (A : Type) : Type :=
| In : BushF Bush A -> Bush A.

Definition mapF
  {F : Type -> Type} {A B : Type}
  (rec : forall {X Y : Type}, (X -> Y) -> F X -> F Y)
  (f : A -> B) (t : BushF F A) : BushF F B :=
match t with
| E => E
| N v t' => N (f v) (rec (rec f) t')
end.