Module Peano.

Parameter N : Type.

Parameter Z : N.
Parameter S : N -> N.

Parameter S_inj :
  forall n m : N, S n = S m -> n = m.

Parameter Z_not_S :
  forall n : N, Z <> S n.

Parameter N_rect :
  forall P : N -> Type,
    P Z -> (forall n : N, P n -> P (S n)) -> forall n : N, P n.

End Peano