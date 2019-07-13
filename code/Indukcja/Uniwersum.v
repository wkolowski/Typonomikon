Axioms
  (U : Type)
  (El : U -> Type)

  (Empty : U)
  (Unit : U)
  (Nat : U)
  (Pi : forall (A : U) (B : El A -> U), U)
  (Sigma : forall (A : U) (B : El A -> U), U)
  (UU : U)

  (El_Empty : El Empty = Empty_set)
  (El_Unit : El Unit = unit)
  (El_Nat : El Nat = nat)
  (El_Pi :
    forall (A : U) (B : El A -> U),
      El (Pi A B) = forall (x : El A), El (B x))
  (El_Sigma :
    forall (A : U) (B : El A -> U),
      El (Pi A B) = {x : El A & El (B x)})
  (El_UU : El UU = U)

  (ind : forall
    (P : U -> Type)
    (PEmpty : P Empty)
    (PUnit : P Unit)
    (PNat : P Nat)
    (PPi :
      forall (A : U) (B : El A -> U),
        P A -> (forall x : El A, P (B x)) -> P (Pi A B))
    (PSigma :
      forall (A : U) (B : El A -> U),
        P A -> (forall x : El A, P (B x)) -> P (Sigma A B))
    (PUU : P UU),
      {f : forall A : U, P A |
        (f Empty = PEmpty) /\
        (f Unit = PUnit) /\
        (f Nat = PNat) /\
        (forall (A : U) (B : El A -> U),
          f (Pi A B) =
          PPi A B (f A) (fun x : El A => f (B x))) /\
        (forall (A : U) (B : El A -> U),
          f (Sigma A B) =
          PSigma A B (f A) (fun x : El A => f (B x))) /\
        (f UU = PUU)
      }).