Parameter Random : Type -> Type.

Class DigitalSignature : Type :=
{
  PublicKey : Type;
  SecretKey : Type;
  Message : Type;
  Signature : Type;

  generate : Random (PublicKey * SecretKey);
  sign : SecretKey -> Message -> Signature;
  verify : PublicKey -> Message -> Signature -> bool;

  scheme_correct :
    forall (pk : PublicKey) (sk : SecretKey) (m : Message),
      verify pk m (sign sk m) = true;

(*
  scheme_secure :
    no polynomial time adversary can forge signatures without the secret key for fresh message
*)
}.

