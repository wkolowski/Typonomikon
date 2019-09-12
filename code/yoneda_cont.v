(** O co chodzi z kontynuacjami?

*)

Definition Cont (R A : Type) : Type := (A -> R) -> R.

Definition f {R A : Type} (x : A) : Cont R A :=
  fun f : A -> R => f x.

Definition g {R A : Type} (h : Cont R A) : A.
Proof.
Abort.

Lemma f_inj :
  forall {R A : Type} (x y : A),
    @f R _ x = f y -> x = y.
Proof.
  intros.
  unfold f in H.
(*  apply (f_equal (fun x : A => x)) in H.*)
Abort.


Definition Cont' (A : Type) : Type := forall R : Type, (A -> R) -> R.

Definition f' {A : Type} (x : A) : Cont' A :=
  fun R f => f x.

Definition g' {A : Type} (h : Cont' A) : A :=
  h _ (fun x : A => x).

Lemma f'_g' :
  forall {A : Type} (x : A),
    g' (f' x) = x.
Proof.
  intros. unfold f'. unfold g'. reflexivity.
Qed.

Lemma g'_f' :
  forall {A : Type} (h : Cont' A),
    f' (g' h) = h.
Proof.
  intros. unfold g'. unfold f'.
  Require Import FunctionalExtensionality.
  extensionality R. extensionality f.
Abort.