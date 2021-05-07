(** Przemyślenia: w uniwersum [SProp] prawo wyłączonego środka jest w słumie
    słuszne, ponieważ mimo bycia aksjomatem normalnie się oblicza. *)

Inductive sor (P Q : SProp) : SProp :=
    | sinl : P -> sor P Q
    | sinr : Q -> sor P Q.

Inductive Empty : SProp := .

Definition snot (P : SProp) : SProp := P -> Empty.

Axiom LEM : forall P : SProp, sor P (snot P).

Lemma jedziemy_na_sor : sor Empty (snot Empty).
Proof.
  right. intro. assumption.
Qed.

Inductive seqs {A : SProp} (x : A) : A -> SProp :=
    | refl : seqs x x.

Lemma lem_sie_oblicza :
  seqs (LEM Empty) jedziemy_na_sor.
Proof.
  reflexivity.
Qed.

Inductive Unit : SProp :=
    | stt : Unit.

Definition b2sp (b : bool) : SProp :=
match b with
    | true  => Unit
    | false => Empty
end.