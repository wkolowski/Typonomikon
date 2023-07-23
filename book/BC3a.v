(** * BC3a: Programowanie funkcyjne z typami zależnymi [TODO] *)

(** * Typy zależne, czyli typowanie statyczne na sterydach *)

(** * Uniwersum (TODO) *)

(** * Funkcje zależne (TODO) *)

(** * Pary zależne (TODO) *)

(** * Indeksowane enumeracje (TODO) *)

(* begin hide *)
(*
TODO: Maszyny stanowe i type-driven design jako ćwiczenia
TODO: do (indeksowanych) enumeracji.
*)
(* end hide *)

(** * Rekordy zależne *)

(** * Równość (TODO) *)

(** * Równość a ścieżki *)

Inductive Path {A : Type} (x : A) : A -> Type :=
| idp : Path x x.

Arguments idp {A x}.

Definition eq_to_Path {A : Type} {x y : A} (e : x = y) : Path x y :=
match e with
| eq_refl => idp
end.

Definition Path_to_eq {A : Type} {x y : A} (p : Path x y) : x = y :=
match p with
| idp => eq_refl
end.

Lemma eq_to_Path_to_eq :
  forall {A : Type} {x y : A} (e : x = y),
    Path_to_eq (eq_to_Path e) = e.
Proof.
  destruct e. cbn. reflexivity.
Qed.

Lemma Path_to_eq_to_Path :
  forall {A : Type} {x y : A} (p : Path x y),
    eq_to_Path (Path_to_eq p) = p.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Lemma eq_to_Path_to_eq' :
  forall {A : Type} {x y : A} (e : x = y),
    Path (Path_to_eq (eq_to_Path e)) e.
Proof.
  destruct e. cbn. reflexivity.
Defined.

Lemma Path_to_eq_to_Path' :
  forall {A : Type} {x y : A} (p : Path x y),
    Path (eq_to_Path (Path_to_eq p)) p.
Proof.
  destruct p. cbn. reflexivity.
Defined.