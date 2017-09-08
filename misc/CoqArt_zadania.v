(* Ćwiczenia z Coq'Art *)

(** Ex. 3.2 Rozpoznaj typ ([nat] oznacza liczby naturalne):
    - [fun a b c : nat => b * b - 4 * a * c]
Moje: 
    - [fun n : nat => n]
    - [fun (f : A -> B) (a : A) => f]
    - [fun (f : A -> B) (a : A) => f a]
    - [fun (f : A -> A -> A) (a b : A) => f (f b b)]
    - [fun (f : A -> B) (g : B -> C) => fun a : A => g (f a)]
    - [fun n _ : nat => n + n]
    - [+]
*)

Theorem delta : forall P Q : Prop, (P -> P -> Q) -> P -> Q.
Proof.
  intros. apply H.
    assumption.
    assumption.
Qed.

Theorem apply_example : forall P Q R S : Prop,
    (Q -> R -> S) -> (P -> Q) -> P -> R -> S.
Proof.
  intros. apply H.
    apply H0. assumption.
    assumption.
Qed.

Hypotheses P Q R S : Prop.

Theorem id_PP : (P -> P) -> (P -> P).
Proof.
  intros. assumption.
Qed.

Print id_PP.

Theorem id_PP' : (P -> P) -> (P -> P).
Proof.
  intro. assumption.
Qed.

Print id_PP.
Print id_PP'.

(** DOTĄD ZROBIONE : STRONA 85 *)