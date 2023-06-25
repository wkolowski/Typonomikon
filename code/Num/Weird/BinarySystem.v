(*
Inductive BS : Type :=
| L : BS
| R : BS
| l : BS -> BS
| r : BS -> BS.
(* | eqL : L   = l L
| eqM : l R = r L
| eqR : R   = r R *)
*)

(** Interpretacja:
    - typ [D] to (0; 1)
    - [middle] to 1/2
    - [left x] to punkt między x a ostatnim punktem na lewo (lub zerem)
    - [right x] to punkt między x a ostatnim punkte na prawo (lub jedynką)
*)
Inductive D : Type :=
| middle : D
| left   : D -> D
| right  : D -> D.

(** [BS'] to [0; 1] *)
Inductive BS' : Type :=
| L' : BS'
| R' : BS'
| η  : D -> BS'.

(** Widać na oko, że [D] jest izomorficzne z [list bool]. *)

Require Import List.
Import ListNotations.

Fixpoint D_to_list (d : D) : list bool :=
match d with
| middle => []
| left d' => false :: D_to_list d'
| right d' => true :: D_to_list d'
end.

Fixpoint list_to_D (l : list bool) : D :=
match l with
| [] => middle
| false :: l' => left (list_to_D l')
| true :: l' => right (list_to_D l')
end.

Lemma there :
  forall (d : D),
    list_to_D (D_to_list d) = d.
Proof.
  now induction d; cbn; congruence.
Qed.

Lemma back_again :
  forall (l : list bool),
    D_to_list (list_to_D l) = l.
Proof.
  now induction l as [| [] l']; cbn; congruence.
Qed.

(** A jakby zrobić koinduktywne? *)

CoInductive CoD : Type :=
| comiddle
| coleft : CoD -> CoD
| coright : CoD -> CoD.

(** Tabelka:
    - 1/2 = middle
    - 0 = coleft 0
    - 1 = coright 1
    - coright 0 = epsilon?
    - coleft 1 = 1 - epsilon?
    - wut = coleft (coright wut) - co to kurła jest?
*)