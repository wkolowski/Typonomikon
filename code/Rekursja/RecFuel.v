Require Import List.
Import ListNotations.

(** TODO: w najogólniejszy sposób można to zaprezentować za pomocą (o ironio)
    koindukcji. *)

Fixpoint qs {A : Type} (le : A -> A -> bool) (fuel : nat) (l : list A)
    : option (list A) :=
match fuel, l with
    | 0, _ => None
    | _, [] => Some []
    | _, [x] => Some [x]
    | S fuel', h :: t =>
        let lesser := qs le fuel' (filter (fun x : A => le x h) t) in
        let greater := qs le fuel' (filter (fun x : A => negb (le x h)) t)
        in
          match lesser, greater with
              | Some l, Some r => Some (l ++ h :: r)
              | _, _ => None
          end
end.

Require Import Arith.

Definition leb := Compare_dec.leb.

Eval compute in qs leb 15 [5; 99; 15; 1; 1; 0; 2; 5; 6; 1; 13; 42; 55; 11].

Theorem qs_fuel :
  forall (A : Type) (le : A -> A -> bool) (l : list A),
    exists (fuel : nat) (l' : list A), qs le fuel l = Some l'.
Proof.
  intros. exists (S (length l)).
  induction l as [| h t].
    exists []. cbn. reflexivity.
    destruct IHt as [l' IH].
      case_eq (qs le (length t) (filter (fun x => le x h) t));
      case_eq (qs le (length t) (filter (fun x => negb (le x h)) t)).
        intros l Hl r Hr. exists (l ++ h :: r). cbn in *.
          destruct t.
            cbn in *. inversion Hr.
            destruct t.
Abort.