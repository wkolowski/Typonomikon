(** * G1z: Wyrażenia regularne [TODO] *)

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Require Import Recdef Bool.
Require Import List.
Import ListNotations.

Require Import Equality.

(** * Typ wrażeń regularnych (TODO) *)

Inductive Regex (A : Type) : Type :=
| Empty : Regex A
| Epsilon : Regex A
| Char : A -> Regex A
| Seq : Regex A -> Regex A -> Regex A
| Or : Regex A -> Regex A -> Regex A
| Star : Regex A -> Regex A.

Arguments Empty {A}.
Arguments Epsilon {A}.

Inductive Matches {A : Type} : list A -> Regex A -> Prop :=
| MEpsilon : Matches [] Epsilon
| MChar : forall x : A, Matches [x] (Char x)
| MSeq :
    forall (l1 l2 : list A) (r1 r2 : Regex A),
      Matches l1 r1 -> Matches l2 r2 ->
        Matches (l1 ++ l2) (Seq r1 r2)
| MOrL :
    forall (l : list A) (r1 r2 : Regex A),
      Matches l r1 -> Matches l (Or r1 r2)
| MOrR :
    forall (l : list A) (r1 r2 : Regex A),
      Matches l r2 -> Matches l (Or r1 r2)
| MStar :
    forall (l : list A) (r : Regex A),
      MatchesStar l r -> Matches l (Star r)

with MatchesStar {A : Type} : list A -> Regex A -> Prop :=
| MS_Epsilon :
    forall r : Regex A, MatchesStar [] r
| MS_Seq :
    forall (h : A) (t l : list A) (r : Regex A),
      Matches (h :: t) r -> MatchesStar l r -> MatchesStar ((h :: t) ++ l) r.

#[global] Hint Constructors Matches MatchesStar : core.

Scheme Matches_ind' := Induction for Matches Sort Prop.

(** * Dopasowanie i pochodna Brzozowskiego (TODO) *)

Fixpoint containsEpsilon
  {A : Type} (r : Regex A) : bool :=
match r with
| Empty => false
| Epsilon => true
| Char _ => false
| Seq r1 r2 => containsEpsilon r1 && containsEpsilon r2
| Or r1 r2 => containsEpsilon r1 || containsEpsilon r2
| Star _ => true
end.

Fixpoint diff
  {A : Type} (dec : A -> A -> bool) (a : A) (r : Regex A)
  : Regex A :=
match r with
| Empty   => Empty
| Epsilon => Empty
| Char x  => if dec a x then Epsilon else Empty
| Seq r1 r2 =>
    Or (Seq (diff dec a r1) r2)
       (if containsEpsilon r1
        then diff dec a r2
        else Empty)
| Or r1 r2 => Or (diff dec a r1) (diff dec a r2)
| Star r' => Seq (diff dec a r') (Star r')
end.

Fixpoint brzozowski {A : Type} (dec : A -> A -> bool) (l : list A) (r : Regex A) : Regex A :=
match l with
| [] => r
| h :: t => diff dec h (brzozowski dec t r)
end.

Definition matches {A : Type} (dec : A -> A -> bool) (l : list A) (r : Regex A) : bool :=
  containsEpsilon (brzozowski dec (rev l) r).

Fixpoint brzozowski' {A : Type} (dec : A -> A -> bool) (l : list A) (r : Regex A) : Regex A :=
match l with
| [] => r
| h :: t => brzozowski' dec t (diff dec h r)
end.

Definition matches' {A : Type} (dec : A -> A -> bool) (l : list A) (r : Regex A) : bool :=
  containsEpsilon (brzozowski' dec l r).

Lemma brzozowski_app :
  forall {A : Type} (dec : A -> A -> bool) (l1 l2 : list A) (r : Regex A),
    brzozowski dec (l1 ++ l2) r = brzozowski dec l1 (brzozowski dec l2 r).
Proof.
  induction l1 as [| h1 t1 IH]; cbn; intros l2 r; [easy |].
  now rewrite IH.
Qed.

Lemma matches'_spec :
  forall {A : Type} (dec : A -> A -> bool) (l : list A) (r : Regex A),
    matches' dec l r = matches dec l r.
Proof.
  intros A dec l r.
  unfold matches, matches'.
  f_equal.
  revert r.
  induction l as [| h t IH]; cbn; intros r; [easy |].
  now rewrite IH, brzozowski_app; cbn.
Qed.

Time Compute matches eqb
  (repeat true 10 ++ repeat false 10)
  (Seq (Star (Char true)) (Star (Char false))).

Time Compute matches eqb (repeat true 10) (Star (Char true)).

Time Compute matches eqb (repeat true 20) (Star (Char true)).

Time Compute matches eqb (repeat true 30) (Star (Char true)).