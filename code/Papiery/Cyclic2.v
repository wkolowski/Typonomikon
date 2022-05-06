Require Import Recdef Nat String Coq.Program.Equality.
Require Import F4 D5.

Inductive Cyclic (A : Type) : Type :=
  | C : forall (start : list A) (cycle : list A), Cyclic A.

Arguments C {A} _ _.

(** * CoLists *)

(** The first part is inspired by
    #<a class='link' href='https://gallais.github.io/blog/cyclic-list-purely.html'>
    Cyclic Lists, Purely</a>#. *)

Definition cmap {A B : Type} (f : A -> B) (l : Cyclic A) : Cyclic B :=
match l with
  | C start cycle => C (map f start) (map f cycle)
end.

Lemma cmap_cmap :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (l : Cyclic A),
    cmap g (cmap f l) = cmap (fun x => g (f x)) l.
Proof.
  destruct l; cbn.
  f_equal; apply map_map.
Qed.

Lemma cmap_id :
  forall {A : Type} (l : Cyclic A), 
    cmap (fun x => x) l = l.
Proof.
  destruct l; cbn.
  f_equal; apply map_id.
Qed.

Definition capp {A : Type} (l1 l2 : Cyclic A) : Cyclic A :=
match l1, l2 with
    | C s1 [], C s2 c2 => C (s1 ++ s2) c2
    | C s1 c1, C s2 c2 => l1
end.

Lemma map_app :
  forall {A B : Type} (f : A -> B) (l1 l2 : Cyclic A),
    cmap f (capp l1 l2) = capp (cmap f l1) (cmap f l2).
Proof.
  destruct l1 as [s1 []], l2 as [s2 c2]; cbn.
    f_equal. apply map_app.
    reflexivity.
Qed.

Lemma capp_assoc :
  forall {A : Type} (l1 l2 l3 : Cyclic A),
    capp (capp l1 l2) l3 = capp l1 (capp l2 l3).
Proof.
  destruct l1 as [s1 []], l2 as [s2 []], l3 as [s3 c3]; cbn.
    2-4: reflexivity.
    f_equal. rewrite app_assoc. reflexivity.
Qed.

Definition csnoc {A : Type} (x : A) (l : Cyclic A) : Cyclic A :=
match l with
    | C s [] => C (snoc x s) []
    | C s c => C s c
end.

Lemma csnoc_capp :
  forall {A : Type} (x : A) (l1 l2 : Cyclic A),
    csnoc x (capp l1 l2) = capp l1 (csnoc x l2).
Proof.
  destruct l1 as [s1 []], l2 as [s2 []]; cbn.
    2-4: try reflexivity.
    f_equal. apply snoc_app.
Qed.

Definition creplicate {A : Type} (n : nat) (x : A) : Cyclic A :=
  C (replicate n x) [].

Definition crepeat {A : Type} (x : A) : Cyclic A :=
  C [] [x].

Inductive Finite {A : Type} : Cyclic A -> Type :=
    | Finite' : forall l : list A, Finite (C l []).

Lemma Finite_creplicate :
  forall (n : nat) {A : Type} (x : A),
    Finite (creplicate n x).
Proof.
  constructor.
Qed.

Lemma not_Finite_crepeat :
  forall {A : Type} (x : A),
    Finite (crepeat x) -> False.
Proof.
  inversion 1.
Qed.

Definition ccons {A : Type} (h : A) (t : Cyclic A) : Cyclic A :=
match t with
    | C s c => C (h :: s) c
end.

Definition cuncons {A : Type} (l : Cyclic A) : option (A * Cyclic A) :=
match l with
    | C [] []       => None
    | C [] (h :: t) => Some (h, C [] (snoc h t))
    | C (h :: t) c  => Some (h, C t c)
end.

Definition example : Cyclic nat :=
  C [] [1; 2; 3; 4; 5].

Fixpoint ctake (n : nat) {A : Type} (l : Cyclic A) : list A :=
match n, l with
    | 0   , _             => []
    | S n', C [] []       => []
    | S n', C (h :: t) c  => h :: ctake n' (C t c)
    | S n', C [] (h :: t) => h :: ctake n' (C [] (snoc h t))
end.

Compute ctake 10 example.

Fixpoint cdrop (n : nat) {A : Type} (l : Cyclic A) : Cyclic A :=
match n, l with
    | 0   , _             => l
    | S n', C [] []       => C [] []
    | S n', C (h :: t) c  => cdrop n' (C t c)
    | S n', C [] (h :: t) => cdrop n' (C [] (snoc h t))
end.

Compute cdrop 23 example.

Fixpoint cbind_aux {A B : Type} (l : list A) (f : A -> Cyclic B) : Cyclic B :=
match l with
    | []     => C [] []
    | h :: t => capp (f h) (cbind_aux t f)
end.

Definition cbind {A B : Type} (l : Cyclic A) (f : A -> Cyclic B) : Cyclic B :=
match l with
    | C s c => capp (cbind_aux s f) (cbind_aux c f)
end.

Definition crev {A : Type} (l : Cyclic A) : Cyclic A :=
match l with
    | C s [] => C (rev s) []
    | C _ c => C [] (rev c)
end.

Compute ctake 10 (crev (C [1; 2] [3; 4; 5])).
Compute crev example.

Fixpoint nth (n : nat) {A : Type} (l : Cyclic A) : option A :=
match n, l with
    | _   , C [] []       => None
    | 0   , C (h :: _) _  => Some h
    | 0   , C [] (h :: _) => Some h
    | S n', C (_ :: t) c  => nth n' (C t c)
    | S n', C [] (h :: t) => nth n' (C [] (snoc h t))
end.

Compute map (fun n => nth n example) [0; 1; 2; 3; 4; 5; 6; 7].

Definition cany {A : Type} (p : A -> bool) (l : Cyclic A) : bool :=
match l with
    | C s c => any p s || any p c
end.

Definition cfilter {A : Type} (p : A -> bool) (l : Cyclic A) : Cyclic A :=
match l with
    | C s c => C (filter p s) (filter p c)
end.

Compute example.
Compute cfilter Nat.even example.
Compute ctake 10 (cfilter Nat.even example).

Definition cintersperse {A : Type} (x : A) (l : Cyclic A) : Cyclic A :=
match l with
    | C s [] => C (intersperse x s) []
    | C s c  => C (intersperse x s) (x :: intersperse x c)
end.

Compute example.
Compute cintersperse 0 example.
Compute ctake 20 (cintersperse 0 example).

Definition ctakeWhile {A : Type} (p : A -> bool) (l : Cyclic A) : Cyclic A :=
match l with
    | C s c =>
        if length s =? length (takeWhile p s)
        then C (takeWhile p s) (takeWhile p c)
        else C (takeWhile p s) []
end.

Compute ctakeWhile (fun n => n <? 3) example.

Definition cdropWhile {A : Type} (p : A -> bool) (l : Cyclic A) : Cyclic A :=
match l with
    | C s c =>
        match dropWhile p s with
            | [] => C [] (dropWhile p c)
            | s' => C s' c
        end
end.

Compute cdropWhile (fun n => n <? 3) example.

Module CyclicBinaryTree.

(** Sadly, this wonderful technique doesn't work with binary trees. This is
    because cyclic lists have only one cycle, which is easy to represent with
    a single ordinary [list], but trees can have as many cycles as they have
    leaves. *)

End CyclicBinaryTree.