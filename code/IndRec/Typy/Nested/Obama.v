Unset Positivity Checking.
CoInductive Obama (A : Type) : Type :=
{
    hd : A;
    tl : Obama (Obama A);
}.
Set Positivity Checking.

Arguments hd {A} _.
Arguments tl {A} _.

CoInductive sim {A : Type} (b1 b2 : Obama A) : Type :=
{
    hds : hd b1 = hd b2;
    tls : sim (tl b1) (tl b2);
}.

Lemma sim_refl :
  forall (A : Type) (s : Obama A), sim s s.
(* begin hide *)
Proof.
  cofix CH. constructor; auto.
Qed.
(* end hide *)

Lemma sim_sym :
  forall (A : Type) (s1 s2 : Obama A),
    sim s1 s2 -> sim s2 s1.
(* begin hide *)
Proof.
  cofix CH.
  destruct 1 as [hds tls]. constructor; auto.
Qed.
(* end hide *)

Lemma sim_trans :
  forall (A : Type) (s1 s2 s3 : Obama A),
    sim s1 s2 -> sim s2 s3 -> sim s1 s3.
(* begin hide *)
Proof.
  cofix CH.
  destruct 1 as [hds1 tls1], 1 as [hds2 tls2].
  constructor; eauto. rewrite hds1. assumption.
Qed.
(* end hide *)

Lemma eq_sim :
  forall {A : Type} (b1 b2 : Obama A), b1 = b2 -> sim b1 b2.
Proof.
  intros A b1 b2 [].
  apply sim_refl.
Qed.

Axiom sim_eq :
  forall {A : Type} (b1 b2 : Obama A), sim b1 b2 -> b1 = b2.

(** * [map] *)

(** Zdefiniuj funkcję [map], która aplikuje funkcję [f : A -> B] do
    każdego elementu strumienia. *)

(* begin hide *)
Unset Guard Checking.
CoFixpoint map {A B : Type} (f : A -> B) (b : Obama A) : Obama B :=
{|
    hd := f (hd b);
    tl := map (map f) (tl b);
|}.
Set Guard Checking.
(* end hide *)

Lemma map_id :
  forall (A : Type) (s : Obama A), sim (map (@id A) s) s.
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    apply eq_sim. specialize (CH _ (tl s)). apply sim_eq in CH.
      replace _ with (map (map (@id A)) (tl s) = map (@id (Obama A)) (tl s)).
        f_equal.
Abort.
(* end hide *)

Lemma map_map :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (s : Obama A),
    sim (map g (map f s)) (map (fun x => g (f x)) s).
(* begin hide *)
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    cofix CH'. constructor; cbn.
      apply sim_eq. apply CH.
      apply CH'.
Abort.
(* end hide *)

Unset Guard Checking.
CoFixpoint zipWith
  {A B C : Type} (f : A -> B -> C)
  (s1 : Obama A) (s2 : Obama B) : Obama C :=
{|
    hd := f (hd s1) (hd s2);
    tl := zipWith (zipWith f) (tl s1) (tl s2);
|}.
Set Guard Checking.

Definition unzip
  {A B : Type} (s : Obama (A * B)) : Obama A * Obama B :=
    (map fst s, map snd s).

Lemma unzip_zipWith :
  forall {A B : Type} (s : Obama (A * B)),
    sim
      (zipWith pair (fst (unzip s)) (snd (unzip s)))
      s.
Proof.
  cofix CH.
  constructor; cbn.
    destruct s as [[ha hb] s']; cbn. reflexivity.
    apply CH.
Abort.

(* TODO *) Lemma zipWith_unzip :
  forall {A B : Type} (sa : Obama A) (sb : Obama B),
    let s' := unzip (zipWith pair sa sb) in
      sim (fst s') sa * sim (snd s') sb.
Proof.
  split; cbn.
    revert sa sb. cofix CH. intros. constructor; cbn.
      reflexivity.
      apply CH.
    revert sa sb. cofix CH. intros. constructor; cbn.
      reflexivity.
      apply CH.
Abort.

Unset Guard Checking.
CoFixpoint repeat {A : Type} (x : A) : Obama A :=
{|
    hd := x;
    tl := repeat (repeat x);
|}.

(* CoFixpoint iterate {A : Type} (f : A -> A) (x : A) : Obama A :=
{|
    hd := x;
    tl := iterate f (f x);
|}. *)

Require Import Bush.

Fixpoint nth' {A B : Type} (n : Bush A) (b : Obama B) : B :=
match n with
    | Leaf => hd b
    | Node _ b' => hd (nth' b' (tl b))
end.

Definition nth (n : Bush unit) {A : Type} (b : Obama A) : A :=
  nth' n b.

(* Fixpoint take (n : nat) {A : Type} (s : Obama A) : list A :=
match n with
    | 0 => nil
    | S n' => cons (hd s) (take n' (tl s))
end.

Fixpoint drop (n : nat) {A : Type} (s : Obama A) : Obama A :=
match n with
    | 0 => s
    | S n' => drop n' (tl s)
end.

Fixpoint splitAt
  (n : nat) {A : Type} (s : Obama A) : list A * A * Obama A :=
match n with
    | 0 => (nil, hd s, tl s)
    | S n' =>
        let '(l, x, s') := splitAt n' (tl s) in (cons (hd s) l, x, s')
end.

CoFixpoint from (n : nat) : Obama nat :=
{|
    hd := n;
    tl := from (S n);
|}.

Fixpoint insert (n : nat) {A : Type} (x : A) (s : Obama A) : Obama A :=
match n with
    | 0 => {| hd := x; tl := s; |}
    | S n' => {| hd := hd s; tl := insert n' x (tl s); |}
end.

Fixpoint replace (n : nat) {A : Type} (x : A) (s : Obama A) : Obama A :=
match n with
    | 0 => {| hd := x; tl := tl s; |}
    | S n' => {| hd := hd s; tl := replace n' x (tl s); |}
end.

CoFixpoint diagonal {A : Type} (s : Obama (Obama A)) : Obama A :=
{|
    hd := hd (hd s);
    tl := diagonal (tl (map tl s));
|}.

CoFixpoint scanl
  {A B : Type} (f : A -> B -> A) (x : A) (s : Obama B) : Obama A :=
{|
    hd := f x (hd s);
    tl := scanl f (f x (hd s)) (tl s);
|}.

CoFixpoint scanr
  {A B : Type} (f : A -> B -> B) (x : B) (s : Obama A) : Obama B :=
{|
    hd := f (hd s) x;
    tl := scanr f (f (hd s) x) (tl s);
|}.

CoFixpoint intersperse {A : Type} (x : A) (s : Obama A) : Obama A :=
{|
    hd := hd s;
    tl :=
    {|
        hd := x;
        tl := intersperse x (tl s);
    |};
|}.
*)

(* CoFixpoint merge {A : Type} (s1 s2 : Obama A) : Obama A :=
{|
    hd := hd s1;
    tl :=
    {|
        hd := hd s2;
        tl := merge (tl s1) (tl s2);
    |};
|}.
 *)

Unset Positivity Checking.
Inductive Exists {A : Type} (P : A -> Type) (b : Obama A) : Type :=
    | Ex_hd : P (hd b) -> Exists P b
    | Ex_tl : Exists (Exists P) (tl b) -> Exists P b.
Set Positivity Checking.

Global Hint Constructors Exists : core.

Definition Elem {A : Type} (x : A) (b : Obama A) : Type :=
  Exists (fun y => x = y) b.

Unset Positivity Checking.
CoInductive Forall {A : Type} (P : A -> Type) (b : Obama A) : Type :=
{
    Forall_hd : P (hd b);
    Forall_tl : Forall (Forall P) (tl b);
}.
Set Positivity Checking.

Unset Positivity Checking.
CoInductive Forall2 {A B : Type} (P : A -> B -> Type) (b1 : Obama A) (b2 : Obama B) : Type :=
{
    Forall2_hd : P (hd b1) (hd b2);
    Forall2_tl : Forall2 (Forall2 P) (tl b1) (tl b2);
}.
Set Positivity Checking.

Definition sim' {A : Type} (b1 b2 : Obama A) : Type :=
  Forall2 eq b1 b2.

Unset Positivity Checking.
Inductive Dup {A : Type} (b : Obama A) : Prop :=
    | Dup_hd : Exists (Exists (fun y => y = hd b)) (tl b) -> Dup b
    | Dup_tl : Exists Dup (tl b) -> Dup b.
Set Positivity Checking.







(* begin hide *)
CoInductive Substream {A : Type} (s1 s2 : Obama A) : Prop :=
{
    n : nat;
    p : hd s1 = nth n s2;
    Substream' : Substream (tl s1) (drop (S n) s2);
}.
(* end hide *)










(* begin hide *)
Inductive Suffix {A : Type} : Obama A -> Obama A -> Prop :=
    | Suffix_refl :
        forall s : Obama A, Suffix s s
    | Suffix_tl :
        forall s1 s2 : Obama A,
          Suffix (tl s1) s2 -> Suffix s1 s2.
(* end hide *)

Fixpoint snoc {A : Type} (x : A) (l : list A) : list A :=
match l with
    | nil => cons x nil
    | cons h t => cons h (snoc x t)
end.



(* begin hide *)
Definition Incl {A : Type} (b1 b2 : Obama A) : Type :=
  forall x : A, Elem x b1 -> Elem x b2.

Definition SetEquiv {A : Type} (s1 s2 : Obama A) : Type :=
  Incl s1 s2 * Incl s2 s1.
(* end hide *)



(* Inductive SPermutation {A : Type} : Obama A -> Obama A -> Prop :=
    | SPerm_refl :
        forall s : Obama A, SPermutation s s
    | SPerm_skip :
        forall (x : A) (s1 s2 : Obama A),
          SPermutation s1 s2 -> SPermutation (scons x s1) (scons x s2)
    | SPerm_swap :
        forall (x y : A) (s1 s2 : Obama A),
          SPermutation s1 s2 ->
            SPermutation (scons x (scons y s1)) (scons y (scons x s2))
    | SPerm_trans :
        forall s1 s2 s3 : Obama A,
          SPermutation s1 s2 -> SPermutation s2 s3 -> SPermutation s1 s3.

Global Hint Constructors SPermutation : core.
 *)










Lemma Obama_coiter :
  forall
    (A : Type)
    (hd : forall D : Type, D -> A)
    (tl : forall (D : Type) (F : Type -> Type), F D -> F (F D)),
      forall D : Type, D -> Obama A.
Proof.
  cofix CH.
  intros A hd tl D d.
  constructor.
    exact (hd _ d).
    apply tl. apply (CH A hd tl D d).
Defined.


(* Definition Obama' (A : Type) : Type :=
  {X : Type & X * (X -> A) * (X -> X)}%type.
 *)

(* Lemma Obama'_Obama {A : Type} (s : Obama' A) : Obama A.
Proof.
Defined.

Definition Obama_Obama' {A : Type} (s : Obama A) : Obama' A.
Proof.
Defined.
 *)

(* Lemma Obamas :
  forall (A : Type) (s : Obama A),
    sim (Obama'_Obama (Obama_Obama' s)) s.
Proof.
Abort.

Lemma Obamas' :
  forall (A : Type) (s : Obama' A),
    Obama_Obama' (Obama'_Obama s) = s.
Proof.
Abort.
 *)