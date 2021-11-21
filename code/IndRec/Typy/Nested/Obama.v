Require Import Bush.

Set Universe Polymorphism.

Unset Positivity Checking.
CoInductive Obama (A : Type) : Type :=
{
    hd : A;
    tl : Obama (Obama A);
}.

Arguments hd {A} _.
Arguments tl {A} _.

CoInductive sim' {A : Type} (b1 b2 : Obama A) : Type :=
{
    hds : hd b1 = hd b2;
    tls : sim' (tl b1) (tl b2);
}.

CoInductive Forall {A : Type} (P : A -> Type) (b : Obama A) : Type :=
{
    Forall_hd : P (hd b);
    Forall_tl : Forall (Forall P) (tl b);
}.

CoInductive Forall2 {A B : Type} (P : A -> B -> Type) (b1 : Obama A) (b2 : Obama B) : Type :=
{
    Forall2_hd : P (hd b1) (hd b2);
    Forall2_tl : Forall2 (Forall2 P) (tl b1) (tl b2);
}.

Definition sim {A : Type} (b1 b2 : Obama A) : Type :=
  Forall2 eq b1 b2.

Inductive Exists {A : Type} (P : A -> Type) (b : Obama A) : Type :=
    | Ex_hd : P (hd b) -> Exists P b
    | Ex_tl : Exists (Exists P) (tl b) -> Exists P b.

Inductive Exists2 {A B : Type} (R : A -> B -> Type) (b1 : Obama A) (b2 : Obama B) : Type :=
    | Ex2_hd : R (hd b1) (hd b2) -> Exists2 R b1 b2
    | Ex2_tl : Exists2 (Exists2 R) (tl b1) (tl b2) -> Exists2 R b1 b2.

Global Hint Constructors Exists Exists2 : core.

Definition Elem {A : Type} (x : A) (b : Obama A) : Type :=
  Exists (fun y => x = y) b.

Definition ObamaNeq {A : Type} (b1 b2 : Obama A) : Type :=
  Exists2 (fun x y => x <> y) b1 b2.

Inductive Dup {A : Type} (b : Obama A) : Prop :=
    | Dup_hd : Exists (Exists (fun y => y = hd b)) (tl b) -> Dup b
    | Dup_tl : Exists Dup (tl b) -> Dup b.
Set Positivity Checking.

(* TODO: to raczej nie powinno być induktywne... *)

Inductive SubObama : forall {A B : Type}, Obama A -> Obama B -> Type :=
    | SubObama_hds :
        forall {A : Type} (b1 b2 : Obama A),
          hd b1 = hd b2 -> SubObama (tl b1) (tl b2) -> SubObama b1 b2
    | SubObama_hd :
        forall {A : Type} (b1 : Obama A) (b2 : Obama (Obama A)),
          SubObama b1 (hd b2) -> SubObama b1 b2
    | SubObama_tl :
        forall {A : Type} (b1 b2 : Obama A),
          SubObama b1 (tl b2) -> SubObama b1 b2.

Inductive DirectSubterm : forall {A B : Type}, A -> B -> Type :=
    | DS_hd :
        forall {A : Type} (b : Obama A),
          DirectSubterm (hd b) b
    | DS_tl :
        forall {A : Type} (b : Obama A),
          DirectSubterm (tl b) b.

Inductive Subterm : forall {A B : Type}, Obama A -> Obama B -> Type :=
    | Subterm_step :
        forall {A B : Type} (b1 : Obama A) (b2 : Obama B),
          DirectSubterm b1 b2 -> Subterm b1 b2
    | Subterm_trans :
        forall {A B C : Type} (b1 : Obama A) (b2 : Obama B) (b3 : Obama C),
          DirectSubterm b1 b2 -> Subterm b2 b3 -> Subterm b1 b3.

Inductive Swap : forall {A B : Type}, B -> Obama A -> B -> Obama A -> Type :=
    | Swap_hdtl :
        forall {A : Type} (x : A) (b : Obama A),
          Swap x b (hd b) {| hd := x; tl := tl b; |}
    | Swap_hd :
        forall {A : Type} (x y : A) (b : Obama (Obama A)) (r : Obama A),
          Swap x (hd b) y r -> Swap x b y {| hd := r; tl := tl b; |}
    | Swap_tl :
        forall {A : Type} (x y : A) (b : Obama A) (r : Obama (Obama A)),
          Swap x (tl b) y r -> Swap x b y {| hd := hd b; tl := r; |}.

Fail Inductive Permutation : forall {A : Type}, Obama A -> Obama A -> Type :=
    | Permutation_refl :
        forall {A : Type} (b : Obama A), Permutation b b
    | Permutation_step :
        forall {A : Type} (x y : A) (b1 b2 b2' b3 : Obama A),
          Swap (hd b1) b1 y b1' -> Permutation {| hd := y; tl := tl b1'; |} b2 -> Permutation b1 b3.
Set Positivity Checking.

Axiom sim_eq :
  forall {A : Type} (b1 b2 : Obama A), sim b1 b2 -> b1 = b2.

Unset Guard Checking.

Definition Obama_corec :
  forall
    {A : Type} {F : Type -> Type}
    (hd' : forall A : Type, F A -> A) (tl' : forall A : Type, F A -> F (F A)),
      F A -> Obama A.
Proof.
  cofix CH.
  intros A F hd' tl' x.
  constructor.
    exact (hd' _ x).
    specialize (CH A F hd' tl' x). apply CH.
Admitted.

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

CoFixpoint map {A B : Type} (f : A -> B) (b : Obama A) : Obama B :=
{|
    hd := f (hd b);
    tl := map (map f) (tl b);
|}.

CoFixpoint zipWith
  {A B C : Type} (f : A -> B -> C)
  (s1 : Obama A) (s2 : Obama B) : Obama C :=
{|
    hd := f (hd s1) (hd s2);
    tl := zipWith (zipWith f) (tl s1) (tl s2);
|}.

Definition unzip
  {A B : Type} (s : Obama (A * B)) : Obama A * Obama B :=
    (map fst s, map snd s).

CoFixpoint repeat {A : Type} (x : A) : Obama A :=
{|
    hd := x;
    tl := repeat (repeat x);
|}.

CoFixpoint iterate {A : Type} (f : A -> A) (x : A) : Obama A :=
{|
    hd := x;
    tl := iterate (map f) (iterate f x);
|}.

Fixpoint nth' {A B : Type} (n : Bush A) (b : Obama B) : B :=
match n with
    | Leaf => hd b
    | Node _ b' => hd (nth' b' (tl b))
end.

Definition nth (n : Bush unit) {A : Type} (b : Obama A) : A :=
  nth' n b.

Fixpoint Obama_to_the (n : nat) (A : Type) : Type :=
match n with
    | 0 => A
    | S n' => Obama_to_the n' (Obama A)
end.

Fixpoint nth2 {A : Type} (n : nat) (b : Obama A) {struct n} : Obama_to_the n A :=
match n with
    | 0 => hd b
    | S n' => nth2 n' (tl b)
end.

CoFixpoint from (n : nat) : Obama nat :=
{|
    hd := n;
    tl := map from (from (S n));
|}.

CoFixpoint diagonal {A : Type} (s : Obama (Obama A)) : Obama A :=
{|
    hd := hd (hd s);
    tl := diagonal (tl s);
|}.






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

Lemma Forall2_refl :
  forall
    {A : Type} {R : A -> A -> Type}
    (Rrefl : forall x : A, R x x)
    (x : Obama A),
      Forall2 R x x.
Proof.
  cofix CH.
  constructor.
    apply Rrefl.
    apply CH. apply CH. assumption.
Admitted.

Lemma sim_refl :
  forall (A : Type) (s : Obama A), sim s s.
Proof.
  intros. apply Forall2_refl. reflexivity.
Qed.

Lemma Forall2_sym :
  forall
    {A : Type} (R : A -> A -> Type)
    (Rsym : forall x y : A, R x y -> R y x)
    (b1 b2 : Obama A),
      Forall2 R b1 b2 -> Forall2 R b2 b1.
Proof.
  cofix CH.
  destruct 2 as [hds tls].
  constructor.
    apply Rsym. assumption.
    apply CH.
      apply CH. assumption.
      assumption.
Admitted.

Lemma sim_sym :
  forall (A : Type) (s1 s2 : Obama A),
    sim s1 s2 -> sim s2 s1.
Proof.
  intros. apply Forall2_sym.
    apply eq_sym.
    exact H.
Qed.

Lemma Forall2_trans :
  forall
    {A : Type} {R : A -> A -> Type}
    (Rtrans : forall x y z : A, R x y -> R y z -> R x z)
    (x y z : Obama A),
      Forall2 R x y -> Forall2 R y z -> Forall2 R x z.
Proof.
  cofix CH.
  destruct 2 as [x_hds x_tls], 1 as [y_hds y_tls].
  constructor.
    eapply Rtrans; eassumption.
    eapply CH.
      apply CH. assumption.
      eassumption.
      eassumption.
Admitted.

Lemma sim_trans :
  forall (A : Type) (s1 s2 s3 : Obama A),
    sim s1 s2 -> sim s2 s3 -> sim s1 s3.
Proof.
  intros.
  eapply Forall2_trans.
    apply eq_trans.
    eassumption.
    eassumption.
Qed.

Lemma eq_sim :
  forall {A : Type} (b1 b2 : Obama A), b1 = b2 -> sim b1 b2.
Proof.
  intros A b1 b2 [].
  apply sim_refl.
Qed.

Lemma map_id :
  forall (A : Type) (s : Obama A), sim (map (@id A) s) s.
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
Abort.

Lemma Forall2_map_map :
  forall
    {A B C : Type} (R : C -> C -> Type)
    (f : A -> B) (g : B -> C)
    (s : Obama A),
      Forall2 R (map g (map f s)) (map (fun x => g (f x)) s).
Proof.
  cofix CH.
  constructor.
    cbn. admit.
    apply CH.
Admitted.

Lemma map_map :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (s : Obama A),
    sim (map g (map f s)) (map (fun x => g (f x)) s).
Proof.
  intros. apply Forall2_map_map.
Qed.

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