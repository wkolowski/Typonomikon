(** * G6: Prawdziwie zagnieżdżone typy induktywne [TODO] *)

From Typonomikon Require Import D5.

Set Universe Polymorphism.

(** * Jerzy Krzak wrednym typem był (TODO) *)

(** Wzięte
    #<a class='link' href='https://personal.cis.strath.ac.uk/neil.ghani/papers/ghani-hosc09.pdf'>
    stąd</a>#. *)

Unset Positivity Checking.
Inductive Bush (A : Type) : Type :=
| Leaf : Bush A
| Node : A -> Bush (Bush A) -> Bush A.
Set Positivity Checking.

Arguments Leaf {A}.
Arguments Node {A} _ _.

Fixpoint map {A B : Type} (f : A -> B) (b : Bush A) {struct b} : Bush B :=
match b with
| Leaf      => Leaf
| Node v bs => Node (f v) (map (map f) bs)
end.

Unset Guard Checking.
Fixpoint sum (b : Bush nat) : nat :=
match b with
| Leaf => 0
| Node n bs => n + sum (map sum bs)
end.
Set Guard Checking.

Unset Guard Checking.
Fixpoint size {A : Type} (b : Bush A) {struct b} : nat :=
match b with
| Leaf => 0
| Node v bs => 1 + sum (map size bs)
end.
Set Guard Checking.

Unset Guard Checking.
Fixpoint toList {A : Type} (b : Bush A) {struct b} : list A :=
match b with
| Leaf      => []
| Node v bs => v :: join (toList (map toList bs))
end.
Set Guard Checking.

Fixpoint replicate (h : nat) {A : Type} (x : A) : Bush A :=
match h with
| 0    => Leaf
| S h' => Node x (replicate h' (replicate h' x))
end.

Fixpoint count {A : Type} (p : A -> nat) (b : Bush A) {struct b} : nat :=
match b with
| Leaf => 0
| Node x b' => p x + count (count p) b'
end.

(*
Fixpoint app {A : Type} (b1 b2 : Bush A) : Bush A :=
match b1 with
| Leaf     => b2
| Node h t => Node h (
*)

(*
Fixpoint join {A : Type} (b : Bush (Bush A)) {struct b} : Bush A.
*)

Compute (replicate 3 (Node 5 Leaf)).

Unset Guard Checking.
Fixpoint nums (n : nat) : Bush nat :=
match n with
| 0 => Node 0 Leaf
| S n' => Node n (map nums (nums n'))
end.
Set Guard Checking.

Compute size (nums 4).

(* Compute count (fun n => if even n then 1 else 0) (nums 10). *)

Require Import FunctionalExtensionality.

Unset Positivity Checking.
Inductive Bush' {A : Type} (P : A -> Type) : Bush A -> Type :=
| Leaf' : Bush' P Leaf
| Node' :
    forall (x : A) (b : Bush (Bush A)),
      P x -> Bush' (Bush' P) b -> Bush' P (Node x b).
Set Positivity Checking.

Fixpoint Bush_ind_deep
  (P : forall (A : Type) (Q : A -> Type), Bush A -> Type)
  (leaf : forall (A : Type) (Q : A -> Type), P A Q Leaf)
  (node : forall (A : Type) (Q : A -> Type) (x : A) (b : Bush (Bush A)),
            Q x -> P (Bush A) (Bush' Q) b -> P A Q (Node x b))
  {A : Type} (Q : A -> Type)
  {b : Bush A} (b' : Bush' Q b) {struct b'} : P A Q b.
Proof.
  destruct b' as [| x b Qx Pb].
  - apply leaf.
  - apply node.
    + exact Qx.
    + apply Bush_ind_deep; try assumption.
Defined.

Fixpoint Bush'_True {A : Type} {Q : A -> Type} (b : Bush A) {struct b} :
  (forall x : A, Q x) -> Bush' Q b.
Proof.
  destruct b as [| x b']; intros H.
  - now constructor.
  - constructor; [easy |].
    apply Bush'_True.
    intros b''.
    now apply Bush'_True.
Defined.

Fixpoint Bush_ind
  (P : forall (A : Type), Bush A -> Type)
  (leaf : forall (A : Type), P A Leaf)
  (node : forall (A : Type) (x : A) (b : Bush (Bush A)),
            P (Bush A) b -> P A (Node x b))
  {A : Type}
  {b : Bush A} {struct b} : P A b.
Proof.
  refine (@Bush_ind_deep (fun A _ => P A) _ _ A (fun _ => True) b _); intros.
  - apply leaf.
  - apply node; assumption.
  - now apply Bush'_True.
Defined.

(*
Fixpoint Bush_ind_deep'
  (P : forall (A : Type) (Q : A -> Type), Bush A -> Type)
  (leaf : forall (A : Type) (Q : A -> Type), P A Q Leaf)
  (node : forall (A : Type) (Q : A -> Type) (x : A) (b : Bush (Bush A)),
            Q x -> P (Bush A) (P A Q) b -> P A Q (Node x b))
  {A : Type} (Q : A -> Type)
  {b : Bush A} (b' : Bush' Q b) {struct b'} : P A Q b.
Proof.
  destruct b' as [| x b Qx Pb].
    apply leaf.
    apply node.
      exact Qx.
      apply Bush_ind_deep'; try assumption. revert P Q leaf node Qx b Pb. fix IH 6.
        destruct 4; constructor.
          apply Bush_ind_deep'; assumption. Check Bush'.
          specialize (IH (fun A Q => Bush' (P A Q))). assumption.
Defined.
*)

Fixpoint Bush_ind_deep''
  {A : Type} (Q : A -> Type) (P : Bush A -> Type)
  (leaf : P Leaf)
  (node : forall (x : A) (b : Bush (Bush A)),
            Q x -> Bush' P b -> P (Node x b))
  {b : Bush A} (b' : Bush' Q b) {struct b'} : P b.
Proof.
  destruct b' as [| x b Qx Pb].
    apply leaf.
    apply node.
      exact Qx.
      revert P Q leaf node Qx b Pb. fix IH 6; intros.
        destruct Pb; constructor.
          apply (Bush_ind_deep'' A Q P); assumption.
Abort.










Lemma map_map :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (b : Bush A),
    map g (map f b) = map (fun x => g (f x)) b.
Proof.
  intro.
  pose (P := (fun (A : Type) (b : Bush A) => forall (B C : Type) (f : A -> B) (g : B -> C)
    (b : Bush A), map g (map f b) = map (fun x => g (f x)) b)).
  refine (Bush_ind P _ _).
  - unfold P; cbn; intros.
Abort.

Unset Guard Checking.
Lemma map_map :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (b : Bush A),
    map g (map f b) = map (fun x => g (f x)) b.
Proof.
  fix IH 6.
  destruct b as [| h t]; cbn.
  - reflexivity.
  - rewrite IH.
    do 2 f_equal.
    extensionality bb.
    now rewrite IH.
Qed.
Set Guard Checking.

(** * Krzak przykościelny *)

Definition BushC (A : Type) : Type :=
  forall
    (F : Type -> Type)
    (leaf : forall R : Type, F R)
    (node : forall R : Type, R -> F (F R) -> F R)
    (* (R : Type) *), F A.

Definition leaf {A : Type} : BushC A :=
  fun F leaf node (* R *) => leaf A.

Definition node {A : Type} (x : A) (b : BushC (BushC A)) : BushC A.
Proof.
  intros F leaf node (* R *).
  unfold BushC in b.

  (* fun F leaf node R =>
    node R x (b F leaf (fun R' x' t' => x' F leaf node R') (F R)).
 *)
Abort.

(* Definition mapC {A B : Type} (f : A -> B) (b : BushC A) : BushC B :=
  fun F leaf node R =>
    b F leaf (fun R a t => node R (f a) t) R.
 *)

(* Fixpoint B2BC {A : Type} (b : Bush A) {struct b} : BushC A :=
match b with
| Leaf => leaf
| Node x b' => node x (B2BC (map B2BC b'))
end.

Definition BC2B {A : Type} (b : BushC A) : Bush A.
Proof.
  unfold BushC in b.
  specialize (b Bush (@Leaf) (@Node)).
*)

(** * Twój stary to krzak (TODO) *)

Module BushSenior.

Unset Positivity Checking.
Inductive BushSenior (A : Type) : Type :=
| E : BushSenior A
| N : A -> BushSenior (BushSenior (BushSenior A)) -> BushSenior A.
Set Positivity Checking.

Arguments E {A}.
Arguments N {A} _ _.

Unset Guard Checking.
Fixpoint map {A B : Type} (f : A -> B) (b : BushSenior A) {struct b} : BushSenior B :=
match b with
| E => E
| N x b' => N (f x) (map (map (map f)) b')
end.

Fixpoint sum (b : BushSenior nat) : nat :=
match b with
| E => 0
| N x b' => x + sum (map sum (map (map sum) b'))
end.

Fixpoint size {A : Type} (b : BushSenior A) {struct b} : nat :=
match b with
| E => 0
| N _ b' => 1 + sum (map sum (map (map size) b'))
end.

Fixpoint nums (n : nat) : BushSenior nat :=
match n with
| 0 => N 0 E
| S n' => N n (map (map nums) (map nums (nums n')))
end.

(* Compute size (nums 8). *)

Set Guard Checking.

End BushSenior.

(** * Funktor krzakotwórczy (TODO) *)

Inductive BushF (F : Type -> Type) (A : Type) : Type :=
| E : BushF F A
| N : A -> F (F A) -> BushF F A.

Arguments E {F A}.
Arguments N {F A} _ _.

Fail Inductive Bush (A : Type) : Type :=
| In : BushF Bush A -> Bush A.

Definition mapF
  {F : Type -> Type} {A B : Type}
  (rec : forall {X Y : Type}, (X -> Y) -> F X -> F Y)
  (f : A -> B) (t : BushF F A) : BushF F B :=
match t with
| E => E
| N v t' => N (f v) (rec (rec f) t')
end.

Unset Positivity Checking.
CoInductive CoBush (A : Type) : Type :=
{
  Out : BushF CoBush A;
}.
Set Positivity Checking.

Arguments Out {A} _.

Unset Guard Checking.
Fail CoFixpoint map {A B : Type} (f : A -> B) (b : CoBush A) : CoBush B :=
{|
  Out :=
    match Out b with
    | E => E
    | N x b' => N (f x) (map (map f) b')
    end;
|}.
Set Guard Checking.

(** * Krzaczasty heredyarianizm (TODO) *)

Module HereditaryList.

(*
Inductive HereditaryList (A : Type) : Type :=
| Nil
| Cons (h : A) (t : HereditaryList A)
| WeNeedToGoDeeper (l : HereditaryList (list A)).
*)

Unset Positivity Checking.
Inductive Hereditary (A : Type) : Type :=
| Nil
| Cons (h : A) (t : Hereditary A)
| Deeper (l' : Hereditary (Hereditary A)).
Set Positivity Checking.

Arguments Nil    {A}.
Arguments Cons   {A} h t.
Arguments Deeper {A} l'.

Require Import List.
Import ListNotations.

Fixpoint map {A B : Type} (f : A -> B) (l : Hereditary A) : Hereditary B :=
match l with
| Nil => Nil
| Cons h t => Cons (f h) (map f t)
| Deeper l' => Deeper (map (map f) l')
end.

Unset Guard Checking.
Fixpoint sum (l : Hereditary nat) : nat :=
match l with
| Nil => 0
| Cons h t => h + sum t
| Deeper l' => sum (map sum l')
end.
Set Guard Checking.

Unset Guard Checking.
Fixpoint size {A : Type} (l : Hereditary A) {struct l} : nat :=
match l with
| Nil => 0
| Cons h t => 1 + size t
| Deeper l => sum (map size l)
end.

Fixpoint list_to_Hereditary {A : Type} (l : list A) : Hereditary A :=
match l with
| [] => Nil
| h :: t => Cons h (list_to_Hereditary t)
end.

Compute size (list_to_Hereditary [1; 2; 3]).

Fixpoint Hereditary_to_list {A : Type} (l : Hereditary A) {struct l} : list A :=
match l with
| Nil => []
| Cons h t => h :: Hereditary_to_list t
| Deeper l' => concat (Hereditary_to_list (map Hereditary_to_list l'))
end.
Set Guard Checking.

Fixpoint list_sum (l : list nat) : nat :=
match l with
| [] => 0
| h :: t => h + list_sum t
end.

Lemma sum_list_to_Hereditary :
  forall l : list nat,
    sum (list_to_Hereditary l) = list_sum l.
Proof.
  induction l as [| h t]; cbn; [easy |].
  now rewrite IHt.
Qed.

Fixpoint list_sum_Hereditary_to_list (l : Hereditary nat) :
  list_sum (Hereditary_to_list l) = sum l.
Proof.
  destruct l as [| h t | l']; cbn.
  - easy.
  - now rewrite list_sum_Hereditary_to_list.
  - cut (list_sum (List.map list_sum (Hereditary_to_list (map Hereditary_to_list l'))) =
      sum (map sum l')).
    + admit.
    +
Abort.

End HereditaryList.

(** * W baraku Obamy rosną dziwne krzaki (TODO) *)

Module Obama.

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

#[global] Hint Constructors Exists Exists2 : core.

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

End Obama.