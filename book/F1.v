(** * F1: Koindukcja i korekursja [TODO] *)

(* begin hide *)

(** Pamiętać o tym, że przy negatywnej koindukcji kryterium ścisłej
    pozytywnośći też obowiązuje. Powody są analogiczne jak dla typów
    induktywnych. *)

Fail CoInductive wut : Type :=
{
  haha : wut -> Prop;
}.

(** Ciężko mi jednak stwierdzić w tej chwili, czy jest jakiś odpowiednik
    problemów z nieterminacją. NIEPRODUKTYWNOŚĆ! *)

(* end hide *)

Set Primitive Projections.

(* Set Warnings "+cannot-define-projection".
(* Set Warnings "+non-primitive-record". *)
 *)
Require Import List.
Import ListNotations.

Require Import FunctionalExtensionality.
Require Import Setoid.
Require Import FinFun.

Require Import NArith.
(* Require Import Div2. *)
Require Import ZArith.

(** * Koindukcja (TODO) *)

(** ** Nanana Batman! (TODO) *)

Module Record.

#[projections(primitive)]
Record product (A B : Type) : Type := Pair
{
  outl : A;
  outr : B;
}.

Arguments outl {A B} _.
Arguments outr {A B} _.

Lemma eq_product :
  forall {A B : Type} (p1 p2 : product A B),
    outl p1 = outl p2 -> outr p1 = outr p2 -> p1 = p2.
Proof.
  intros A B [a1 b1] [a2 b2]; cbn.
  now intros -> ->.
Qed.

End Record.

Module Inductive.

#[projections(primitive)]
Inductive product (A B : Type) : Type := Pair
{
  outl : A;
  outr : B;
}.

Arguments outl {A B} _.
Arguments outr {A B} _.

Lemma eq_product :
  forall {A B : Type} (p1 p2 : product A B),
    outl p1 = outl p2 -> outr p1 = outr p2 -> p1 = p2.
Proof.
  Fail intros A B [a1 b1] [a2 b2]; cbn.
Abort.

End Inductive.

Module CoInductive.

#[projections(primitive)]
CoInductive product (A B : Type) : Type := Pair
{
  outl : A;
  outr : B;
}.

Arguments outl {A B} _.
Arguments outr {A B} _.

Lemma eq_product :
  forall {A B : Type} (p1 p2 : product A B),
    outl p1 = outl p2 -> outr p1 = outr p2 -> p1 = p2.
Proof.
  Fail intros A B [a1 b1] [a2 b2]; cbn.
Abort.

End CoInductive.

(** ** Drzewka (TODO) *)

CoInductive coBTree (A : Type) : Type :=
{
  root : option (coBTree A * A * coBTree A)
}.

Arguments root {A} _.

CoFixpoint fmap {A B : Type} (f : A -> B) (t : coBTree A) : coBTree B :=
{|
  root :=
  match root t with
  | None => None
  | Some (l, v, r) => Some (fmap f l, f v, fmap f r)
  end
|}.

CoFixpoint ns (n : nat) : coBTree nat :=
{|
  root := Some (ns (1 + 2 * n), n, ns (2 + 2 * n))
|}.

Inductive BTree (A : Type) : Type :=
| Empty : BTree A
| Node : A -> BTree A -> BTree A -> BTree A.

Arguments Empty {A}.
Arguments Node {A} _ _ _.

Fixpoint ttake (n : nat) {A : Type} (t : coBTree A) : BTree A :=
match n with
| 0 => Empty
| S n' =>
  match root t with
  | None => Empty
  | Some (l, v, r) => Node v (ttake n' l) (ttake n' r)
  end
end.

Compute ttake 5 (ns 0).

CoInductive tsim {A : Type} (t1 t2 : coBTree A) : Prop :=
{
  tsim' :
    root t1 = None /\ root t2 = None \/
    exists (v1 v2 : A) (l1 l2 r1 r2 : coBTree A),
      root t1 = Some (l1, v1, r1) /\
      root t2 = Some (l2, v2, r2) /\
        tsim l1 l2 /\ tsim r1 r2
}.

CoFixpoint mirror {A : Type} (t : coBTree A) : coBTree A :=
{|
  root :=
    match root t with
    | None => None
    | Some (l, v, r) => Some (mirror r, v, mirror l)
    end
|}.

Lemma tsim_mirror_inv :
  forall (A : Type) (t : coBTree A),
    tsim (mirror (mirror t)) t.
Proof.
Admitted.
(*
  cofix CH.
  destruct t as [[[[l v] r]|]]; constructor; [right | left]. cbn.
    exists v, v, (mirror (mirror l)), l, (mirror (mirror r)), r. auto.
    auto.
Qed.
*)

(** ** Rekursja ogólna (TODO) *)

From Typonomikon Require Import F4.

(* begin hide *)
CoInductive Div (A : Type) : Type :=
{
  call : A + Div A
}.

Fixpoint even (n : nat) : bool :=
match n with
| 0 => true
| 1 => false
| S (S n') => even n'
end.

(* The name is very unfortunate. *)
CoFixpoint collatz (n : nat) : Div unit :=
{|
  call :=
  match n with
  | 0 | 1 => inl tt
  | n' =>
    if even n'
    then inr (collatz (Nat.div2 n'))
    else inr (collatz (1 + 3 * n'))
  end
|}.

Fixpoint fuel (n : nat) {A : Type} (d : Div A) : option A :=
match n, d with
| 0, _ => None
| _, Build_Div _ (inl a) => Some a
| S n', Build_Div _ (inr d') => fuel n' d'
end.

Compute fuel 5 (collatz 4).

Arguments uncons {A} _.

CoFixpoint collatz' (n : nat) : CoList nat :=
match n with
| 0 => {| uncons := NilF |}
| 1 => {| uncons := ConsF 1 {| uncons := NilF |} |}
| n' =>
  if even n'
  then {| uncons := ConsF n' (collatz' (Nat.div2 n')) |}
  else {| uncons := ConsF n' (collatz' (1 + 3 * n')) |}
end.

Fixpoint take (n : nat) {A : Type} (l : CoList A) : list A :=
match n, uncons l with
| 0, _ => []
| _, NilF => []
| S n', ConsF h t => h :: take n' t
end.

Compute map (fun n : nat => take 200 (collatz' n)) [30; 31; 32; 33].

Set Warnings "-abstract-large-number".
Compute take 150 (collatz' 12344).

(** * Ćwiczenia (TODO) *)

(** **** Ćwiczenie *)

(** Zdefiniuj typ potencjalnie nieskończonych drzew binarnych trzymających
    wartości typu [A] w węzłach, jego relację bipodobieństwa, predykaty
    "skończony" i "nieskończony" oraz funkcję [mirror], która zwraca
    lustrzane odbicie drzewa. Udowodnij, że bipodobieństwo jest relacją
    równoważności i że funkcja [mirror] jest inwolucją (tzn.
    [mirror (mirror t)] jest bipodobne do [t]), która zachowuje właściwości
    bycia drzewem skończonym/nieskończonym. Pokaż, że drzewo nie może być
    jednocześnie skończone i nieskończone. *)

(* begin hide *)
Module Zad1.

CoInductive coBTree (A : Type) : Type :=
{
  tree : option (coBTree A * A * coBTree A)
}.

Arguments tree {A} _.

CoInductive sim {A : Type} (t1 t2 : coBTree A) : Prop :=
{
  sim' :
    tree t1 = None /\ tree t2 = None \/
    exists (v1 v2 : A) (l1 l2 r1 r2 : coBTree A),
      tree t1 = Some (l1, v1, r1) /\
      tree t2 = Some (l2, v2, r2) /\
        sim l1 l2 /\ sim r1 r2
}.

Lemma sim_refl :
  forall (A : Type) (t : coBTree A), sim t t.
Proof.
Admitted.
(*
  cofix CH.
  constructor.
  destruct t as [[[[l v] r] |]]; cbn.
    right. eauto 10.
    left. auto.
Qed.
*)

Lemma sim_sym :
  forall (A : Type) (t1 t2 : coBTree A),
    sim t1 t2 -> sim t2 t1.
Proof.
  cofix CH.
  constructor.
  destruct H as [H]; decompose [ex or and] H; clear H; eauto 20.
Qed.

Lemma sim_trans :
  forall (A : Type) (t1 t2 t3 : coBTree A),
    sim t1 t2 -> sim t2 t3 -> sim t1 t3.
Proof.
  cofix CH.
  constructor.
  destruct H as [H], H0 as [H0].
  decompose [ex or and] H; decompose [ex or and] H0; clear H H0.
    auto.
    1-2: congruence.
    rewrite H1 in H6. inversion H6; subst; clear H6. eauto 15.
Qed.

CoFixpoint mirror {A : Type} (t : coBTree A) : coBTree A :=
{|
  tree :=
    match tree t with
    | None => None
    | Some (l, v, r) => Some (mirror r, v, mirror l)
    end
|}.

Lemma mirror_involution :
  forall (A : Type) (t : coBTree A),
    sim (mirror (mirror t)) t.
Proof.
Admitted.
(*
  cofix CH.
  destruct t as [[[[l v] r] |]];
  constructor; [right | left].
    exists v, v, (mirror (mirror l)), l, (mirror (mirror r)), r. auto.
    auto.
Qed.
*)

Inductive Finite {A : Type} : coBTree A -> Prop :=
| Finite_None : forall t : coBTree A, tree t = None -> Finite t
| Finite_Some :
    forall (v : A) (l r t : coBTree A),
      Finite l -> Finite r ->
      tree t = Some (l, v, r) -> Finite t.

CoInductive Infinite {A : Type} (t : coBTree A) : Prop :=
{
  root : A;
  left : coBTree A;
  right : coBTree A;
  p : tree t = Some (left, root, right);
  Infinite_left : Infinite left;
  Infinite_right : Infinite right;
}.

Lemma Finite_mirror :
  forall (A : Type) (t : coBTree A),
    Finite t -> Finite (mirror t).
Proof.
  induction 1.
    constructor. cbn. rewrite H. reflexivity.
    eapply Finite_Some.
      exact IHFinite2.
      exact IHFinite1.
      cbn. rewrite H1. reflexivity.
Qed.

Lemma Infinite_mirror :
  forall (A : Type) (t : coBTree A),
    Infinite t -> Infinite (mirror t).
Proof.
  cofix CH.
  inversion 1. econstructor.
    cbn. rewrite p. reflexivity.
    apply CH; assumption.
    apply CH; assumption.
Qed.

Lemma Finite_Infinite_contradiction :
  forall (A : Type) (t : coBTree A),
    Finite t -> Infinite t -> False.
Proof.
  induction 1; inversion 1; subst; congruence.
Qed.

Lemma Finite_or_Infinite : (* TODO: dla coBTree *)
  forall {A : Type} (t : coBTree A),
    ~ ~ (Finite t \/ Infinite t).
Proof.
Admitted.
(*
  intros A t H.
  apply H. right.
  revert t H. cofix CH.
  intros t H.
  destruct t as [[[[l x] r] |]].
    econstructor.
      cbn. reflexivity.
      apply CH. destruct 1.
        apply H. left.
Abort.
*)

End Zad1.
(* end hide *)

(** **** Ćwiczenie *)

(** Znajdź taką rodzinę typów koinduktywnych [C], że dla dowolnego
    typu [A], [C A] jest w bijekcji z typem funkcji [nat -> A]. Przez
    bijekcję będziemy tu rozumieć funkcję, która ma odwrotność, z którą
    w obie strony składa się do identyczności.

    Uwaga: nie da się tego udowodnić bez użycia dodatkowych aksjomatów,
    które na szczęście są bardzo oczywiste i same się narzucają. *)

(* begin hide *)
Require Import FunctionalExtensionality.
Require Import FinFun.

Module Zad2.

CoInductive Stream (A : Type) : Type :=
{
  hd : A;
  tl : Stream A;
}.

Arguments hd {A}.
Arguments tl {A}.

CoInductive sim {A : Type} (s1 s2 : Stream A) : Prop :=
{
  hds : hd s1 = hd s2;
  tls : sim (tl s1) (tl s2);
}.

Axiom sim_eq :
  forall (A : Type) (s1 s2 : Stream A), sim s1 s2 -> s1 = s2.

CoFixpoint memo_aux {A : Type} (f : nat -> A) (n : nat) : Stream A :=
{|
  hd := f n;
  tl := memo_aux f (S n);
|}.

Definition memo {A : Type} (f : nat -> A) : Stream A :=
  memo_aux f 0.

Fixpoint index {A : Type} (s : Stream A) (n : nat) : A :=
match n with
| 0 => hd s
| S n' => index (tl s) n'
end.

Fixpoint drop {A : Type} (n : nat) (s : Stream A) : Stream A :=
match n with
| 0 => s
| S n' => drop n' (tl s)
end.

Lemma tl_drop :
  forall (A : Type) (n : nat) (s : Stream A),
    tl (drop n s) = drop (S n) s.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.

Lemma memo_index_aux' :
  forall (f : nat -> nat) (n m : nat),
    sim (memo_aux f (n + m)) (memo_aux (fun k : nat => f (n + k)) m).
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    rewrite plus_n_Sm. apply CH.
Qed.

Lemma memo_index_aux :
  forall (A : Type) (s : Stream A) (n : nat),
    sim (memo_aux (index s) n) (drop n s).
Proof.
  cofix CH.
  constructor; cbn.
    revert s. induction n as [| n']; cbn in *; intros.
      reflexivity.
      apply IHn'.
    rewrite tl_drop. apply CH.
Qed.

Lemma memo_index :
  forall (A : Type) (s : Stream A),
    sim (memo (index s)) s.
Proof.
  intros. unfold memo. apply memo_index_aux.
Qed.

Lemma index_memo_aux :
  forall (A : Type) (f : nat -> A) (n : nat),
    index (memo_aux f n) = fun k : nat => f (k + n).
Proof.
  intros. extensionality k. revert n.
  induction k as [| k']; cbn; intros.
    reflexivity.
    rewrite IHk'. rewrite plus_n_Sm. reflexivity.
Qed.

Lemma index_memo :
  forall (A : Type) (f : nat -> A),
    index (memo f) = fun k : nat => f k.
Proof.
  intros.
  replace (fun k : nat => f k) with (fun k : nat => f (k + 0)).
    apply index_memo_aux.
    extensionality k. rewrite <- plus_n_O. reflexivity.
Qed.

Lemma natfun_is_stream_nat :
  Bijective (@memo nat).
Proof.
  red. exists index. split; intros.
    apply index_memo.
    apply sim_eq. apply memo_index.
Qed.

End Zad2.
(* end hide *)

(** **** Ćwiczenie *)

(** Zdefiniuj pojęcie "nieskończonego łańcucha malejącego" (oczywiście
    za pomocą koindukcji) i udowodnij, że jeżeli relacja jest dobrze
    ufundowana, to nie ma nieskończonych łańcuchów malejących. *)

(* begin hide *)
Module Zad5.

CoInductive DecChain {A : Type} (R : A -> A -> Prop) (x : A) : Type :=
{
  hd : A;
  R_hd_x : R hd x;
  tl : DecChain R hd;
}.

Lemma wf_no_DecChain :
  forall (A : Type) (R : A -> A -> Prop) (x : A),
    well_founded R -> DecChain R x -> False.
Proof.
  unfold well_founded.
  intros A R x H C.
  specialize (H x).
  induction H.
  inversion C.
  apply H0 with hd0; assumption.
Qed.

End Zad5.
(* end hide *)