(** * F0b: Nierówność i różność [TODO] *)

Set Universe Polymorphism.

Require Import Arith.
Require Import Bool.
Require Import Equality.
Require Import FunctionalExtensionality.

Require Import List.
Import ListNotations.

From Typonomikon Require Import F0a.
From Typonomikon Require Import D5.

(** * Różność *)

(** ** (Słaba) różność funkcji *)

(** Funkcje są różne (w silnym sensie), gdy różnią się dla jakiegoś
    argumentu. *)

Definition fun_apart {A B : Type} (R : B -> B -> Type) (f g : A -> B) : Type :=
  {x : A & R (f x) (g x)}.

Lemma fun_apart_spec :
  forall {A B : Type} (R : B -> B -> Type) (f g : A -> B),
    (forall x : B, R x x -> False) ->
      fun_apart R f g -> f <> g.
(* begin hide *)
Proof.
  intros A B R f g HR [x r] ->.
  now apply HR in r.
Qed.
(* end hide *)

Lemma fun_apart_spec' :
  forall {A B : Type} (R : B -> B -> Type) (f g : A -> B),
    (forall x : B, R x x -> False) ->
      fun_apart R f g -> ~ (forall x : A, f x = g x).
(* begin hide *)
Proof.
  intros A B R f g HR [x r] Hext.
  rewrite Hext in r.
  now apply HR in r.
Qed.
(* end hide *)

(** ** Silna różność funkcji (TODO) *)

Inductive strong_fun_apart
  {A B : Type} (RA : A -> A -> Type) (RB : B -> B -> Type) (f g : A -> B) : Type :=
| sfa (x1 x2 : A) (ra : RA x1 x2) (rb : RB (f x1) (g x2)).

Lemma strong_fun_apart_spec :
  forall {A B : Type} (RB : B -> B -> Type) (f g : A -> B),
    strong_fun_apart eq RB f g -> fun_apart RB f g.
(* begin hide *)
Proof.
  intros A B RB f g [x ? <- rb].
  now exists x.
Qed.
(* end hide *)

(** ** Różność funkcji zależnych (TODO) *)

Inductive dep_fun_apart
  {A : Type} {B : A -> Type}
  (R : forall x : A, B x -> B x -> Type)
  (f g : forall x : A, B x) : Type :=
| dep_fun_apart' : forall {x : A}, R x (f x) (g x) -> dep_fun_apart R f g.

Lemma dep_fun_apart_spec :
  forall
    {A : Type} {B : A -> Type}
    (R : forall x : A, B x -> B x -> Type)
    (f g : forall x : A, B x)
    (HR : forall {x : A} (y : B x), R x y y -> False),
      dep_fun_apart R f g -> f <> g.
(* begin hide *)
Proof.
  intros A B R f g HR [x r] ->.
  apply (HR _ (g x)). apply r.
Qed.
(* end hide *)

Lemma dep_fun_apart_spec' :
  forall
    {A : Type} {B : A -> Type}
    (R : forall x : A, B x -> B x -> Type)
    (f g : forall x : A, B x)
    (HR : forall {x : A} (y : B x), R x y y -> False),
      dep_fun_apart R f g -> ~ (forall x : A, f x = g x).
(* begin hide *)
Proof.
  intros A B R f g HR [x r] Hext.
  apply (HR _ (g x)). rewrite <- Hext at 1. assumption.
Qed.
(* end hide *)

(** ** Liczby naturalne (TODO) *)

(** A co to znaczy, że liczby naturalne nie są równe? *)

(** Powinien być tylko jeden dowód na nierówność. *)

(** *** Nierówność liczb naturalnych - rekurencyjnie *)

Module nat_neq_rec.

Fixpoint code (n m : nat) : Type :=
match n, m with
| 0, 0 => False
| 0, S _ => True
| S _, 0 => True
| S n', S m' => code n' m'
end.

Lemma isProp_code :
  forall {n m : nat} (c1 c2 : code n m), c1 = c2.
(* begin hide *)
Proof.
  induction n as [| n'], m as [| m']; cbn.
    1-3: destruct c1, c2; reflexivity.
    apply IHn'.
Qed.
(* end hide *)

Fixpoint encode {n m : nat} {struct n} : n <> m -> code n m.
(* begin hide *)
Proof.
  destruct n as [| n'], m as [| m']; cbn; intro p.
    apply p. reflexivity.
    exact I.
    exact I.
    apply encode. intro q. apply p. f_equal. exact q.
Defined.
(* end hide *)

Fixpoint decode {n m : nat} : code n m -> n <> m.
(* begin hide *)
Proof.
  destruct n as [| n'], m as [| m']; cbn; intro p.
    contradiction.
    inversion 1.
    inversion 1.
    intro q. apply (decode _ _ p). inversion q. reflexivity.
Defined.
(* end hide *)

Lemma encode_decode :
  forall {n m : nat} (p : n <> m),
    decode (encode p) = p.
Proof.
  intros.
  apply functional_extensionality.
  destruct x.
  contradiction.
Qed.

Lemma decode_encode :
  forall {n m : nat} (c : code n m),
    encode (decode c) = c.
Proof.
  intros.
  apply isProp_code.
Qed.

End nat_neq_rec.

(** *** Nierówność liczb naturalnych - induktywnie *)

Module nat_neq_ind.

Inductive nat_neq : nat -> nat -> Prop :=
| ZS : forall n : nat, nat_neq 0 (S n)
| SZ : forall n : nat, nat_neq (S n) 0
| SS : forall n m : nat, nat_neq n m -> nat_neq (S n) (S m).

Arguments ZS {n}.
Arguments SZ {n}.
Arguments SS {n m} _.

Scheme nat_neq_ind' := Induction for nat_neq Sort Prop.

Lemma isProp_nat_neq :
  forall {n m : nat} (p q : nat_neq n m), p = q.
(* begin hide *)
Proof.
  induction p using nat_neq_ind';
  dependent destruction q.
  - reflexivity.
  - reflexivity.
  - apply f_equal, IHp.
Qed.
(* end hide *)

Fixpoint encode {n m : nat} : n <> m -> nat_neq n m :=
match n, m with
| 0, 0       => fun p => match p eq_refl with end
| 0, S m'    => fun _ => @ZS m'
| S n', 0    => fun _ => @SZ n'
| S n', S m' => fun p => SS (@encode n' m' (fun p' => p (f_equal S p')))
end.

Fixpoint decode {n m : nat} (c : nat_neq n m) : n <> m.
Proof.
  destruct c.
  - inversion 1.
  - inversion 1.
  - inversion 1. apply (decode _ _ c). assumption.
Defined.

Lemma encode_decode :
  forall {n m : nat} (p : n <> m),
    decode (encode p) = p.
(* begin hide *)
Proof.
  induction n as [| n'];
  destruct  m as [| m'];
  cbn; intros.
  - contradiction.
  - apply functional_extensionality. inversion x.
  - apply functional_extensionality. inversion x.
  - apply functional_extensionality. contradiction.
Qed.
(* end hide *)

Lemma decode_encode :
  forall {n m : nat} (c : nat_neq n m),
    encode (decode c) = c.
(* begin hide *)
Proof.
  induction c using nat_neq_ind'; cbn; [reflexivity.. |].
  rewrite <- IHc. do 2 f_equal.
  apply functional_extensionality.
  destruct x; cbn.
  rewrite IHc.
  reflexivity.
Qed.
(* end hide *)

End nat_neq_ind.

(** *** Tadam *)

Module nat_eq_neq.

Import nat_eq_ind nat_neq_ind.

Lemma nat_eq_dec :
  forall n m : nat, nat_eq n m + nat_neq n m.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m'].
  - left. constructor.
  - right. constructor.
  - right. constructor.
  - destruct (IHn' m').
    + left. constructor. assumption.
    + right. constructor. assumption.
Qed.
(* end hide *)

End nat_eq_neq.

(** ** Listy *)

(** *** Różność list - induktywnie *)

Module list_apart_ind.

Inductive list_apart
  {A : Type} (R : A -> A -> Type) : list A -> list A -> Type :=
| nc  : forall (h : A) (t : list A), list_apart R [] (h :: t)
| cn  : forall (h : A) (t : list A), list_apart R (h :: t) []
| cc1 : forall (h1 h2 : A) (t1 t2 : list A),
          R h1 h2 -> list_apart R (h1 :: t1) (h2 :: t2)
| cc2 : forall (h1 h2 : A) (t1 t2 : list A),
          list_apart R t1 t2 -> list_apart R (h1 :: t1) (h2 :: t2).

#[global] Hint Constructors list_apart : core.

Lemma list_apart_irrefl :
  forall {A : Type} {R : A -> A -> Prop} (l1 l2 : list A),
    (forall x : A, R x x -> False) ->
      list_apart R l1 l2 -> l1 <> l2.
(* begin hide *)
Proof.
  induction 2; inversion 1; subst.
  - apply (H _ r).
  - apply IHX. reflexivity.
Defined.
(* end hide *)

Lemma list_apart_sym :
  forall {A : Type} {R : A -> A -> Prop} (l1 l2 : list A),
    (forall x y : A, R x y -> R y x) ->
      list_apart R l1 l2 -> list_apart R l2 l1.
(* begin hide *)
Proof.
  induction 2; [constructor.. |].
  - apply H. assumption.
  - constructor 4. assumption.
Defined.
(* end hide *)

Lemma list_apart_cotrans :
  forall {A : Type} {R : A -> A -> Prop} (l1 l3 : list A),
    (forall x y z : A, R x z -> R x y + R y z) ->
      list_apart R l1 l3 -> forall l2 : list A,
        list_apart R l1 l2 + list_apart R l2 l3.
(* begin hide *)
Proof.
  induction 2; intros.
  - destruct l2; [right | left]; constructor.
  - destruct l2; [left | right]; constructor.
  - destruct l2 as [| h t].
    + left. constructor.
    + destruct (X _ h _ r).
      * left. constructor. assumption.
      * right. constructor. assumption.
  - destruct l2 as [| h t].
    + left. constructor.
    + destruct (IHX0 t).
      * left. constructor 4. assumption.
      * right. constructor 4. assumption.
Defined.
(* end hide *)

(** *** Różność list a [Exists2] *)

Inductive Exists2
  {A : Type} (R : A -> A -> Type) : list A -> list A -> Type :=
| E2_here :
    forall {h1 h2 : A} (t1 t2 : list A),
      R h1 h2 -> Exists2 R (h1 :: t1) (h2 :: t2)
| E2_there :
    forall {h1 h2 : A} {t1 t2 : list A},
      Exists2 R t1 t2 -> Exists2 R (h1 :: t1) (h2 :: t2).

Lemma Exists2_list_apart :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    Exists2 R l1 l2 -> list_apart R l1 l2.
(* begin hide *)
Proof.
  induction 1.
  - constructor. assumption.
  - constructor 4. assumption.
Qed.
(* end hide *)

Inductive DifferentStructure
  {A : Type} : list A -> list A -> Type :=
| DS_nc :
    forall (h : A) (t : list A),
      DifferentStructure [] (h :: t)
| DS_cn :
    forall (h : A) (t : list A),
      DifferentStructure (h :: t) []
| DS_cc :
    forall (h1 h2 : A) {t1 t2 : list A},
      DifferentStructure t1 t2 ->
        DifferentStructure (h1 :: t1) (h2 :: t2).

Lemma isProp_DS :
  forall
    {A : Type} {l1 l2 : list A}
    (p q : DifferentStructure l1 l2),
      p = q.
(* begin hide *)
Proof.
  induction p; intro q.
  - refine (match q with DS_nc _ _   => _ end). reflexivity.
  - refine (match q with DS_cn _ _   => _ end). reflexivity.
  - dependent destruction q. f_equal. apply IHp.
Qed.
(* end hide *)

(** Insajt, że o ja pierdole: [list_apart] to w sumie [Exists2] lub
    [DifferentStructure], czyli listy różnią się, gdy różnią się
    na którymś elemencie lub mają różną długość. *)

Lemma list_apart_to_ED :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    list_apart R l1 l2 -> Exists2 R l1 l2 + DifferentStructure l1 l2.
(* begin hide *)
Proof.
  induction 1.
  - right. constructor.
  - right. constructor.
  - left. constructor. assumption.
  - destruct IHX.
    + left. constructor 2. assumption.
    + right. constructor. assumption.
Defined.
(* end hide *)

Lemma list_apart_to_ED_conv :
  forall {A : Type} {R : A -> A -> Prop} {l1 l2 : list A},
    Exists2 R l1 l2 + DifferentStructure l1 l2 -> list_apart R l1 l2.
(* begin hide *)
Proof.
  destruct 1.
  - induction e.
    + constructor. assumption.
    + constructor 4. assumption.
  - induction d.
    + constructor.
    + constructor.
    + constructor 4. assumption.
Defined.
(* end hide *)

Lemma okurwa :
  forall
    (A : Type) (R : A -> A -> Type) (h1 h2 : A) (t1 t2 : list A)
    (r1 : R h1 h2) (r2 : R h1 h2),
      @inl _
        (DifferentStructure (h1 :: t1) (h2 :: t2))
        (E2_here R t1 t2 r1)
      =
      inl (E2_here R t1 t2 r2) ->
        r1 = r2.
(* begin hide *)
Proof.
  assert (forall (A B : Type) (x y : A), @inl A B x = inl y -> x = y)
    by (inversion 1; reflexivity).
  intros. apply H in H0.
  apply (f_equal
    (fun x : Exists2 R (h1 :: t1) (h2 :: t2) =>
      match x with
      | E2_here _ _ _ r => Some r
      | _             => None
      end))
  in H0.
  inversion H0. reflexivity.
Qed.
(* end hide *)

Lemma list_apart_to_ED_list_apart_to_ED_conv :
  forall
    {A : Type} {R : A -> A -> Prop} {l1 l2 : list A}
    (c : list_apart R l1 l2),
      list_apart_to_ED_conv (list_apart_to_ED c) = c.
(* begin hide *)
Proof.
  induction c; cbn; [reflexivity.. |].
  destruct (list_apart_rect A R _) eqn: Heq; cbn; f_equal.
  - induction e; cbn in *.
    + dependent destruction c; cbn in *.
      * f_equal. symmetry. apply okurwa in Heq. assumption.
      * cbn in *. rewrite Heq in IHc. cbn in IHc. inversion IHc.
    + dependent destruction c.
      * cbn in *. inversion Heq.
      * cbn in *. rewrite Heq in IHc. cbn in IHc. assumption.
  - dependent destruction c; cbn in *.
    + inversion Heq; subst; cbn. reflexivity.
    + inversion Heq; subst; cbn. reflexivity.
    + inversion Heq.
    + rewrite Heq in IHc. cbn in IHc. assumption.
Qed.
(* end hide *)

Lemma list_apart_to_ED_conv_list_apart_to_ED :
  forall
    {A : Type} {R : A -> A -> Prop} {l1 l2 : list A}
    (x : Exists2 R l1 l2 + DifferentStructure l1 l2),
      list_apart_to_ED (list_apart_to_ED_conv x) = x.
(* begin hide *)
Proof.
  destruct x.
  - induction e; cbn in *.
    + reflexivity.
    + destruct (list_apart_rect A R _); inversion IHe. reflexivity.
  - induction d; cbn in *.
    + reflexivity.
    + reflexivity.
    + destruct (list_apart_rect A R _); inversion IHd. reflexivity.
Qed.
(* end hide *)

End list_apart_ind.

(** *** Różność list - rekurencyjnie *)

Fixpoint list_apart'
  {A : Type} (R : A -> A -> Type) (l1 l2 : list A) : Type :=
match l1, l2 with
| [], [] => False
| h1 :: t1, h2 :: t2 => R h1 h2 + list_apart' R t1 t2
| _, _ => True
end.

Lemma apart_to_apart' :
  forall {A : Type} {R : A -> A -> Type} {l1 l2 : list A},
    list_apart_ind.list_apart R l1 l2 -> list_apart' R l1 l2.
(* begin hide *)
Proof.
  now induction 1; cbn; [trivial.. | left | right].
Defined.
(* end hide *)

Lemma apart'_to_apart :
  forall {A : Type} {R : A -> A -> Type} {l1 l2 : list A},
    list_apart' R l1 l2 -> list_apart_ind.list_apart R l1 l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn.
  - easy.
  - constructor.
  - constructor.
  - intros [r | H].
    + now constructor 3.
    + now constructor 4; apply IHt1.
Defined.
(* end hide *)

Lemma appart_to_apart'_to_apart :
  forall {A : Type} (R : A -> A -> Type) (l1 l2 : list A)
    (x : list_apart_ind.list_apart R l1 l2),
      apart'_to_apart (apart_to_apart' x) = x.
(* begin hide *)
Proof.
  dependent induction x; cbn; [easy.. |].
  destruct (list_rect _ _ _); f_equal.
  - now dependent destruction x.
  - now dependent destruction x.
  - dependent destruction x; admit.
  - dependent destruction x.
Abort.
(* end hide *)

(** ** Różność strumieni (TODO) *)

From Typonomikon Require F2 F3.

Module Stream_apart.

Import F2.

Inductive Stream_apart
  {A : Type} (R : A -> A -> Type) : Stream A -> Stream A -> Type :=
| Stream_apart_hd :
    forall s1 s2 : Stream A,
      R (hd s1) (hd s2) -> Stream_apart R s1 s2
| Stream_apart_tl :
    forall s1 s2 : Stream A,
      Stream_apart R (tl s1) (tl s2) -> Stream_apart R s1 s2.

Definition Stream_neq {A : Type} : Stream A -> Stream A -> Type :=
  Stream_apart (fun x y => x <> y).

Lemma Stream_neq_Stream_apart :
  forall {A : Type} (R : A -> A -> Type) {s1 s2 : Stream A},
    (forall x : A, R x x -> False) ->
      Stream_apart R s1 s2 -> Stream_neq s1 s2.
(* begin hide *)
Proof.
  intros A R s1 s2 Hirrefl.
  induction 1.
  - constructor 1.
    intros Heq.
    apply Hirrefl with (hd s1).
    now rewrite Heq at 2.
  - constructor 2.
    now apply IHX.
Qed.
(* end hide *)

Lemma Stream_neq_not_sim :
  forall {A : Type} {s1 s2 : Stream A},
    Stream_neq s1 s2 -> ~ sim s1 s2.
(* begin hide *)
Proof.
  induction 1; intros []; contradiction.
Qed.
(* end hide *)

Lemma not_sim_neq :
  forall {A : Type} {s1 s2 : Stream A},
    ~ sim s1 s2 -> s1 <> s2.
(* begin hide *)
Proof.
  intros A s1 s2 Hsn ->.
  now apply Hsn, sim_refl.
Qed.
(* end hide *)

End Stream_apart.

(** ** Nierówność liczb konaturalnych *)

Module conat_apart.

Import F3.

Inductive conat_apart : conat -> conat -> Prop :=
| conat_apart_zero_succ :
    forall c1 c2 : conat,
      out c1 = Z -> out c2 <> Z -> conat_apart c1 c2
| conat_apart_succ_zero :
    forall c1 c2 : conat,
      out c1 <> Z -> out c2 = Z -> conat_apart c1 c2
| conat_apart_succ_succ :
    forall (c1 c2 : conat) (c1' c2' : conat),
      out c1 = S c1' -> out c2 = S c2' -> conat_apart c1' c2' -> conat_apart c1 c2.

Lemma conat_apart_spec :
  forall n m : conat,
    conat_apart n m -> n <> m.
(* begin hide *)
Proof.
  induction 1; intro Heq; inversion Heq; congruence.
Qed.
(* end hide *)

Lemma conat_apart_irrefl :
  forall n : conat, ~ conat_apart n n.
(* begin hide *)
Proof.
  intros n Hneq.
  now eapply conat_apart_spec; eauto.
Qed.
(* end hide *)

End conat_apart.

(** ** Różność kolist *)

From Typonomikon Require F4.

Module CoList_apart.

Import F4.

Inductive CoList_apart {A : Type} (R : A -> A -> Type) (l1 l2 : CoList A) : Type :=
| CLa_nil_cons :
    uncons l1 = NilF -> uncons l2 <> NilF -> CoList_apart R l1 l2
| CLa_cons_nil :
    uncons l1 <> NilF -> uncons l2 = NilF -> CoList_apart R l1 l2
| CLa_head :
    forall
      {h1 : A} {t1 : CoList A} (Hu1 : uncons l1 = ConsF h1 t1)
      {h2 : A} {t2 : CoList A} (Hu2 : uncons l2 = ConsF h2 t2),
        R h1 h2 -> CoList_apart R l1 l2
| CLa_tail :
    forall
      {h1 : A} {t1 : CoList A} (Hu1 : uncons l1 = ConsF h1 t1)
      {h2 : A} {t2 : CoList A} (Hu2 : uncons l2 = ConsF h2 t2),
        CoList_apart R t1 t2 -> CoList_apart R l1 l2.

Lemma CoList_apart_spec :
  forall {A : Type} {R : A -> A -> Type} {l1 l2 : CoList A},
    (forall x : A, R x x -> False) ->
      CoList_apart R l1 l2 -> ~ lsim l1 l2.
(* begin hide *)
Proof.
  intros A R l1 l2 HR; induction 1; intros [Hlsim].
  - inversion Hlsim; subst; clear Hlsim; congruence.
  - inversion Hlsim; subst; clear Hlsim; congruence.
  - inversion Hlsim; subst; clear Hlsim.
    + congruence.
    + apply (HR h3). congruence.
  - inversion Hlsim; subst; clear Hlsim; congruence.
Qed.
(* end hide *)

End CoList_apart.