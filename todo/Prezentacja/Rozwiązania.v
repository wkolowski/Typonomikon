(** **** Zadanie 1 *)

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
  cofix CH.
  constructor.
  destruct t as [[[[l v] r] |]]; cbn.
    right. eauto 10.
    left. auto.
Qed.

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
  cofix CH.
  destruct t as [[[[l v] r] |]];
  constructor; [right | left].
    exists v, v, (mirror (mirror l)), l, (mirror (mirror r)), r. auto.
    auto.
Qed.

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

End Zad1.

(** **** Zadanie 2 *)

Module Zad2.

Require Import FunctionalExtensionality.
Require Import FinFun.

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

(** **** Zadanie 3 *)

Module Zad3.

Inductive T : Type :=
    | from0 : nat -> T
    | fromω : nat -> T
    | ωω : T.

Definition R (x y : T) : Prop :=
match x, y with
    | from0 n, from0 m => n < m
    | from0 _, _ => True
    | fromω _, from0 _ => False
    | fromω n, fromω m => n < m
    | fromω _, _ => True
    | ωω, _ => False
end.

Require Import Omega.

Lemma R_trans :
  forall a b c : T, R a b -> R b c -> R a c.
Proof.
  induction a as [n | n |];
  destruct b as [m | m |], c as [k | k |]; cbn; try omega; auto.
Qed.

Lemma Acc_from0 :
  forall n : nat, Acc R (from0 n).
Proof.
  induction n as [| n']; cbn.
    constructor. destruct y; inversion 1.
    constructor. destruct y; inversion 1; subst.
      assumption.
      inversion IHn'. constructor. intros. apply H0.
        eapply R_trans; eauto.
Qed.

Lemma Acc_fromω :
  forall n : nat, Acc R (fromω n).
Proof.
  induction n as [| n']; cbn.
    constructor. destruct y; inversion 1. apply Acc_from0.
    constructor. destruct y; inversion 1; subst.
      apply Acc_from0.
      assumption.
      inversion IHn'. constructor. intros. apply H0.
        eapply R_trans; eauto.
Qed.

Lemma wf_R : well_founded R.
Proof.
  unfold well_founded.
  destruct a as [m | m |].
    apply Acc_from0.
    apply Acc_fromω.
    constructor. destruct y; inversion 1.
      apply Acc_from0.
      apply Acc_fromω.
Qed.

End Zad3.

(** **** Zadanie 4 *)

Module Zad4.

Definition funord
  (A : Type) {B : Type} (R : B -> B -> Prop) (f g : A -> B) : Prop :=
    forall x : A, R (f x) (g x).

Lemma Acc_antirefl :
  forall (A : Type) (R : A -> A -> Prop) (x : A),
    Acc R x -> ~ R x x.
Proof.
  induction 1. intro. apply (H0 x); assumption.
Qed.

Lemma wf_funord_empty :
  forall (A B : Type) (R : B -> B -> Prop),
    (A -> False) -> ~ well_founded (funord A R).
Proof.
  unfold well_founded.
  intros A B R Hempty H.
  pose (f := fun a : A => match Hempty a with end : B); clearbody f.
  apply (Acc_antirefl _ (funord A R) f).
    apply H.
    unfold funord. intro. contradiction.
Qed.

Lemma wf_funord_nonempty :
  forall (A B : Type) (R : B -> B -> Prop) (a : A),
    well_founded R -> well_founded (funord A R).
Proof.
  unfold well_founded.
  intros A B R a Hwf f.
  pose (b := f a).
  assert (b = f a) by reflexivity; clearbody b.
  revert b f H.
  apply (@well_founded_induction B R Hwf
    (fun b => forall f, b = f a -> Acc (funord A R) f)).
  intros b IH f Heq. constructor. intros g Hord.
  apply IH with (g a).
    unfold funord in Hord. specialize (Hord a). subst. apply Hord.
    reflexivity.
Qed.

End Zad4.

(** **** Zadanie 5 *)

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

(** **** Zadanie 6 *)

Module Zad6.

Require Import List.
Import ListNotations.

Require Import Omega.

Definition lengthOrder {A : Type} (l1 l2 : list A) : Prop :=
  length l1 < length l2.

Lemma wf_inverse_image :
  forall (A B : Type) (f : A -> B) (R : B -> B -> Prop),
    well_founded R -> well_founded (fun x y => R (f x) (f y)).
Proof.
  unfold well_founded.
  intros A B f R H x.
  pose (b := f x). assert (b = f x) by reflexivity. clearbody b.
  specialize (H b). revert x H0. induction H. rename x into b.
  intros x Heq. constructor. intros.
  eapply H0. rewrite Heq.
    eauto.
    reflexivity.
Defined.

Lemma wf_lengthOrder :
  forall A : Type, well_founded (@lengthOrder A).
Proof.
  intros. apply (wf_inverse_image _ _ (@length A)). apply lt_wf.
Defined.

Fixpoint split
  (n : nat) {A : Type} (l : list A) : option (list A * list A) :=
match n, l with
    | 0, _ => Some ([], l)
    | S _, [] => None
    | S n', h :: t =>
        match split n' t with
            | None => None
            | Some (l1, l2) => Some (h :: l1, l2)
        end
end.

Lemma lengthOrder_split_aux :
  forall (n : nat) (A : Type) (l : list A) (l1 l2 : list A),
    split n l = Some (l1, l2) ->
      n = 0  \/ lengthOrder l2 l.
Proof.
  induction n as [| n']; cbn; intros.
    left. reflexivity.
    right. destruct l as [| h t]; cbn in *.
      inversion H.
      case_eq (split n' t).
        intros [l1' l2'] H'. rewrite H' in H. inversion H; subst.
          destruct (IHn' A t l1' l2 H').
            rewrite H0 in *. cbn in *. inversion H'; subst.
              apply le_n.
            apply lt_trans with (length t).
              assumption.
              apply le_n.
        intro. rewrite H0 in H. inversion H.
Qed.

Lemma lengthOrder_split :
  forall (n : nat) (A : Type) (l : list A) (l1 l2 : list A),
    split (S n) l = Some (l1, l2) -> lengthOrder l2 l.
Proof.
  intros. destruct (lengthOrder_split_aux _ _ _ _ _ H).
    inversion H0.
    assumption.
Qed.

Definition rotn {A : Type} (n : nat) (l : list A) : list A.
Proof.
  revert l n.
  apply (@well_founded_induction_type _ _ (@wf_lengthOrder A)
    (fun l => nat -> list A)).
  intros l IH n.
  case_eq (split (S n) l).
    intros [l1 l2] H. refine (rev l1 ++ IH l2 _ n).
      eapply lengthOrder_split. exact H.
    intro. exact l.
Defined.

Compute rotn 1 [1; 2; 3; 4; 5; 6; 7].

Lemma rotn_eq :
  forall (A : Type) (n : nat) (l : list A),
    rotn n l =
    match split (S n) l with
        | None => l
        | Some (l1, l2) => rev l1 ++ rotn n l2
    end.
Proof.
  intros. revert l n.
  apply (@well_founded_induction _ _ (@wf_lengthOrder A)
    (fun l => forall n : nat, _)).
  intros l IH n.
  case_eq (split (S n) l).
    intros [l1 l2] H.
Admitted.

Inductive Rotn {A : Type} : nat -> list A -> list A -> Prop :=
    | Rotn_None :
        forall (n : nat) (l : list A),
          split (S n) l = None -> Rotn n l l
    | Rotn_Some :
        forall (n : nat) (l l1 l2 r : list A),
          split (S n) l = Some (l1, l2) ->
            Rotn n l2 r -> Rotn n l (rev l1 ++ r).

Lemma Rotn_complete :
  forall (A : Type) (n : nat) (l r : list A),
    Rotn n l r -> rotn n l = r.
Proof.
  induction 1.
    rewrite rotn_eq, H. reflexivity.
    rewrite rotn_eq, H, IHRotn. reflexivity.
Qed.

Lemma Rotn_correct :
  forall (A : Type) (n : nat) (l : list A),
    Rotn n l (rotn n l).
Proof.
  intros A n l. revert l n.
  apply (@well_founded_induction _ _ (@wf_lengthOrder A)
    (fun l => forall n : nat, Rotn n l (rotn n l))).
  intros l IH n.
  rewrite rotn_eq. case_eq (split (S n) l).
    intros [l1 l2] H. econstructor.
      eassumption.
      apply IH. apply (lengthOrder_split n _ l l1). assumption.
    intros. constructor. assumption.
Qed.

Lemma rotn_ind :
  forall (A : Type) (P : nat -> list A -> list A -> Prop),
    (forall (n : nat) (l : list A),
      split (S n) l = None -> P n l l) ->
    (forall (n : nat) (l l1 l2 : list A),
      split (S n) l = Some (l1, l2) ->
        P n l2 (rotn n l2) -> P n l (rev l1 ++ rotn n l2)) ->
    forall (n : nat) (l : list A), P n l (rotn n l).
Proof.
  intros A P H1 H2 n l.
  refine (Rotn_ind A P H1 _ n l (rotn n l) _).
    intros. apply Rotn_complete in H0. rewrite <- H0. apply H2.
      assumption.
      rewrite H0. assumption.
    apply Rotn_correct.
Qed.

Lemma split_None :
  forall (A : Type) (n : nat) (l : list A),
    split n l = None -> length l < n.
Proof.
  induction n as [| n']; cbn; intros.
    inversion H.
    destruct l as [| h t]; cbn in H.
      apply le_n_S, le_0_n.
      case_eq (split n' t).
        intros [l1 l2] Heq. rewrite Heq in H. inversion H.
        intro. cbn. apply lt_n_S. apply IHn'. assumption.
Qed.

Lemma split_app :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 = n -> split n (l1 ++ l2) = Some (l1, l2).
Proof.
  induction n as [| n']; cbn; intros.
    destruct l1; cbn.
      reflexivity.
      inversion H.
    destruct l1 as [| h t]; cbn.
      inversion H.
      rewrite IHn'.
        reflexivity.
        cbn in H. inversion H. reflexivity.
Qed.

Lemma split_length :
  forall {A : Type} {n : nat} {l1 l2 : list A},
    split n (l1 ++ l2) = Some (l1, l2) -> length l1 = n.
Proof.
  induction n as [| n']; cbn; intros.
    inversion H. reflexivity.
    destruct l1 as [| h t]; cbn in *.
      destruct l2; cbn in H.
        inversion H.
        destruct (split n' l2).
          destruct p. 1-2: inversion H.
      case_eq (split n' (t ++ l2)).
        intros [l1' l2'] Heq. eapply f_equal, IHn'.
          rewrite Heq in H. inversion H; subst. eassumption.
        intro. rewrite H0 in H. inversion H.
Qed.

Lemma split_spec :
  forall (A : Type) (n : nat) (l l1 l2 : list A),
    split n l = Some (l1, l2) -> l = l1 ++ l2.
Proof.
  induction n as [| n']; cbn; intros.
    inversion H. cbn. reflexivity.
    destruct l as [| h t]; cbn.
      inversion H.
      case_eq (split n' t).
        intros [l1' l2'] H'. rewrite H' in H. inversion H.
          cbn. f_equal. apply IHn'. inversion H; subst. assumption.
        intro. rewrite H0 in H. inversion H.
Qed.

Lemma rotn_app :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 = S n ->
      rotn n (l1 ++ l2) = rev l1 ++ rotn n l2.
Proof.
  intros A n l1 l2 h.
  rewrite rotn_eq, split_app; auto.
Qed.

Lemma rotn_involution :
  forall (A : Type) (n : nat) (l : list A),
    rotn n (rotn n l) = l.
Proof.
  intro. apply (rotn_ind A (fun n l r => rotn n r = l)); intros.
    rewrite rotn_eq, H. reflexivity.
    rewrite rotn_app, H0, rev_involutive.
      apply split_spec in H. rewrite H. reflexivity.
      rewrite rev_length. eapply split_length. rewrite <- H.
        f_equal. apply split_spec in H. rewrite H. reflexivity.
Qed.

End Zad6.

(** **** Zadanie 7 *)

Module Zad7.

Require Import Recdef.

Require Import List.
Import ListNotations.

Require Import Omega.

Function split
  {A : Type} (n : nat) (l : list A)
  : option (list A * list A) :=
match n, l with
    | 0, _ => Some ([], l)
    | S n', [] => None
    | S n', h :: t =>
        match split n' t with
            | None => None
            | Some (l1, l2) => Some (h :: l1, l2)
        end
end.

Lemma split_length_aux :
  forall (A : Type) (n : nat) (l l1 l2 : list A),
    split n l = Some (l1, l2) ->
      n = 0 \/ length l2 < length l.
Proof.
  intros. revert l1 l2 H.
  functional induction (split n l); inversion 1; subst.
    left. reflexivity.
    right. destruct (IHo _ _ e1).
      subst. cbn in e1. inversion e1; subst. cbn. omega.
      cbn. omega.
Qed.

Lemma split_length :
  forall (A : Type) (n : nat) (l l1 l2 : list A),
    split (S n) l = Some (l1, l2) -> length l2 < length l.
Proof.
  intros. destruct (split_length_aux A (S n) l l1 l2 H).
    inversion H0.
    assumption.
Qed.

Function rotn
  {A : Type} (n : nat) (l : list A) {measure length l} : list A :=
match split (S n) l with
    | None => l
    | Some (l1, l2) => rev l1 ++ rotn n l2
end.
Proof.
  intros A n l _ l1 l2 _ H.
  eapply split_length. eassumption.
Defined.

Arguments rotn {x} _ _.

Compute rotn 1 [1; 2; 3; 4; 5; 6; 7].

Lemma split_app :
  forall (A : Type) (n : nat) (l1 l2 : list A),
    length l1 = n -> split n (l1 ++ l2) = Some (l1, l2).
Proof.
  induction n as [| n']; cbn; intros.
    destruct l1; cbn.
      reflexivity.
      inversion H.
    destruct l1 as [| h t]; cbn.
      inversion H.
      rewrite IHn'.
        reflexivity.
        cbn in H. inversion H. reflexivity.
Qed.

Lemma split_length' :
  forall {A : Type} {n : nat} {l1 l2 : list A},
    split n (l1 ++ l2) = Some (l1, l2) -> length l1 = n.
Proof.
  induction n as [| n']; cbn; intros.
    inversion H. reflexivity.
    destruct l1 as [| h t]; cbn in *.
      destruct l2; cbn in H.
        inversion H.
        destruct (split n' l2).
          destruct p. 1-2: inversion H.
      case_eq (split n' (t ++ l2)).
        intros [l1' l2'] Heq. eapply f_equal, IHn'.
          rewrite Heq in H. inversion H; subst. eassumption.
        intro. rewrite H0 in H. inversion H.
Qed.

Lemma split_spec :
  forall (A : Type) (n : nat) (l l1 l2 : list A),
    split n l = Some (l1, l2) -> l = l1 ++ l2.
Proof.
  intros A n l.
  functional induction (split n l); inversion 1; subst.
    reflexivity.
    cbn. f_equal. apply IHo. assumption.
Qed.

Lemma rotn_involution :
  forall (A : Type) (n : nat) (l : list A),
    rotn n (rotn n l) = l.
Proof.
  intros. functional induction (rotn n l).
    rewrite rotn_equation, e. reflexivity.
    rewrite rotn_equation, split_app, rev_involutive, IHl0.
      apply split_spec in e. rewrite e. reflexivity.
      rewrite rev_length. eapply split_length'.
        rewrite <- e. f_equal. apply split_spec in e. rewrite e. reflexivity.
Qed.

End Zad7.

(** **** Zadanie 8 *)

(** Z oczywistych względów nie ma. *)

(** **** Zadanie bonusowe *)

Module ZadBonusowe.

Require Import Arith.

Set Universe Polymorphism.

(** Lemat: aksjomat K dla liczb naturalnych. *)

Fixpoint code (n m : nat) : Type :=
match n, m with
    | 0, 0 => unit
    | S _, 0 => Empty_set
    | 0, S _ => Empty_set
    | S n', S m' => code n' m'
end.

Fixpoint encode_aux (n : nat) : code n n :=
match n with
    | 0 => tt
    | S n' => encode_aux n'
end.

Definition encode {n m : nat} (p : n = m) : code n m :=
match p with
    | eq_refl => encode_aux n
end.

Fixpoint decode {n m : nat} : code n m -> n = m :=
match n, m with
    | 0, 0 => fun _ => eq_refl
    | 0, S _ => fun c => match c with end
    | S _, 0 => fun c => match c with end
    | S n', S m' => fun c => @f_equal _ _ S _ _ (@decode n' m' c)
end.

Lemma decode_encode :
  forall (n m : nat) (p : n = m),
    decode (encode p) = p.
Proof.
  destruct p; cbn.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.

Lemma isProp_code :
  forall (n m : nat) (c1 c2 : code n m), c1 = c2.
Proof.
  induction n as [| n']; destruct m as [| m']; cbn; try destruct c1, c2.
    reflexivity.
    intros. apply IHn'.
Qed.

Lemma encode_decode :
  forall (n m : nat) (c : code n m),
    encode (decode c) = c.
Proof.
  induction n as [| n']; destruct m as [| m']; cbn; try destruct c.
    reflexivity.
    intro. apply isProp_code.
Qed.

Lemma K_nat :
  forall (n : nat) (p : n = n), p = eq_refl.
Proof.
  intros. rewrite <- (decode_encode _ _ p).
  replace (encode p) with (encode_aux n).
    induction n as [| n']; cbn.
      reflexivity.
      rewrite IHn'.
        cbn. reflexivity.
        reflexivity.
    apply isProp_code.
Qed.

Definition idtoeqv {A B : Type} (p : A = B) : A -> B.
Proof.
  destruct p. intro x. exact x.
Defined.

Lemma idtoeqv_sur :
  forall (A B : Type) (p : A = B) (b : B),
    exists a : A, idtoeqv p a = b.
Proof.
  destruct p. intro a. exists a. reflexivity.
Qed.

Definition wut
  (f : nat -> Type) (n : nat) (h : f n -> forall m : nat, f m -> bool)
  : forall k : nat, f k -> bool.
Proof.
  intros k x. destruct (Nat.eqb_spec n k).
    destruct e. exact (negb (h x n x)).
    exact true.
Defined.

Print idtoeqv.

Theorem nat_not_Type : ~ @eq Type nat Type.
Proof.
  intro p.
  pose (f := idtoeqv p). pose (idtoeqv_sur _ _ p).
  change (idtoeqv p) with f in e. clearbody f e.
  pose (A := forall n : nat, f n -> bool).
  destruct (e A) as [n q].
  pose (h := idtoeqv q). pose (e' := idtoeqv_sur _ _ q).
  change (idtoeqv q) with h in e'; clearbody h e'.
  destruct (e' (wut f n h)) as [x r]; unfold wut in r.
  apply (@f_equal _ _ (fun f => f n x)) in r.
  destruct (Nat.eqb_spec n n) as [s | s].
    rewrite (K_nat _ s) in r. destruct (h x n x); inversion r.
    contradiction.
Qed.

End ZadBonusowe.