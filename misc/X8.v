(** * X8: Kolisty *)

Require Import List.
Import ListNotations.

CoInductive coList (A : Type) : Type :=
{
    uncons : option (A * coList A);
}.

Arguments uncons {A}.

CoInductive sim {A : Type} (l1 l2 : coList A) : Prop :=
{
    sim' :
      uncons l1 = None /\ uncons l2 = None \/
      exists (h1 : A) (t1 : coList A) (h2 : A) (t2 : coList A),
        uncons l1 = Some (h1, t1) /\
        uncons l2 = Some (h2, t2) /\
          h1 = h2 /\ sim t1 t2
}.

Hint Constructors sim.

Lemma sim_refl :
  forall (A : Type) (l : coList A), sim l l.
Proof.
  cofix CH.
  destruct l as [[[h t]|]].
    constructor. right. exists h, t, h, t; auto.
    constructor. left. cbn. split; reflexivity.
Qed.

Lemma sim_symm :
  forall (A : Type) (l1 l2 : coList A),
    sim l1 l2 -> sim l2 l1.
Proof.
  cofix CH.
  destruct 1 as [[[] | (h1 & t1 & h2 & t2 & p1 & p2 & p3 & H)]].
    constructor. left. split; assumption.
    constructor. right. exists h2, t2, h1, t1. auto.
Qed.

Lemma sim_trans :
  forall (A : Type) (l1 l2 l3 : coList A),
    sim l1 l2 -> sim l2 l3 -> sim l1 l3.
Proof.
  cofix CH.
  destruct 1 as [[[] | (h11 & t11 & h12 & t12 & p11 & p12 & p13 & H1)]],
           1 as [[[] | (h21 & t21 & h22 & t22 & p21 & p22 & p23 & H2)]];
  subst.
    auto.
    rewrite H0 in p21. inversion p21.
    rewrite H in p12. inversion p12.
    rewrite p12 in p21; inversion p21; subst.
      econstructor. right. exists h22, t11, h22, t22.
        do 3 try split; auto. eapply CH; eauto.
Qed.

Definition conil {A : Type} : coList A :=
{|
    uncons := None;
|}.

Definition cocons {A : Type} (h : A) (t : coList A) : coList A :=
{|
    uncons := Some (h, t);
|}.

Inductive Finite {A : Type} : coList A -> Prop :=
    | Finite_None :
        forall l : coList A, uncons l = None -> Finite l
    | Finite_Some :
        forall (h : A) (t l : coList A),
          uncons l = Some (h, t) -> Finite t -> Finite l.

CoInductive Infinite {A : Type} (l : coList A) : Prop :=
{
    h : A;
    t : coList A;
    p : uncons l = Some (h, t);
    inf' : Infinite t;
}.

Lemma Finite_not_Infinite :
  forall (A : Type) (l : coList A),
    Finite l -> Infinite l -> False.
Proof.
  induction 1; intro.
    destruct H0. congruence.
    apply IHFinite. destruct H1. congruence.
Qed.

CoFixpoint snoc {A : Type} (l : coList A) (x : A) : coList A :=
{|
    uncons :=
      match uncons l with
          | None => Some (x, conil)
          | Some (h, t) => Some (h, snoc t x)
      end;
|}.

Lemma Finite_snoc :
  forall (A : Type) (l : coList A) (x : A),
    Finite l -> Finite (snoc l x).
Proof.
  induction 1; cbn.
    apply (Finite_Some x conil).
      cbn. rewrite H. reflexivity.
      constructor. cbn. reflexivity.
    apply (Finite_Some h (snoc t x)).
      cbn. rewrite H. reflexivity.
      assumption.
Qed.

Lemma Infinite_snoc :
  forall (A : Type) (l : coList A) (x : A),
    Infinite l -> sim (snoc l x) l.
Proof.
  cofix CH.
  constructor. right. destruct H.
  exists h, (snoc t x), h, t.
  cbn. rewrite p. do 3 split.
    reflexivity.
    apply CH. assumption.
Qed.

(*
CoFixpoint rev {A : Type} (l : coList A) : coList A :=
{|
    uncons :=
      match uncons l with
          | None => None
          | Some (h, t) =>
              match uncons (rev t) with
                  | None => Some (h, conil)
                  | Some (h', t') => Some (h', cocons h t')
              end
      end
|}.
*)

Lemma sim_Infinite :
  forall (A : Type) (l1 l2 : coList A),
    sim l1 l2 -> Infinite l1 -> Infinite l2.
Proof.
  cofix CH.
  destruct 1 as [[[] | (h1 & t1 & h2 & t2 & p1 & p2 & p3 & H)]], 1.
    rewrite H in p. inversion p.
    econstructor.
      exact p2.
      rewrite p1 in p. inversion p; subst. eapply CH; eauto.
Qed.

CoFixpoint lapp {A : Type} (l1 l2 : coList A) : coList A :=
{|
    uncons :=
      match uncons l1 with
          | None => uncons l2
          | Some (h, t) => Some (h, lapp t l2)
      end
|}.

(*
CoFixpoint lapp {A : Type} (l1 l2 : coList A) : coList A :=
match uncons l1 with
    | None => l2
    | Some (h, t) => {| uncons := Some (h, lapp t l2) |}
end.
*)

Lemma Infinite_lapp_l :
  forall (A : Type) (l1 l2 : coList A),
    Infinite l1 -> Infinite (lapp l1 l2).
Proof.
  cofix CH.
  destruct 1. econstructor.
    destruct l1; cbn in *; inversion p; cbn. reflexivity.
    apply CH. assumption.
Qed.

Lemma Infinite_lapp_r :
  forall (A : Type) (l1 l2 : coList A),
    Infinite l2 -> Infinite (lapp l1 l2).
Proof.
  cofix CH.
  destruct l1 as [[[h t] |]]; intros.
    econstructor.
      cbn. reflexivity.
      apply CH. assumption.
    destruct H. econstructor.
      lazy. destruct l2; cbn in *. rewrite p. reflexivity.
      assumption.
Qed.

Lemma Finite_lapp :
  forall (A : Type) (l1 l2 : coList A),
    Finite l1 -> Finite l2 -> Finite (lapp l1 l2).
Proof.
  induction 1; cbn; intros.
    destruct H0.
      left. cbn. rewrite H. assumption.
      eright; eauto. cbn. rewrite H. exact H0.
    eright.
      cbn. rewrite H. reflexivity.
      apply IHFinite. assumption.
Qed.

Lemma Finite_lapp_conv :
  forall (A : Type) (l1 l2 : coList A),
    Finite (lapp l1 l2) -> Finite l1 \/ Finite l2.
Proof.
  intros. remember (lapp l1 l2) as l. revert l1 l2 Heql.
  induction H; intros; subst; cbn in *.
    destruct l1 as [[[h t]|]]; cbn in H.
      inversion H.
      left. constructor. cbn. reflexivity.
    destruct l1 as [[[h' t']|]]; cbn in H.
      inversion H; subst. destruct (IHFinite _ _ eq_refl).
        left. eright; eauto. cbn. reflexivity.
        right. assumption.
      left. constructor. cbn. reflexivity.
Qed.

CoFixpoint lmap {A B : Type} (f : A -> B) (l : coList A) : coList B :=
{|
    uncons :=
    match uncons l with
        | None => None
        | Some (h, t) => Some (f h, lmap f t)
    end
|}.

Lemma Finite_lmap :
  forall (A B : Type) (f : A -> B) (l : coList A),
    Finite l -> Finite (lmap f l).
Proof.
  induction 1.
    constructor. cbn. rewrite H. reflexivity.
    eright; eauto. cbn. rewrite H. reflexivity.
Qed.

Lemma Infinite_lmap :
  forall (A B : Type) (f : A -> B) (l : coList A),
    Infinite l -> Infinite (lmap f l).
Proof.
  cofix CH.
  destruct 1. econstructor.
    cbn. rewrite p. reflexivity.
    apply CH. assumption.
Qed.

Lemma lmap_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : coList A),
    sim (lmap g (lmap f l)) (lmap (fun x => g (f x)) l).
Proof.
  cofix CH.
  constructor. destruct l as [[[h t]|]]; [right | left]; cbn.
    exists (g (f h)), (lmap g (lmap f t)),
           (g (f h)), (lmap (fun x => g (f x)) t).
      repeat (split; [reflexivity | idtac]). apply CH.
    do 2 split.
Qed.

CoFixpoint iterate {A : Type} (f : A -> A) (x : A) : coList A :=
{|
    uncons := Some (x, iterate f (f x));
|}.

Lemma Infinite_iterate :
  forall (A : Type) (f : A -> A) (x : A),
    Infinite (iterate f x).
Proof.
  cofix CH.
  econstructor.
    cbn. reflexivity.
    apply CH.
Qed.

CoFixpoint piterate {A : Type} (f : A -> option A) (x : A) : coList A :=
{|
    uncons := Some (x,
      match f x with
          | None => conil
          | Some y => piterate f y
      end)
|}.

Lemma piterate_Finite :
  forall (A : Type) (f : A -> option A) (x : A),
    Finite (piterate f x) -> exists x : A, f x = None.
Proof.
  intros. remember (piterate f x) as l.
  revert f x Heql.
  induction H; intros; subst; cbn in *; inversion H; subst.
  clear H. case_eq (f h); intros; rewrite H in *.
    eapply IHFinite. reflexivity.
    exists h. assumption.
Qed.

(*
Require Import CoqBookPL.book.X7.

Fixpoint splitAt
  {A : Type} (l : coList A) (n : nat) : option (list A * A * coList A) :=
match n, uncons l with
    | _, None => None
    | 0, Some (h, t) => Some ([], h, t)
    | S n', Some (h, t) =>
        match splitAt t n' with
            | None => None
            | Some (start, mid, rest) => Some (h :: start, mid, rest)
        end
end.

CoFixpoint fromStream {A : Type} (s : Stream A) : coList A :=
{|
    uncons := Some (hd s, fromStream (tl s));
|}.

Lemma Infinite_splitAt :
  forall (A : Type) (n : nat) (l : coList A),
    Infinite l ->
      exists (start : list A) (mid : A) (rest : coList A),
        splitAt l n = Some (start, mid, rest).
Proof.
  induction n as [| n']; cbn; intros.
    destruct H. rewrite p. exists [], h, t. reflexivity.
    destruct l as [[[h t] |]].
      destruct H. destruct (IHn' _ H) as (start & mid & rest & spec).
        exists (h :: start), mid, rest. cbn. inversion p. rewrite spec.
        reflexivity.
      inversion H. inversion p.
Qed.
*)

(** TODO: modyfikacje *)

(*
CoFixpoint takeWhile {A : Type} (f : A -> bool) (l : coList A) : coList A :=
{|
    uncons :=
      match uncons l with
          | None => None
          | Some (h, t) =>
              if f h then Some (h, takeWhile f t) else takeWhile f t
      end;
|}.
*)

CoFixpoint scan
  {A B : Type} (l : coList A) (f : B -> A -> B) (b : B) : coList B :=
{|
    uncons :=
      match uncons l with
          | None => None
          | Some (h, t) => Some (b, scan t f (f b h))
      end;
|}.

CoFixpoint intersperse {A : Type} (x : A) (l : coList A) : coList A :=
{|
    uncons :=
      match uncons l with
          | None => None
          | Some (h, t) =>
              match uncons t with
                  | None => Some (h, t)
                  | Some (h', t') => Some (h, cocons x (intersperse x t))
              end
      end;
|}.

(** TODO: zip, unzip *)

(*
CoFixpoint join {A : Type} (l : coList (coList A)) : coList A :=
      match uncons l with
          | None => conil
          | Some (h, t) => lapp h (join t)
      end.
*)

CoInductive Rev {A : Type} (l r : coList A) : Prop :=
{
    Revc :
      (uncons l = None /\ uncons r = None)
      \/
      exists (h : A) (tl tr : coList A),
        uncons l = Some (h, tl) /\ r = snoc tr h /\ Rev tl tr
}.

Axiom sim_eq :
  forall (A : Type) (l1 l2 : coList A), sim l1 l2 -> l1 = l2.

Lemma Rev_wut :
  forall (A : Type) (l r : coList A),
    Infinite l -> Infinite r -> Rev l r.
Proof.
  cofix CH.
  constructor. right. destruct H, H0.
  exists h, t, r. split.
    assumption.
    split.
      Focus 2. apply CH; auto; econstructor; eauto.
      apply sim_eq. apply sim_symm. apply Infinite_snoc. econstructor; eauto.
Qed.

Lemma Rev_Finite :
  forall (A : Type) (l r : coList A),
    Rev l r -> Finite r -> Finite l.
Proof.
  intros A l r HRev H. revert l HRev.
  induction H; intros.
    destruct HRev. decompose [ex or and] Revc0; clear Revc0.
      left. assumption.
      subst. cbn in H. destruct (uncons x1) as [[]|]; inversion H.
    destruct HRev. decompose [ex or and] Revc0; clear Revc0.
      congruence.
      subst. apply IHFinite. cbn in H. constructor. right.
        destruct (uncons x1) as [[]|].
          Focus 2. inversion H; subst. exists h, x0, x1. split.
Abort.

Lemma Rev_Finite :
  forall (A : Type) (l r : coList A),
    Rev l r -> Finite l -> Finite r.
Proof.
  intros A l r HRev H. revert r HRev.
  induction H; intros.
    destruct HRev. decompose [ex or and] Revc0; clear Revc0.
      left. assumption.
      subst. cbn in *. inversion H.

Abort.

Lemma Infinite_Rev :
  forall (A : Type) (l r : coList A),
    Rev l r -> Infinite l -> Infinite r.
Proof.
  cofix CH.
  destruct 1. decompose [ex or and] Revc0; clear Revc0.
    destruct 1. congruence.
    intro. subst. destruct x1 as [[[h t] |]]; cbn.
      econstructor.
        cbn. reflexivity.
        apply (CH _ (cocons x t)).
          constructor. cbn. right. exists x, t, t. auto.
      congruence.
      subst. cbn in *. inversion p; subst.
Abort.

Inductive Rev {A : Type} : coList A -> coList A -> Prop :=
    | Rev_conil : Rev conil conil
    | Rev_cocons :
        forall (x : A) (l1 l2 : coList A),
          Rev l1 l2 -> Rev (cocons x l1) (snoc l2 x).

Hint Constructors Rev.

Lemma Finite_cocons :
  forall (A : Type) (x : A) (l : coList A),
    Finite l -> Finite (cocons x l).
Proof.
  intros. apply (Finite_Some x l); auto.
Qed.

Lemma Rev_Finite :
  forall (A : Type) (l1 l2 : coList A),
    Rev l1 l2 -> Finite l1 /\ Finite l2.
Proof.
  induction 1.
    do 3 constructor.
    destruct IHRev. split.
      apply Finite_cocons. assumption.
      apply Finite_snoc. assumption.
Qed.

(*
CoInductive Rev' {A : Type} (l r : coList A) : Prop :=
{
    spec : sim l (
}.
*)

Fixpoint fromList {A : Type} (l : list A) : coList A :=
{|
    uncons :=
    match l with
        | [] => None
        | h :: t => Some (h, fromList t)
    end
|}.

Lemma fromList_inj  :
  forall {A : Set} (l1 l2 : list A),
    fromList l1 = fromList l2 -> l1 = l2.
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; inversion 1.
    reflexivity.
    f_equal. apply IHt1. assumption.
Defined.

CoFixpoint from (n : nat) : coList nat :=
{|
    uncons := Some (n, from (S n));
|}.

Definition lhead {A : Type} (l : coList A) : option A :=
match uncons l with
    | Some (a, _) => Some a
    | _ => None
end.

Definition ltail {A : Type} (l : coList A) : option (coList A) :=
match uncons l with
    | Some (_, t) => Some t
    | _ => None
end.

Fixpoint lnth {A : Type} (n : nat) (l : coList A) : option A :=
match n, uncons l with
    | _, None => None
    | 0, Some (x, _) => Some x
    | S n', Some (_, l') => lnth n' l'
end.

Eval compute in lnth 511 (from 0).

Definition nats := from 0.

CoFixpoint repeat {A : Type} (x : A) : coList A :=
{|
    uncons := Some (x, repeat x);
|}.

Eval simpl in lnth 123 (repeat 5).

Lemma empty_not_Infinite :
  forall A : Type, ~ Infinite {| uncons := @None (A * coList A) |}.
Proof.
  intros A []. cbn in p. inversion p.
Qed.