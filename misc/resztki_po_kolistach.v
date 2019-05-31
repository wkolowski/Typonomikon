


CoInductive Rev {A : Type} (l r : coList A) : Prop :=
{
    Rev' :
      (uncons l = None /\ uncons r = None)
      \/
      exists (h : A) (tl tr : coList A),
        uncons l = Some (h, tl) /\ r = snoc tr h /\ Rev tl tr
}.

Lemma Rev_wut :
  forall (A : Type) (l r : coList A),
    Infinite l -> Infinite r -> Rev l r.
(* begin hide *)
Proof.
  cofix CH.
  constructor. right. destruct H, H0.
  exists h, t, r. split.
    assumption.
    split.
      Focus 2. apply CH; auto; econstructor; eauto.
      apply eq_lsim. apply lsim_symm. apply Infinite_snoc. econstructor; eauto.
Qed.
(* end hide *)

Lemma Rev_Finite :
  forall (A : Type) (l r : coList A),
    Rev l r -> Finite r -> Finite l.
(* begin hide *)
Proof.
  intros A l r HRev H. revert l HRev.
  induction H as [r H | h t r' H IH]; intros.
    destruct HRev as [[[H1 H2] | (h & tl & tr & H1 & H2 & H3)]].
      left. assumption.
      subst. cbn in H. destruct (uncons tr) as [[]|]; inv H.
    destruct HRev as [[[H1 H2] | (h' & tl & tr & H1 & H2 & H3)]].
      congruence.
      subst.
Abort.
(* end hide *)

Lemma Rev_Finite :
  forall (A : Type) (l r : coList A),
    Rev l r -> Finite l -> Finite r.
(* begin hide *)
Proof.
  intros A l r HRev H. revert r HRev.
  induction H; intros.
    destruct HRev as [[[H1 H2] | (h & tl & tr & H1 & H2 & H3)]].
      left. assumption.
      subst. congruence.
    destruct HRev as [[[H1 H2] | (h' & tl & tr & H1 & H2 & H3)]].
      congruence.
      subst. rewrite H1 in H. inv H. apply Finite_snoc, IHFinite.
        assumption.
Qed.
(* end hide *)

Lemma Infinite_Rev :
  forall (A : Type) (l r : coList A),
    Rev l r -> Infinite l -> Infinite r.
(* begin hide *)
Proof.
  cofix CH.
  destruct 1. (* decompose [ex or and] Revc0; clear Revc0.
    destruct 1. congruence.
    intro. subst. destruct x1 as [[[h t] |]]; cbn.
      econstructor.
        cbn. reflexivity.
        apply (CH _ (cocons x t)).
          constructor. cbn. right. exists x, t, t. auto.
      congruence.
      subst. cbn in *. inversion p; subst. *)
Abort.
(* end hide *)

Lemma Finite_cocons :
  forall (A : Type) (x : A) (l : coList A),
    Finite l -> Finite (cocons x l).
(* begin hide *)
Proof.
  intros. apply (Finite_Some x l); auto.
Qed.
(* end hide *)

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
(* begin hide *)
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