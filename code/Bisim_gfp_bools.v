

CoFixpoint bools : Colist bool :=
  Cocons true (Cocons false bools).

Definition head {A : Type} (l : Colist A) : option A :=
match out l with
| ConilF => None
| CoconsF h _ => Some h
end.

Definition tail {A : Type} (l : Colist A) : option (Colist A) :=
match out l with
| ConilF => None
| CoconsF _ t => Some t
end.

Definition uncons {A : Type} (l : Colist A) : option (A * Colist A) :=
match out l with
| ConilF => None
| CoconsF h t => Some (h, t)
end.

Lemma wut :
  Bisim bools (Cocons true (Cocons false bools)).
Proof.
  do 2 (constructor; cbn); [done |].
  do 2 (constructor; cbn); [done |].
  apply Bisim_refl.
Restart.
  apply Bisim_gfp
  with (fun l1 l2 => out l1 = out l2); cbn; [| done].
  intros l1 l2 ->.
  by destruct (out l2) as [| h t]; cbn; constructor.
Qed.

Lemma wut' :
  forall l : Colist bool,
    tail bools = Some l ->
      Bisim (Cocons false bools) l.
Proof.
  intros l H.
  apply Bisim_gfp
    with (fun l1 l2 => out l1 = out l2); cycle 1.
  - by cbn in H; inversion H; subst.
  - intros l1 l2 ->.
    by destruct (out l2) as [| h t]; cbn; constructor.
Restart.
  constructor; cbn in *; inversion H; subst.
  constructor; [done |].
  by apply Bisim_refl.
Qed.

Lemma wut'' :
  Bisim (map negb bools) (Cocons false bools).
Proof.
  apply Bisim_gfp
    with (fun l1 l2 =>
      l1 = map negb bools /\ l2 = Cocons false bools \/
      l1 = map negb (Cocons false bools) /\ l2 = bools); cycle 1.
  - by left.
  - intros l1 l2 [[-> ->] | [-> ->]]; cbn in *; (constructor; [done |]).
    + by right.
    + by left.
Qed.

    destruct (out l1) eqn: Heql1, (out l2) eqn: Heql2.
    + by constructor.
    + by congruence.
    + by congruence.
    + constructor; [by congruence |].
      inversion H1; subst.
      destruct (out c) eqn: Heqc, (out c0) eqn: Heqc0.
      * by firstorder.
      * by firstorder congruence.
      * by firstorder congruence.
      * split; [done |].
        inversion HB.
        -- by split; [| repeat constructor].
        -- by split; [congruence |].
Qed.
      inversion H2; subst.
      destruct (out c1), (out c2); try congruence.
      
    inversion H1; inversion H2; subst.
    constructor; [done |]. cbn in *.
  intros l1 l2 [-> ->]; cbn.
  constructor; [done |].
  cbn.
Qed.

Lemma wut'' :
  forall l : Colist bool,
    tail bools = Some l ->
      Bisim (map negb bools) l.
Proof.
  cofix CH.
  constructor; cbn in *; inversion H; subst.
  constructor; [done |].
  constructor; cbn; constructor; [done |].
  by apply CH.
Restart.
  cbn; intros l [= <-].
  apply Bisim_gfp
    with (fun l1 l2 => exists l1' l2',
            l1 = Cocons false l1' /\ l2 = Cocons false l2' /\
              exists l1'' l2'', l1' = Cocons true l1'' /\ l2' = Cocons true l2''); cycle 1.
  - admit.
  - intros l1 l2 (l1' & l2' & -> & -> & l1'' & l2'' & -> & ->); cbn.
    constructor; [done |].
    do 2 eexists. split; [done |].
Qed.