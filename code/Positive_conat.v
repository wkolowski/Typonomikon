Require Import Setoid SetoidClass.

CoInductive conat : Type :=
| Z : conat
| S : conat -> conat.

CoInductive sim : conat -> conat -> Prop :=
| sim_Z : sim Z Z
| sim_S : forall {n m : conat}, sim n m -> sim (S n) (S m).

Lemma sim_refl :
  forall n : conat,
    sim n n.
Proof.
  cofix CH.
  intros [| n']; constructor.
  apply CH.
Qed.

CoFixpoint add (n m : conat) : conat :=
match n with
| Z => m
| S n' => S (add n' m)
end.

Lemma unfold_conat :
  forall n : conat,
    n =
    match n with
    | Z => Z
    | S n' => S n'
    end.
Proof.
  now intros [| n'].
Qed.

Lemma add_Z_l :
  forall n : conat,
    add Z n = n.
Proof.
  intros.
  rewrite (unfold_conat _); cbn.
  now destruct n.
Qed.

Lemma add_Z_r :
  forall n : conat,
    sim (add n Z) n.
Proof.
  cofix CH.
  intros [| n'].
  - rewrite add_Z_l.
    constructor.
  - rewrite (unfold_conat (add _ _)); cbn.
    constructor.
    apply CH.
Qed.

Lemma sim_add :
  forall n1 n2 m1 m2 : conat,
    sim n1 n2 -> sim m1 m2 -> sim (add n1 m1) (add n2 m2).
Proof.
  cofix CH.
  intros * [] [].
  - rewrite add_Z_l.
    apply sim_refl.
  - rewrite !add_Z_l.
    now constructor.
  - rewrite (unfold_conat (add (S _) _)); cbn.
    rewrite (unfold_conat (add (S _) _)); cbn.
    constructor.
    now apply CH; [| apply sim_refl].
  - rewrite (unfold_conat (add (S _) _)); cbn.
    rewrite (unfold_conat (add (S _) _)); cbn.
    constructor.
    now apply CH; [| constructor].
Qed.

#[export]
Instance Proper_add :
  Proper (sim ==> sim ==> sim) add.
Proof.
  now repeat red; intros; apply sim_add.
Qed.

#[export]
Instance Proper_S :
  Proper (sim ==> sim) S.
Proof.
  now intros n m []; repeat constructor.
Qed.

Lemma add_S_l :
  forall n m : conat,
    sim (add (S n) m) (S (add n m)).
Proof.
  intros.
  rewrite (unfold_conat (add _ _)); cbn.
  apply sim_refl.
Qed.

Lemma add_S_r :
  forall n m : conat,
    sim (add n (S m)) (S (add n m)).
Proof.
  cofix CH.
  intros [| n'] m.
  - rewrite !add_Z_l.
    apply sim_refl.
  - rewrite (unfold_conat (add _ _)); cbn.
    rewrite (unfold_conat (add (S _) _)); cbn.
    constructor.
    apply CH.
Qed.

Lemma add_comm :
  forall n m : conat,
    sim (add n m) (add m n).
Proof.
  cofix CH.
  intros [| n'] m.
  - rewrite (unfold_conat (add Z _)); simpl.
    admit.
  -
Abort.

CoFixpoint add' (n m : conat) : conat :=
match n, m with
| Z   , _    => m
| _   , Z    => n
| S n', S m' => S (S (add' n' m'))
end.

CoFixpoint add'' (n m : conat) : conat :=
match n with
| Z    => m
| S n' => S
  match m with
  | Z    => Z
  | S m' => S (add'' n' m')
  end
end.

Lemma add'_comm :
  forall n m : conat,
    sim (add' n m) (add' m n).
Proof.
  cofix CH.
  intros [| n'] [| m'].
  - rewrite (unfold_conat (add' _ _)); cbn.
    constructor.
  - rewrite (unfold_conat (add' Z _)); cbn.
    rewrite (unfold_conat (add' _ Z)); cbn.
    constructor.
    admit.
  - rewrite (unfold_conat (add' Z _)); cbn.
    rewrite (unfold_conat (add' _ Z)); cbn.
    constructor.
    admit.
  - rewrite (unfold_conat (add' (S _) _)); cbn.
    rewrite (unfold_conat (add' _ (S _))); cbn.
    do 2 constructor.
    apply CH.
Admitted.

Lemma add'_Z_l :
  forall n : conat,
    add' Z n = n.
Proof.
  intros.
  rewrite (unfold_conat (add' _ _)); cbn.
  now destruct n.
Qed.

Lemma add'_Z_r :
  forall n : conat,
    add' n Z = n.
Proof.
  intros.
  rewrite (unfold_conat (add' _ _)); cbn.
  now destruct n.
Qed.

Lemma add'_SS :
  forall n m : conat,
    add' (S n) (S m) = S (S (add' n m)).
Proof.
  now intros; rewrite (unfold_conat (add' _ _)); cbn.
Qed.

Require Import Setoid.

Lemma add'_S_l :
  forall n m : conat,
    sim (add' (S n) m) (S (add' n m)).
Proof.
  intros n [| m']; cbn.
  - admit.
  - rewrite (unfold_conat (add' _ _)). cbn.
    constructor.
    cut (sim (S (add' n m')) (add' (S m') n)).
    + admit.
    + rewrite (unfold_conat (add' (S m') n)). cbn.
Abort.

Lemma add''_S_l :
  forall n m : conat,
    add'' (S n) m = S (add'' n m).
Proof.
  intros.
  rewrite (unfold_conat (add'' _ _)); cbn.
Admitted.

Lemma add'_assoc :
  forall a b c : conat,
    sim (add' (add' a b) c) (add' a (add' b c)).
Proof.
  cofix CH.
  intros [| a'] [| b'] [| c'];
    rewrite ?add'_Z_l, ?add'_Z_r, ?add'_SS; repeat constructor.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  -
Admitted.