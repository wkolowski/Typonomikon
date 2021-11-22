CoInductive Conat : Type :=
| z : Conat
| s : Conat -> Conat.

CoFixpoint add (n m : Conat) : Conat :=
match n, m with
    | z, _ => m
    | _, z => n
    | s n', s m' => s (s (add n' m'))
end.

CoInductive sim : Conat -> Conat -> Prop :=
    | simz : sim z z
    | sims : forall n m : Conat, sim n m -> sim (s n) (s m).

Definition out (n : Conat) : Conat :=
match n with
    | z    => z
    | s n' => s n'
end.

Lemma out' :
  forall n : Conat, n = out n.
Proof.
  destruct n as [| n']; cbn; reflexivity.
Defined.

Lemma add_z_l :
  forall n : Conat, add z n = n.
Proof.
  intros. rewrite (out' (add z n)).
  destruct n as [| n']; cbn; reflexivity.
Defined.

Lemma add_z_r :
  forall n : Conat, add n z = n.
Proof.
  intros. rewrite (out' (add n z)).
  destruct n as [| n']; cbn; reflexivity.
Qed.

Lemma add_s_R :
  forall n m : Conat, add n (s m) = s (add n m).
Proof.
  intros. rewrite (out' (add n (s m))).
  destruct n as [| n']; cbn.
    admit.
Abort.

Lemma add_s_l :
  forall n m : Conat, add (s n) m = s (add n m).
Proof.
  intros. rewrite (out' (add (s n) m)).
  destruct m as [| m']; cbn.
    rewrite add_z_r. reflexivity.
Abort.

Lemma add_comm :
  forall n m : Conat, sim (add n m) (add m n).
Proof.
  cofix CH.
  destruct n as [| n'], m as [| m'].
    rewrite add_z_r. constructor.
    rewrite add_z_l, add_z_r. admit.
    rewrite add_z_l, add_z_r. admit.
Abort.