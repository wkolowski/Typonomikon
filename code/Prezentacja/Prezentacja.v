(** * Koindukcja (negatywna, czyli lepsza) *)

(** ** Strumienie *)

CoInductive Stream (A : Type) : Type :=
{
    hd : A;
    tl : Stream A;
}.

Arguments hd {A}.
Arguments tl {A}.

CoFixpoint from' (n : nat) : Stream nat :=
{|
    hd := n;
    tl := from' (S n);
|}.

CoInductive bisim {A : Type} (s1 s2 : Stream A) : Prop :=
{
    hds : hd s1 = hd s2;
    tls : bisim (tl s1) (tl s2);
}.

Lemma bisim_refl :
  forall (A : Type) (s : Stream A), bisim s s.
Proof.
  cofix CH. constructor; auto.
Qed.

Lemma bisim_sym :
  forall (A : Type) (s1 s2 : Stream A),
    bisim s1 s2 -> bisim s2 s1.
Proof.
  cofix CH.
  destruct 1 as [hds tls]. constructor; auto.
Qed.

Lemma bisim_trans :
  forall (A : Type) (s1 s2 s3 : Stream A),
    bisim s1 s2 -> bisim s2 s3 -> bisim s1 s3.
Proof.
  cofix CH.
  destruct 1 as [hds1 tls1], 1 as [hds2 tls2].
  constructor; eauto. rewrite hds1. assumption.
Qed.

CoFixpoint evens {A : Type} (s : Stream A) : Stream A :=
{|
    hd := hd s;
    tl := evens (tl (tl s));
|}.

(** Na tablicy można pisać za pomocą (ko?)równań.

    hd (evens s) := hd s;
    tl (evens s) := evens (tl (tl s));

*)

CoFixpoint odds {A : Type} (s : Stream A) : Stream A :=
{|
    hd := hd (tl s);
    tl := odds (tl (tl s));
|}.

Definition split {A : Type} (s : Stream A)
  : Stream A * Stream A := (evens s, odds s).

CoFixpoint merge
  {A : Type} (ss : Stream A * Stream A) : Stream A :=
{|
    hd := hd (fst ss);
    tl := merge (snd ss, tl (fst ss));
|}.

Lemma merge_split :
  forall (A : Type) (s : Stream A),
    bisim (merge (split s)) s.
Proof.
  cofix CH.
  intros. constructor.
    cbn. reflexivity.
    cbn. constructor.
      cbn. reflexivity.
      cbn. apply CH.
Qed.

(** ** Kolisty *)

CoInductive LList (A : Type) : Type :=
{
    uncons : option (A * LList A);
}.

Arguments uncons {A}.

Definition lnil {A : Type} : LList A := {| uncons := None |}.

Definition lcons {A : Type} (x : A) (l : LList A) : LList A :=
  {| uncons := Some (x, l); |}.

CoFixpoint from (n : nat) : LList nat :=
  lcons n (from (S n)).

Inductive Finite {A : Type} : LList A -> Prop :=
    | Finite_nil : Finite lnil
    | Finite_cons :
        forall (h : A) (t : LList A),
          Finite t -> Finite (lcons h t).

CoInductive Infinite {A : Type} (l : LList A) : Prop :=
{
    h : A;
    t : LList A;
    p : uncons l = Some (h, t);
    inf' : Infinite t;
}.