(** * X8: Kolisty *)

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

(*
Inductive Finite {A : Type} : coList A -> Prop :=
    | Finite_nil : Finite {| uncons := None |}
    | Finite_cons :
        forall (h : A) (t : coList A),
          Finite t -> Finite {| uncons := Some (h, t) |}.
*)

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

CoFixpoint snoc {A : Type} (l : coList A) (x : A) : coList A :=
{|
    uncons :=
      match uncons l with
          | None => Some (x, conil)
          | Some (h, t) => Some (h, snoc t x)
      end;
|}.

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

CoFixpoint lapp {A : Type} (l1 l2 : coList A) : coList A :=
match uncons l1 with
    | None => l2
    | Some (h, t) => {| uncons := Some (h, lapp t l2) |}
end.

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

(*
Lemma Finite_snoc_not_sim :
  forall (A : Type) (l : coList A) (x : A),
    Finite l -> ~ sim (snoc l x) l.
Proof.
  induction 1; intro.
    inversion H. cbn in *. decompose [ex or and] sim'0; congruence.
    inversion H0. cbn in *. decompose [ex or and] sim'0; congruence.
Qed.
*)

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

Fixpoint tocoList {A : Type} (l : list A) : coList A :=
{|
    uncons :=
    match l with
        | [] => None
        | h :: t => Some (h, tocoList t)
    end
|}.

Lemma tocoList_inj :
  forall {A : Set} (l1 l2 : list A),
    tocoList l1 = tocoList l2 -> l1 = l2.
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

(*
CoFixpoint general_omega {A : Set} (l1 l2 : coList A) : coList A :=
match l1, l2 with
    | _, LNil => l1
    | LNil, LCons h' t' => LCons h' (general_omega t' l2)
    | LCons h t, _ => LCons h (general_omega t l2)
end.
*)

CoFixpoint lmap {A B : Type} (f : A -> B) (l : coList A) : coList B :=
{|
    uncons :=
    match uncons l with
        | None => None
        | Some (h, t) => Some (f h, lmap f t)
    end
|}.

Lemma empty_not_Infinite :
  forall A : Type, ~ Infinite {| uncons := @None (A * coList A) |}.
Proof.
  intros A []. cbn in p. inversion p.
Qed.

Lemma lmap_Infinite :
  forall (A B : Type) (f : A -> B) (l : coList A),
    Infinite l -> Infinite (lmap f l).
Proof.
  cofix CH.
  destruct 1. econstructor.
    cbn. rewrite p. reflexivity.
    apply CH. assumption.
Qed.

Lemma lapp_Infinite_l :
  forall (A : Type) (l1 l2 : coList A),
    Infinite l1 -> Infinite (lapp l1 l2).
Proof.
  cofix CH.
  destruct 1. econstructor.
    destruct l1; cbn in *; inversion p; cbn. reflexivity.
    apply CH. assumption.
Qed.

Lemma lapp_Infinite_r :
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

Lemma Finite_not_Infinite :
  forall (A : Type) (l : coList A),
    Finite l -> ~ Infinite l.
Proof.
  induction 1; intro.
    inversion H. cbn in p. inversion p.
    apply IHFinite. inversion H0; inversion p; subst. assumption.
Qed.

(*
Lemma Infinite_not_Finite :
  forall (A : Type) (l : coList A),
    Infinite l -> ~ Finite l.
Proof.
  induction 2.
    inversion H. inversion p.
    apply IHFinite. inversion H; inversion p; subst. assumption.
Qed.
*)

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