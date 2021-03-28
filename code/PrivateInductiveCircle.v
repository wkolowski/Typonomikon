Definition ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
match p with
    | eq_refl => eq_refl
end.

Definition transport {A : Type} {P : A -> Type} {x y : A} (p : x = y) : P x -> P y :=
match p with
    | eq_refl => fun x => x
end.

Definition apd
  {A : Type} {B : A -> Type}
  (f : forall x : A, B x) {x y : A} (p : x = y) : transport p (f x) = f y :=
match p with
    | eq_refl => eq_refl
end.

Definition pinv {A : Type} {x y : A} (p : x = y) : y = x :=
match p with
    | eq_refl => eq_refl
end.

Definition pcat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
match p, q with
    | eq_refl, eq_refl => eq_refl
end.

Lemma transport_of_refl :
  forall {A : Type} {x y : A} (p : x = y),
    @transport A (eq x) _ _ p eq_refl = p.
Proof.
  destruct p. cbn. reflexivity.
Defined.

Lemma transport_const :
  forall {A B : Type} {x y : A} (p : x = y) (b : B),
    @transport A (fun _ => B) _ _ p b = b.
Proof.
  destruct p. cbn. reflexivity.
Defined.

Lemma transport_eq_l :
  forall {A : Type} {x y : A} (p : x = y) (l : A) (lx : l = x),
    @transport _ (fun r => l = r) _ _ p lx = pcat lx p.
Proof.
  destruct p, lx. cbn. reflexivity.
Defined.

Lemma transport_comp :
  forall {A B : Type} (f g : A -> B) {x y : A} (p : x = y) (q : f x = g x),
    @transport _ (fun x => f x = g x) _ _ p q
      =
    pcat (pinv (ap f p)) (pcat q (ap g p)).
Proof.
Admitted.

Module Interval.

Private Inductive I : Type :=
    | i0 : I
    | i1 : I.

Axiom seg : i0 = i1.

Definition I_rec {P : Type} (p0 p1 : P) (p : p0 = p1) (i : I) : P :=
match i with
    | i0 => p0
    | i1 => p1
end.

Axiom I_rec_seg :
  forall {P : Type} (p0 p1 : P) (p : p0 = p1),
    ap (I_rec p0 p1 p) seg = p.

Definition I_ind
  {P : I -> Type} (p0 : P i0) (p1 : P i1) (p : transport seg p0 = p1) (i : I) : P i :=
match i with
    | i0 => p0
    | i1 => p1
end.

Axiom I_ind_seg :
  forall {P : I -> Type} (p0 : P i0) (p1 : P i1) (p : transport seg p0 = p1) (i : I),
    apd (I_ind p0 p1 p) seg = p.

End Interval.

Module Circle.

Private Inductive Circle : Type :=
    | base : Circle.

Axiom loop : base = base.

Definition Circle_rec
  {P : Type} (b : P) (l : b = b) : Circle -> P :=
    fun c : Circle => b.

Axiom Circle_rec_loop :
  forall {P : Type} (b : P) (l : b = b),
    ap (Circle_rec b l) loop = l.

Definition Circle_ind
  {P : Circle -> Type}
  (b : P base) (l : transport loop b = b)
  (c : Circle) : P c :=
match c with
    | base => b
end.

Axiom Circle_ind_loop :
  forall {P : Circle -> Type} (b : P base) (l : transport loop b = b) (c : Circle),
    apd (Circle_ind b l) loop = l.

End Circle.

Module WeirdCircle.

Private Inductive WeirdCircle : Type :=
    | N : WeirdCircle
    | S : WeirdCircle.

Axiom NS : N = S.
Axiom SN : S = N.

Definition WeirdCircle_rec
  {P : Type} (n s : P) (ns : n = s) (sn : s = n) (c : WeirdCircle) : P :=
match c with
    | N => n
    | S => s
end.

Axiom WeirdCircle_rec_NS :
  forall {P : Type} (n s : P) (ns : n = s) (sn : s = n) (c : WeirdCircle),
    ap (WeirdCircle_rec n s ns sn) NS = ns.

Axiom WeirdCircle_rec_SN :
  forall {P : Type} (n s : P) (ns : n = s) (sn : s = n) (c : WeirdCircle),
    ap (WeirdCircle_rec n s ns sn) SN = sn.

Definition WeirdCircle_ind
  {P : WeirdCircle -> Type}
  (n : P N) (s : P S)
  (ns : transport NS n = s) (sn : transport SN s = n)
  (c : WeirdCircle) : P c :=
match c with
    | N => n
    | S => s
end.

Axiom WeirdCircle_ind_NS :
  forall
    {P : WeirdCircle -> Type} (n : P N) (s : P S)
    (ns : transport NS n = s) (sn : transport SN s = n)
    (c : WeirdCircle),
      apd (WeirdCircle_ind n s ns sn) NS = ns.

Axiom WeirdCircle_ind_SN :
  forall
    {P : WeirdCircle -> Type} (n : P N) (s : P S)
    (ns : transport NS n = s) (sn : transport SN s = n)
    (c : WeirdCircle),
      apd (WeirdCircle_ind n s ns sn) SN = sn.

End WeirdCircle.

Import Circle WeirdCircle.

Definition cw (c : Circle) : WeirdCircle :=
  Circle_rec N (pcat NS SN) c.

Definition wc (w : WeirdCircle) : Circle :=
  WeirdCircle_rec base base loop loop w.

Lemma cw_wc :
  forall c : Circle,
    wc (cw c) = c.
Proof.
  Check @Circle_ind (fun c => wc (cw c) = c) eq_refl.
  eapply Circle_ind. Unshelve.
  all: cycle 1; cbn.
    exact loop.
Abort.

Lemma wc_cw :
  forall c : WeirdCircle,
    cw (wc c) = c.
Proof.
  eapply WeirdCircle_ind. Unshelve. all: cycle 2; cbn.
    compute. reflexivity.
    compute. exact NS.
    rewrite transport_comp.
Abort.