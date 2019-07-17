(** Przyjaźnie wyglądające uniwersum, które jednak podstępnie masakruje
    zbłąkanych wędrowców. Jak zawsze ciężko nazwać ten paradoks. Chyba
    najprościej powiedzieć, że jest to jednocześnie paradoks Russela i
    Girarda. Ciekawe, że udało mi się to wycisnąć z rozważań nad
    indukcją-rekursją oraz ścisłą pozytywnością. *)

Module Uniwersum.

Axioms
  (U : Type)
  (El : U -> Type)

  (Empty : U)
  (Unit : U)
  (Nat : U)
  (Pi : forall (A : U) (B : El A -> U), U)
  (Sigma : forall (A : U) (B : El A -> U), U)
  (UU : U)

  (El_Empty : El Empty = Empty_set)
  (El_Unit : El Unit = unit)
  (El_Nat : El Nat = nat)
  (El_Pi :
    forall (A : U) (B : El A -> U),
      El (Pi A B) = forall (x : El A), El (B x))
  (El_Sigma :
    forall (A : U) (B : El A -> U),
      El (Pi A B) = {x : El A & El (B x)})
  (El_UU : El UU = U)

  (ind : forall
    (P : U -> Type)
    (PEmpty : P Empty)
    (PUnit : P Unit)
    (PNat : P Nat)
    (PPi :
      forall (A : U) (B : El A -> U),
        P A -> (forall x : El A, P (B x)) -> P (Pi A B))
    (PSigma :
      forall (A : U) (B : El A -> U),
        P A -> (forall x : El A, P (B x)) -> P (Sigma A B))
    (PUU : P UU),
      {f : forall A : U, P A |
        (f Empty = PEmpty) /\
        (f Unit = PUnit) /\
        (f Nat = PNat) /\
        (forall (A : U) (B : El A -> U),
          f (Pi A B) =
          PPi A B (f A) (fun x : El A => f (B x))) /\
        (forall (A : U) (B : El A -> U),
          f (Sigma A B) =
          PSigma A B (f A) (fun x : El A => f (B x))) /\
        (f UU = PUU)
      }).

(** Czyżby sprzeczność? *)

Definition bad : U -> (U -> U).
Proof.
  apply (ind (fun _ => U -> U)).
    1-3,6: exact (fun u : U => u).
    intros A B _ _. revert A B.
      apply (ind (fun A : U => (El A -> U) -> (U -> U))).
        1-5: intros; assumption.
        intro f. rewrite El_UU in f. exact f.
    intros. assumption.
Defined.

Lemma homotopiczny_czarodziej :
  forall (A : Type) (P : A -> Type) (x y : A) (p : x = y) (u : P y),
    eq_rect x P (@eq_rect_r A y P u x p) y p = u.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Lemma bad_sur :
  forall f : U -> U, exists u : U, f = bad u.
Proof.
  intro. unfold bad.
  destruct (ind _) as [g H]; decompose [and] H; clear H.
  destruct (ind _) as [h H']; decompose [and] H'; clear H'.
  pose (f' := eq_rect_r (fun T : Type => T -> U) f El_UU).
  exists (Pi UU f').
  rewrite H3. rewrite H11.
  unfold f'. rewrite homotopiczny_czarodziej. reflexivity.
Qed.

Definition change : U -> U.
Proof.
  apply ind.
    exact Nat.
    all: intros; exact Empty.
Defined.

Definition help : U -> nat.
Proof.
  apply ind.
    exact 0.
    exact 1.
    exact 2.
    intros. exact 3.
    intros. exact 4.
    exact 5.
Defined.

Ltac help H :=
  apply (f_equal help) in H;
  cbn in H; unfold help in H;
  destruct (ind _) as [help Hhelp];
  decompose [and] Hhelp; clear Hhelp;
  congruence.

Lemma change_neq :
  forall u : U, change u <> u.
Proof.
  apply ind; unfold change;
  destruct (ind _) as [f H]; decompose [and] H; clear H;
  intros; try help H; help H6.
Qed.

Definition Russel_Girard : False.
Proof.
  destruct (bad_sur (fun u : U => change (bad u u))).
  unfold bad in H. destruct (ind _).
  apply (f_equal (fun f => f x)) in H.
  apply (change_neq (x0 x x)).
  assumption.
Qed.

End Uniwersum.

Module Russel_Girard.

(* Uproszczona wersja paradoksu - tylko U i Pi. *)

Axioms
  (U : Type)
  (El : U -> Type)

  (Pi : forall (A : U) (B : El A -> U), U)
  (UU : U)

  (El_Pi :
    forall (A : U) (B : El A -> U),
      El (Pi A B) = forall (x : El A), El (B x))
  (El_UU : El UU = U)

  (ind : forall
    (P : U -> Type)
    (PPi :
      forall (A : U) (B : El A -> U),
        P A -> (forall x : El A, P (B x)) -> P (Pi A B))
    (PUU : P UU),
      {f : forall A : U, P A |
        (forall (A : U) (B : El A -> U),
          f (Pi A B) =
          PPi A B (f A) (fun x : El A => f (B x))) /\
        (f UU = PUU)
      }).

Definition bad : U -> (U -> U).
Proof.
  apply (ind (fun _ => U -> U)).
    intros A B _ _. revert A B.
      apply (ind (fun A : U => (El A -> U) -> (U -> U))).
        intros; assumption.
        intro f. rewrite El_UU in f. exact f.
    exact (fun u => u).
Defined.

Lemma homotopiczny_czarodziej :
  forall (A : Type) (P : A -> Type) (x y : A) (p : x = y) (u : P y),
    eq_rect x P (@eq_rect_r A y P u x p) y p = u.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Lemma bad_sur :
  forall f : U -> U, exists u : U, f = bad u.
Proof.
  intro. unfold bad.
  destruct (ind _) as [g H]; decompose [and] H; clear H.
  destruct (ind _) as [h H']; decompose [and] H'; clear H'.
  pose (f' := eq_rect_r (fun T : Type => T -> U) f El_UU).
  exists (Pi UU f').
  rewrite H0. rewrite H2.
  unfold f'. rewrite homotopiczny_czarodziej. reflexivity.
Qed.

Definition change : U -> U.
Proof.
  apply ind.
    intros. exact UU.
    exact (Pi UU (fun _ => UU)).
Defined.

Definition help : U -> bool.
Proof.
  apply ind.
    intros. exact true.
    exact false.
Defined.

Ltac help H :=
  apply (f_equal help) in H;
  cbn in H; unfold help in H;
  destruct (ind _) as [help Hhelp];
  decompose [and] Hhelp; clear Hhelp;
  congruence.

Lemma change_neq :
  forall u : U, change u <> u.
Proof.
  apply ind; unfold change;
  destruct (ind _) as [f H]; decompose [and] H; clear H;
  help H1.
Qed.

Definition Russel_Girard_simplified : False.
Proof.
  destruct (bad_sur (fun u : U => change (bad u u))).
  unfold bad in H. destruct (ind _); clear a.
  apply (f_equal (fun f => f x)) in H.
  apply (change_neq (x0 x x)).
  assumption.
Qed.

End Russel_Girard.