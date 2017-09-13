(** * Z1: Teoria funkcji (alfa, TODO) *)

Require Import Arith.

(** Prerekwizyty:
    - [Empty_set], [unit], [prod], [sum] i funkcje
    - właściwości konstruktorów? *)

(** W tym rozdziale zapoznamy się z najważniejszymi rodzajami funkcji.
    Trzeba przyznać na wstępie, że rozdział będzie raczej matematyczny. *)

(** * Injekcje *)

(** TODO ACHTUNG: to pojęcie zostało użyte implicite przy opisywaniu
    właściciwości konstruktorów. *)

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x x' : A, f x = f x' -> x = x'.

(** Objaśnienia zacznijmy od nazwy. Po łacinie "iacere" znaczy "rzucać",
    zaś "in" znaczy "w, do". W językach romańskich samo słowo "injekcja"
    oznacza zaś zastrzyk. Bliższym matematycznemu znaczeniu byłoby jednak
    tłumaczenie "wstrzyknięcie". Jeżeli funkcja jest injekcją, to możemy
    też powiedzieć, że jest "injektywna".

    Podstawowa idea jest prosta: jeżeli funkcja jest injekcją, to identyczne
    jej wartości pochodzą od równych argumentów.

    Przekonajmy się na przykładzie. *)

Goal injective (fun n : nat => 2 + n).
Proof.
  unfold injective; intros. destruct x, x'; cbn in *.
    trivial.
    inversion H.
    inversion H.
    inversion H. trivial.
Qed.

(** Funkcja [fun n : nat => 2 + n], czyli dodanie [2] z lewej strony, jest
    injekcją, gdyż jeżeli [2 + n = 2 + n'], to rozwiązując równanie dostajemy
    [n = n']. Jeżeli wartości funkcji są równe, to argumenty również muszą
    być równe.

    Zobaczmy też kontrprzykład. *)

Goal ~ injective (fun n : nat => n * n - n).
Proof.
  unfold injective, not; intros.
  specialize (H 0 1). simpl in H. specialize (H eq_refl). inversion H.
Qed.

(** Funkcja f(n) = n^2 - n nie jest injekcją, gdyż mamy zarówno f(0) = 0
    jak i f(1) = 0. Innymi słowy: są dwa nierówne argumenty (0 i 1), dla
    których wartość funkcji jest taka sama (0).

    A oto alternatywna definicja. *)

Definition injective' {A B : Type} (f : A -> B) : Prop :=
  forall x x' : A, x <> x' -> f x <> f x'.

(** Głosi ona, że funkcja injektywna to funkcja, która dla różnych argumentów
    przyjmuje różne wartości. Innymi słowy, injekcja to funkcja, która
    zachowuje relację [<>]. Przykład 1 możemy sparafrazować następująco:
    jeżeli [n] jest różn od [n'], to wtedy [2 + n] jest różne od [2 + n'].

    Definicja ta jest równoważna poprzedniej, ale tylko pod warunkiem, że
    przyjmiemy logikę klasyczną. W logice konstruktywnej pierwsza definicja
    jest ogólniejsza od drugiej. *)

(** **** Ćwiczenie *)

(** Pokaż, że [injective] jest mocniejsze od [injective']. Pokaż też, że w
    logice klasycznej są one równoważne. *)

Theorem injective_injective' :
  forall (A B : Type) (f : A -> B),
    injective f -> injective' f.
(* begin hide *)
Proof.
  unfold injective, injective', not; intros.
  apply H0. apply H. assumption.
Qed.
(* end hide *)

Theorem injective'_injective :
  (forall P : Prop, ~ ~ P -> P) ->
  forall (A B : Type) (f : A -> B),
    injective' f -> injective f.
(* begin hide *)
Proof.
  unfold injective, injective', not; intros.
  apply H. intro. apply (H0 x x'); assumption.
Qed.
(* end hide *)

(** Udowodnij, że różne funkcje są lub nie są injektywne. *)

Theorem id_injective :
  forall A : Type, injective (fun x : A => x).
(* begin hide *)
Proof.
  intro. unfold injective. trivial.
Qed.
(* end hide *)

Theorem S_injective : injective S.
(* begin hide *)
Proof.
  red. inversion 1. trivial.
Qed.
(* end hide *)

Theorem const_unit_inj :
  forall (A : Type) (a : A),
    injective (fun _ : unit => a).
(* begin hide *)
Proof.
  unfold injective; intros. destruct x, x'. trivial.
Qed.
(* end hide *)

Theorem add_k_left_inj :
  forall k : nat, injective (fun n : nat => k + n).
(* begin hide *)
Proof.
  red. induction k as [| k']; simpl; intros.
    assumption.
    inversion H. apply IHk'. assumption.
Qed.
(* end hide *)

Theorem mul_k_inj :
  forall k : nat, k <> 0 -> injective (fun n : nat => k * n).
(* begin hide *)
Proof.
  red. intros k H x x'. generalize dependent k. generalize dependent x'.
  induction x as [| y]; induction x' as [| y']; simpl; intros.
    trivial.
    do 2 (rewrite mult_comm in H0; simpl in *). destruct k.
      contradiction H. trivial.
      simpl in H0. inversion H0.
    rewrite mult_0_r in H0. rewrite mult_comm in H0. simpl in H0. destruct k.
      contradiction H. trivial.
      simpl in H0. inversion H0.
    f_equal. apply (IHy y' k).
      assumption.
      SearchPattern (_ * S _ = _).
      do 2 rewrite mult_succ_r in H0. rewrite plus_comm in H0 at 1.
        replace (k * y' + k) with (k + k * y') in H0.
          assert (Hinj : injective (fun n : nat => k + n)).
            apply add_k_left_inj.
          red in Hinj. apply Hinj in H0. assumption.
        apply plus_comm.
Qed.
(* end hide *)

Theorem const_2elem_not_inj :
  forall (A B : Type) (b : B),
    (exists a a' : A, a <> a') -> ~ injective (fun _ : A => b).
(* begin hide *)
Proof.
  unfold injective, not; intros. destruct H as [a [a' H]].
  specialize (H0 a a' eq_refl). contradiction.
Qed.
(* end hide *)

Theorem mul_k_0_not_inj :
  ~ injective (fun n : nat => 0 * n).
(* begin hide *)
Proof.
  simpl. apply const_2elem_not_inj. exists 0, 1. inversion 1.
Qed.
(* end hide *)

Theorem pred_not_injective : ~ injective pred.
(* begin hide *)
Proof.
  unfold injective; intro. specialize (H 0 1 eq_refl). inversion H.
Qed.
(* end hide *)

(** Jedną z ważnych właśściwości injekcji jest to, że są składalne:
    złożenie dwóch injekcji daj injekcję. *)

Theorem inj_comp :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    injective f -> injective g -> injective (fun x : A => g (f x)).
(* begin hide *)
Proof.
  unfold injective; intros.
  specialize (H0 _ _ H1). specialize (H _ _ H0). assumption.
Qed.
(* end hide *)

(** Ta właściwość jest dziwna. Być może kiedyś wymyślę dla niej jakąś
    bajkę. *)

Theorem LOLWUT :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    injective g -> injective (fun x : A => g (f x)) -> injective f.
(* begin hide *)
Proof.
  unfold injective; intros.
  apply H0. rewrite H1. trivial.
Qed.
(* end hide *)

(** Surjekcje *)

Definition surjective {A B : Type} (f : A -> B) : Prop :=
    forall b : B, exists a : A, f a = b.

Theorem S_not_surjective : ~ surjective S.
(* begin hide *)
Proof.
  unfold surjective; intro. destruct (H 0). inversion H0.
Qed.
(* end hide *)

Definition bijective {A B : Type} (f : A -> B) : Prop :=
    injective f /\ surjective f.

Definition bijective' {A B : Type} (f : A -> B) : Prop :=
    forall b : B, exists! a : A, f a = b.

Theorem bijectives_equiv : forall (A B : Type) (f : A -> B),
    bijective f <-> bijective' f.
(* begin hide *)
Proof.
  unfold bijective, bijective', injective, surjective; split; intros.
    destruct H as [Hinj Hsur]. destruct (Hsur b) as [a H].
      exists a. red. split; try assumption. intros. apply Hinj.
      rewrite H, H0. reflexivity.
    split; intros.
      destruct (H (f x)) as [a Ha]. destruct Ha as [Ha1 Ha2].
        rewrite <- (Ha2 x).
          apply Ha2. rewrite H0. reflexivity.
          reflexivity.
      destruct (H b) as [a [H1 H2]]. exists a. assumption.
Qed.
(* end hide *)

Require Import List.
Import ListNotations.

Fixpoint unary (n : nat) : list unit :=
match n with
    | 0 => []
    | S n' => tt :: unary n'
end.

Theorem unary_bij : bijective unary.
(* begin hide *)
Proof.
  unfold bijective, injective, surjective. split.
    induction x as [| y]; induction x' as [| y']; simpl in *.
      trivial.
      inversion 1.
      inversion 1.
      inversion 1. f_equal. apply IHy. assumption.
    intro. exists (length b). induction b as [| h t]; simpl.
      trivial.
      destruct h. f_equal. assumption.
Qed.
(* end hide *)

