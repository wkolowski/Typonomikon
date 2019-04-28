(** * Koindukcja (znowu, ale lepiej) *)

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

(** Zadania:

    1. Zdefiniuj typ potencjalnie nieskończonych drzew binarnych trzymających
       wartości typu [A] w węzłach, jego relację bipodobieństwa, predykaty
       "skończony" i "nieskończony" oraz funkcję [mirror], która zwraca
       lustrzane odbicie drzewa. Udowodnij, że bipodobieństwo jest relacją
       równoważności i że funkcja [mirror] jest inwolucją
       (tzn. [mirror (mirror t)] jest bipodobne do [t]), która zachowuje
       właściwości bycia drzewem skończonym/nieskończonym. Pokaż, że drzewo
       nie może być jednocześnie skończone i nieskończone.

    2. Znajdź taką rodzinę typów koinduktywnych [C], że dla dowolnego
       typu [A], [C A] jest w bijekcji z typem funkcji [nat -> A]. Przez
       bijekcję będziemy tu rozumieć funkcję, która ma odwrotność, z którą
       w obie strony składa się do identyczności.

       Uwaga: nie da się tego udowodnić bez użycia dodatkowych aksjomatów,
       które na szczęście są bardzo oczywiste i same się narzucają.
*)

(** ** Indukcja i rekursja dobrze ufundowana *)

Module Wf.

Inductive Acc {A : Type} (R : A -> A -> Type) (x : A) : Prop :=
    | Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.

Definition well_founded {A : Type} (R : A -> A -> Type) : Prop :=
  forall x : A, Acc R x.

Lemma le_not_Acc :
  forall n : nat, Acc le n -> False.
Proof.
  induction 1. apply (H0 x). apply le_n.
Qed.

Lemma le_not_wf : ~ well_founded le.
Proof.
  unfold well_founded. intro.
  apply le_not_Acc with 0. apply H.
Qed.

Lemma lt_wf : well_founded lt.
Proof.
  unfold well_founded.
  induction x as [| n']; constructor; inversion 1; subst.
    assumption.
    inversion IHn'. apply H0. assumption.
Qed.

Theorem well_founded_induction_type :
  forall
    (A : Type) (R : A -> A -> Type)
    (wf : well_founded R) (P : A -> Type),
      (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
        forall x : A, P x.
Proof.
  intros A R wf P IH x.
  unfold well_founded in wf.
  specialize (wf x).
  induction wf.
  apply IH.
  assumption.
Defined.

End Wf.

(** Zadania:

    3. Sprawdź, czy dobrze ufundowana jest następująca relacja porządku
       (mam nadzieję, że obrazek jest zrozumiały):
       [0 < 1 < ... < ω < ω + 1 < ... < 2 * ω]

       Oczywiście najpierw musisz wymyślić, w jaki sposób zdefiniować taką
       relację.

    4. Niech (B, R) będzie typem wyposażonym w relację dobrze ufundowaną R.
       Zdefiniuj po współrzędnych relację porządku na funkcjach [A -> B]
       i rozstrzygnij, czy relacja ta jest dobrze ufundowana.

    5. Zdefiniuj pojęcie "nieskończonego łańcucha malejącego" (oczywiście
       za pomocą koindukcji) i udowodnij, że jeżeli relacja jest dobrze
       ufundowana, to nie ma nieskończonych łańcuchów malejących.
*)

(** Przykład: dzielenie i indukcja funkcyjna *)

Require Import Arith.
Require Import Omega.

Definition div : nat -> forall k : nat, 0 < k -> nat.
Proof.
  apply (@well_founded_induction_type nat lt lt_wf
    (fun n : nat => forall k : nat, 0 < k -> nat)).
  intros. destruct (le_lt_dec k x).
    Focus 2. exact 0.
    apply S. apply (H (x - k)) with k.
      apply Nat.sub_lt; assumption.
      assumption.
Defined.

Compute div 5 2 ltac:(omega).

Lemma div_le :
  forall (n m : nat) (H : 0 < m),
    div n m H <= n.
Proof.
  intros. revert n.
  apply (@well_founded_induction_type nat lt lt_wf).
  intros n IH.
  cbn. destruct (le_lt_dec m n).
    admit.
    apply le_0_n.
Abort.

Lemma div_lt_n_k :
  forall (n k : nat) (H : 0 < k),
    n < k -> div n k H = 0.
Proof.
  intros. cbn. destruct (le_lt_dec k n).
    omega.
    trivial.
Qed.

Lemma div_le_k_n :
  forall (n k : nat) (H : 0 < k),
    k <= n -> div n k H = S (div (n - k) k H).
Proof.
  apply (@well_founded_ind nat lt lt_wf
    (fun n => forall (k : nat) (H : 0 < k),
      k <= n -> div n k H = S (div (n - k) k H))).
  intros. cbn. destruct (le_lt_dec k x).
    f_equal.
Admitted.

Theorem div_eq :
  forall (n k : nat) (H : 0 < k), div n k H =
    match le_lt_dec k n with
        | left _ => S (div (n - k) k H)
        | right _ => 0
    end.
Proof.
  intros. destruct (le_lt_dec k n).
    rewrite div_le_k_n; auto.
    rewrite div_lt_n_k; auto.
Qed.

Lemma div_le :
  forall (n m : nat) (H : 0 < m),
    div n m H <= n.
Proof.
  intros.
  rewrite div_eq.
  destruct (le_lt_dec m n).
Abort.

Inductive divR : nat -> nat -> nat -> Prop :=
    | div_base :
        forall (n k : nat), 0 < k -> n < k -> divR n k 0
    | div_rec :
        forall (n k r : nat), 0 < k -> k <= n ->
          divR (n - k) k r -> divR n k (S r).

Hint Constructors divR.

Lemma divR_correct :
  forall (n k r : nat) (H : 0 < k),
    div n k H = r -> divR n k r.
Proof.
  apply (@well_founded_induction nat lt lt_wf
    (fun n : nat => forall (k r : nat) (H : 0 < k ),
      div n k H = r -> divR n k r)).
  intros. rewrite div_eq in H1. destruct (le_lt_dec k x); subst.
    Focus 2. constructor; auto.
    constructor; auto. apply H with H0; omega.
Qed.

Lemma divR_complete :
  forall (n k r : nat) (H : 0 < k),
    divR n k r -> div n k H = r.
Proof.
  induction 1.
    apply div_lt_n_k. assumption.
    rewrite <- IHdivR with H. rewrite div_le_k_n; auto.
Qed.

Theorem div_ind :
  forall P : nat -> nat -> nat -> Prop,
    (forall n k : nat, 0 < k -> n < k -> P n k 0) ->
    (forall (n k : nat) (H : 0 < k), k <= n ->
      P (n - k) k (div (n - k) k H) -> P n k (S (div (n - k) k H))) ->
        forall (n k : nat) (H : 0 < k), P n k (div n k H).
Proof.
  intros. apply divR_ind; intros.
    apply H; auto.
    eapply (divR_complete _ _ _ H2) in H4. subst. apply H0; assumption.
    apply divR_correct with H1. reflexivity.
Qed.

Lemma div_le :
  forall (n m : nat) (H : 0 < m),
    div n m H <= n.
Proof.
  apply (div_ind (fun n m r => r <= n)).
    intros. apply le_0_n.
    intros. destruct n as [| n'].
      omega.
      apply le_n_S. omega.
Qed.

Require Import Recdef.

(** div' n m = n/(m + 1) *)
Function div' (n m : nat) {measure id n} : nat :=
  if le_lt_dec (S m) n
  then S (div' (n - S m) m)
  else 0.
Proof.
  intros. unfold id. omega.
Defined.

Print R_div'.
Check R_div'_correct.
Check R_div'_complete.
Check div'_ind.

Lemma div'_le :
  forall n m : nat, div' n m <= n.
Proof.
  intros. functional induction (div' n m).
    omega.
    apply le_0_n.
Defined.

(** Zadanie:

    6. Zdefiniuj funkcję [rot2], która bierze funkcję i zamienia miejscami
       sąsiednie elementy na liście, np. [rot2 [1; 2; 3; 4] = [2; 1; 4; 3]].

       Spróbuj udowodnić przez indukcję, że [rot2] jest inwolucją, tzn.
       [rot2 (rot2 l) = l]. Wytłumacz, dlaczego się nie da.

       Zdefiniuj ręcznie regułę indukcji dla list, za pomocą której da się
       udowodnić to twierdzenie.

       Zdefiniuj relację opisującą wykres funkcji [rot2]. Pokaż, że
       definicja wykresu jest poprawna i pełna oraz wyprowadź z niej
       regułę indukcji funkcyjnej dla funkcji [rot2]. Użyj jej, żeby
       jeszcze raz udowodnić, że [rot2] jest inwolucją.

       Na koniec zdefiniuj funkcję [rot2] jeszcze raz, tym razem za pomocą
       komendy [Function]. Porównaj swoje definicje wykresu oraz reguły
       indukcji z tymi automatycznie wygenerowanymi. Użyj taktyki [functional
       induction], żeby jeszcze raz udowodnić twierdzenie.
*)

(** ** Plugin Equations *)

(** Zabrakło czasu na customowy przykład.

    Zadanie:

    Zainstaluj plugin Equations:
    https://github.com/mattam82/Coq-Equations

    Przeczytaj tutorial:
    https://raw.githubusercontent.com/mattam82/Coq-Equations/master/doc/equations_intro.v

    Następnie znajdź jakiś swój dowód przez indukcję, który był skomplikowany
    i napisz prostszy dowód, najpierw za pomocą komendy [Function] i taktyki
    [functional induction], a potem za pomocą komendy [Equations] i taktyki
    [funelim].
*)