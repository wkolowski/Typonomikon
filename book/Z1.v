(** * Z1: Reguły indukcji i indukcja funkcyjna [TODO] *)

Require Import Coq.Program.Wf Arith NPeano Div2 Lia List.
Import ListNotations.

(** * Customowe reguły indukcji *)

Fixpoint nat_ind_2
  (P : nat -> Prop)
  (H0 : P 0) (H1 : P 1)
  (H : forall n : nat, P n -> P (S (S n)))
  (n : nat) : P n :=
match n with
| 0 => H0
| 1 => H1
| S (S n') => H n' (nat_ind_2 P H0 H1 H n')
end.

Lemma expand :
  forall (P : nat -> Prop) (n k : nat),
    ~ n <= k -> P (k + (n - k)) -> P n.
Proof.
  intros. replace n with (k + (n - k)).
    assumption.
    lia.
Defined.

Program Fixpoint nat_ind_k
  (k : nat) (P : nat -> Prop)
  (H : forall k' : nat, k' <= k -> P k')
  (H' : forall n : nat, P n -> P (S k + n))
  (n : nat) {measure n} : P n :=
match le_dec n k with
| left n_le_k => H n n_le_k
| right n_gt_k =>
    expand P n k n_gt_k (H' (n - S k) (nat_ind_k k P H H' (n - S k)))
end.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.

Inductive even : nat -> Prop :=
| even0 : even 0
| evenSS : forall n : nat, even n -> even (S (S n)).

Fixpoint even_ind'
  (P : nat -> Prop)
  (H0 : P 0)
  (HSS : forall n : nat, even n -> P n -> P (S (S n)))
  (n : nat) (Heven : even n) : P n.
Proof.
  destruct n as [| [| n']].
    assumption.
    inversion Heven.
    inversion Heven; subst. apply HSS.
      assumption.
      apply (even_ind' P H0 HSS n' H1).
Defined.

Program Fixpoint nat_ind_k'
  (k : nat) (Hk : k <> 0) (P : nat -> Prop)
  (H : forall k' : nat, k' <= k -> P k')
  (H' : forall n : nat, P n -> P (k + n))
  (n : nat) {measure n} : P n :=
match le_dec n k with
| left n_le_k => H n n_le_k
| right n_gt_k =>
    expand P n k n_gt_k (H' (n - k) (nat_ind_k' k Hk P H H' (n - k)))
end.
Next Obligation. lia. Defined.

Fixpoint nat_ind_8
  {P : nat -> Type}
  (P0 : P 0)
  (P1 : P 1)
  (P2 : P 2)
  (P3 : P 3)
  (P4 : P 4)
  (P5 : P 5)
  (P6 : P 6)
  (P7 : P 7)
  (P8plus : forall n : nat, P n -> P (8 + n))
  (n : nat) : P n :=
match n with
| 0 => P0
| 1 => P1
| 2 => P2
| 3 => P3
| 4 => P4
| 5 => P5
| 6 => P6
| 7 => P7
| S (S (S (S (S (S (S (S n'))))))) =>
    P8plus n' (nat_ind_8 P0 P1 P2 P3 P4 P5 P6 P7 P8plus n')
end.

Lemma above_7 : forall n : nat,
    exists i j : nat, 8 + n = 3 * i + 5 * j.
Proof.
  apply nat_ind_8.
    exists 1, 1. cbn. reflexivity.
    exists 3, 0. cbn. reflexivity.
    exists 0, 2. cbn. reflexivity.
    exists 2, 1. cbn. reflexivity.
    exists 4, 0. cbn. reflexivity.
    exists 1, 2. cbn. reflexivity.
    exists 3, 1. cbn. reflexivity.
    exists 0, 3. cbn. reflexivity.
    intros n' (i & j & IH). exists (S i), (S j). lia.
Qed.

Fixpoint fac (n : nat) : nat :=
match n with
| 0 => 1
| S n' => n * fac n'
end.

Fixpoint f (n : nat) : nat :=
match n with
| 0 => 0 * fac 0
| S n' => f n' + n * fac n
end.

Lemma pred_lemma :
  forall n m : nat,
    1 <= n -> pred (n + m) = pred n + m.
Proof.
  induction 1; cbn; trivial.
Qed.

Lemma fact_ge_1 :
  forall n : nat, 1 <= fac n.
Proof.
  induction n as [| n']; cbn.
    trivial.
    eapply Nat.le_trans. eauto. apply Nat.le_add_r.
Qed.

Lemma f_fac :
  forall n : nat, f n = pred (fac (1 + n)).
Proof.
  induction n as [| n'].
    cbn. trivial.
    cbn in *. rewrite pred_lemma. rewrite IHn'. trivial.
    eapply Nat.le_trans.
      apply fact_ge_1.
      apply Nat.le_add_r.
Qed.

Inductive pos : Set :=
| HJ : pos
| Z : pos -> pos
| J : pos -> pos.

Inductive bin : Set :=
| HZ : bin
| HP : pos -> bin.

Definition five : bin := HP (J (Z HJ)).
Definition answer : bin := HP (Z (J (Z (J (Z HJ))))).

Fixpoint pos_to_nat (p : pos) : nat :=
match p with
| HJ => 1
| Z p' => 2 * pos_to_nat p'
| J p' => 1 + 2 * pos_to_nat p'
end.

Definition bin_to_nat (b : bin) : nat :=
match b with
| HZ => 0
| HP p => pos_to_nat p
end.

Program Fixpoint divmod
  (n k : nat) (H : k <> 0) {measure n} : nat * nat :=
match n with
| 0 => (0, 0)
| _ =>
  if Nat.leb n k
  then (0, n)
  else let (d, m) := divmod (n - k) k H in (S d, m)
end.
Next Obligation. lia. Qed.

Lemma two_not_0 : 2 <> 0.
Proof. inversion 1. Qed.

Fixpoint divmod2 (n : nat) : nat * nat :=
match n with
| 0 => (0, 0)
| 1 => (0, 1)
| S (S n') => let (a, b) := divmod2 n' in (S a, b)
end.

Compute divmod2 155.

Compute bin_to_nat answer.
Compute bin_to_nat (HP (Z (J (Z (J (Z HJ)))))).

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x x' : A, f x = f x' -> x = x'.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall b : B, exists a : A, f a = b.

Definition bijective {A B : Type} (f : A -> B) : Prop :=
  injective f /\ surjective f.

Lemma pos_to_nat_neq_0 :
  forall p : pos,
    pos_to_nat p <> 0.
Proof.
  induction p as [| p' | p']; cbn; inversion 1.
  apply IHp'. destruct (pos_to_nat p').
    trivial.
    inversion H.
Qed.

Lemma pos_to_nat_inj :
  injective pos_to_nat.
Proof.
  red. induction x as [| p1 | p1]; induction x' as [| p2 | p2]; cbn in *.
    reflexivity.
    lia.
    inversion 1. assert (pos_to_nat p2 = 0). lia.
      destruct (pos_to_nat_neq_0 _ H0).
    lia.
    intros. f_equal. apply IHp1. lia.
    intros. cut False; lia.
    inversion 1. assert (pos_to_nat p1 = 0). lia.
      destruct (pos_to_nat_neq_0 _ H0).
    lia.
    inversion 1. f_equal. apply IHp1. lia.
Qed.

#[global] Hint Resolve pos_to_nat_inj : core.

Lemma bin_to_nat_inj : injective bin_to_nat.
Proof.
  red. destruct x, x'; cbn; intro.
    trivial.
    cut False. inversion 1. eapply pos_to_nat_neq_0. eauto.
    cut False. inversion 1. eapply pos_to_nat_neq_0. eauto.
    f_equal. apply pos_to_nat_inj. assumption.
Qed.

Fixpoint succ (p : pos) : pos :=
match p with
| HJ => Z HJ
| J p' => Z (succ p')
| Z p' => J p'
end.

Lemma pos_to_nat_S :
  forall (p : pos),
    pos_to_nat (succ p) = S (pos_to_nat p).
Proof.
  induction p as [| p' | p']; cbn; trivial.
    rewrite IHp'. cbn. rewrite <- plus_n_Sm. reflexivity.
Qed.

Lemma bin_to_nat_sur :
  surjective bin_to_nat.
Proof.
  red. intro n. induction n as [| n'].
    exists HZ. cbn. trivial.
    destruct IHn' as [b H]. destruct b; cbn in H.
      exists (HP HJ). cbn. rewrite H. trivial.
      destruct p; cbn in H.
        exists (HP (Z HJ)). cbn. rewrite H. trivial.
        exists (HP (succ (Z p))). cbn. rewrite H. trivial.
        exists (HP (succ (J p))). cbn. rewrite pos_to_nat_S.
          cbn. f_equal. rewrite <- plus_n_Sm. assumption.
Qed.

Lemma bin_to_nat_bij :
  bijective bin_to_nat.
Proof.
  unfold bijective. split.
    apply bin_to_nat_inj.
    apply bin_to_nat_sur.
Qed.

Lemma div2_even_inv :
  forall n m : nat,
    n + n = m -> n = Nat.div2 m.
Proof.
  intros n m. generalize dependent n.
  induction m using nat_ind_2; cbn; intros.
    destruct n; inversion H. trivial.
    destruct n; inversion H.
      rewrite <- plus_n_Sm in H1. inversion H1.
    rewrite <- (IHm (pred n)); destruct n; inversion H; cbn; trivial.
      rewrite <- plus_n_Sm in H. inversion H. trivial.
Qed.

Lemma div2_odd_inv :
  forall n m : nat,
    S (n + n) = m -> n = Nat.div2 m.
Proof.
  intros n m. generalize dependent n.
  induction m using nat_ind_2; cbn; intros.
    inversion H.
    inversion H. destruct n; inversion H1; trivial.
    rewrite <- (IHm (pred n)).
      destruct n.
        inversion H.
        cbn. trivial.
      destruct n.
        inversion H.
        cbn in *. rewrite <- plus_n_Sm in H. inversion H. trivial. 
Qed.

Lemma nat_ind_bin
  (P : nat -> Prop) (H0 : P 0)
  (Hx2 : forall n : nat, P n -> P (2 * n))
  (Hx2p1 : forall n : nat, P n -> P (1 + 2 * n))
  (n : nat) : P n.
Proof.
  pose proof bin_to_nat_sur. red in H. destruct (H n) as [b H'].
  rewrite <- H'. destruct b as [| p].
    cbn. apply H0.
    generalize dependent n. induction p as [| p' | p']; intros.
      cbn. change 1 with (1 + 2 * 0). apply Hx2p1. assumption.
      cbn in *. apply Hx2. apply (IHp' (Nat.div2 n)).
        apply div2_even_inv. rewrite <- plus_n_O in H'. assumption.
      cbn in *. apply Hx2p1. apply (IHp' (Nat.div2 n)).
        apply div2_odd_inv. rewrite <- plus_n_O in H'. assumption.
Qed.

Lemma even_dec :
  forall n : nat,
    {k : nat & {n = 2 * k} + {n = 1 + 2 * k}}.
Proof.
  induction n as [| n'].
    exists 0. left. trivial.
    destruct IHn' as [k [H | H]].
      exists k. right. rewrite H. trivial.
      exists (S k). left. rewrite H. cbn. lia.
Defined.

Inductive Tree (A : Type) : Type :=
| Empty : Tree A
| Node : A -> list (Tree A) -> Tree A.

Arguments Empty {A}.
Arguments Node {A} _ _.

Print Tree_ind.

Fixpoint Tree_ind_full
  (A : Type) (P : Tree A -> Prop) (Q : list (Tree A) -> Prop)
  (HPQ : forall ltr : list (Tree A), Q ltr -> forall x : A, P (Node x ltr))
  (HPEmpty : P Empty)
  (HQNil : Q nil)
  (HQCons : forall (h : Tree A) (t : list (Tree A)),
      P h -> Q t -> Q (cons h t))
  (t : Tree A) : P t.
Proof.
  destruct t as [| v forest].
    apply HPEmpty.
    apply HPQ. induction forest as [| t' forest'].
      apply HQNil; auto.
      apply HQCons; auto. apply Tree_ind_full with Q; eauto.
Defined.

Fixpoint size {A : Type} (t : Tree A) : nat :=
match t with
| Empty => 0
| Node v forest => 1 +
  (fix size' {A : Type} (forest : list (Tree A)) : nat :=
  match forest with
  | nil => 0
  | cons t forest' => size t + size' forest'
  end) _ forest
end.

Fixpoint size_f {A : Type} (t : Tree A) : nat :=
match t with
| Empty => 0
| Node _ forest => S (fold_right (fun t' s => size_f t' + s) 0 forest)
end.

Fixpoint flatten' {A : Type} (t : Tree A) : list A :=
match t with
| Empty => []
| Node v forest => v :: fold_right (fun h t => flatten' h ++ t) [] forest
end.

Lemma flatten_preserves_size :
    forall (A : Type) (t : Tree A), size t = length (flatten' t).
Proof.
  intro.
  induction t using Tree_ind_full with
      (Q := fun (ltr : list (Tree A)) =>
          forall v : A, size (Node v ltr) =
          S (length (fold_right (fun h t => flatten' h ++ t) [] ltr))).
    rewrite IHt. cbn. reflexivity.
    cbn. reflexivity.
    cbn. reflexivity.
    cbn. intro. f_equal. rewrite app_length.
      specialize (IHt0 v). inversion IHt0. rewrite H0.
      rewrite IHt. reflexivity.
Qed.

Section nat_ind_dbl_pred.

Variable P : nat -> Prop.

Hypothesis H1 : P 1.
Hypothesis Hdbl : forall n : nat, P n -> P (n + n).
Hypothesis Hpred : forall n : nat, P (S n) -> P n.

Lemma H0 : P 0.
Proof. apply Hpred. assumption. Qed.

Lemma Hplus : forall n m : nat, P (n + m) -> P m.
Proof.
  induction n as [| n']; cbn.
    trivial.
    intros. apply IHn'. apply Hpred. assumption.
Qed.

Lemma HS : forall n : nat, P n -> P (S n).
Proof.
  induction n as [| n']; intro.
    assumption.
    apply Hplus with n'. replace (n' + S (S n')) with (S n' + S n').
      apply Hdbl. assumption.
      rewrite (Nat.add_comm n'). cbn. f_equal. rewrite Nat.add_comm. trivial.
Qed.

Lemma nat_ind_dbl_pred : forall n : nat, P n.
Proof.
  induction n as [| n'].
    apply H0.
    apply HS. assumption.
Qed.

End nat_ind_dbl_pred.

Goal forall n : nat, 2 * n <= Nat.pow 2 n.
Proof.
  induction n as [| n'].
    cbn. lia.
    cbn [Nat.pow]. destruct n'; cbn in *; lia.
Qed.

Lemma pow2_lin :
  forall n : nat,
    n < Nat.pow 2 n.
Proof.
  induction n as [| n']; cbn.
    constructor.
    lia.
Qed.

Goal forall n : nat, 2 * n < Nat.pow 2 (S n).
Proof.
  intros. cbn [Nat.pow].
  apply Nat.mul_lt_mono_pos_l.
  - apply Nat.lt_0_succ.
  - apply pow2_lin.
Qed.

Definition maxL := fold_right max 0.
Definition sumL := fold_right plus 0.

Lemma whatt : forall l : list nat, sumL l <= length l * maxL l.
Proof.
  induction l as [| h t]; cbn.
    trivial.
    apply Nat.add_le_mono.
      apply Nat.le_max_l.
      apply Nat.le_trans with (length t * maxL t).
        assumption.
        apply Nat.mul_le_mono.
          apply le_n.
          apply Nat.le_max_r.
Qed.

Fixpoint nat_ind_4
  (P : nat -> Type)
  (P0 : P 0)
  (P1 : P 1)
  (P2 : P 2)
  (P3 : P 3)
  (P4 : forall n : nat, P n -> P (4 + n))
  (n : nat) : P n :=
match n with
| 0 => P0
| 1 => P1
| 2 => P2
| 3 => P3
| S (S (S (S n'))) => P4 n' (nat_ind_4 P P0 P1 P2 P3 P4 n')
end.

Lemma two_and_five :
  forall n : nat,
    exists i j : nat, 4 + n = 2 * i + 5 * j.
Proof.
  induction n using nat_ind_4.
    exists 2, 0. cbn. reflexivity.
    exists 0, 1. cbn. reflexivity.
    exists 3, 0. cbn. reflexivity.
    exists 1, 1. cbn. reflexivity.
    destruct IHn as (i & j & IH).
      exists (2 + i), j. rewrite IH. lia.
Qed.

(** * Reguły indukcji dla typów zagnieżdżonych *)

Inductive RoseTree (A : Type) : Type :=
| E : RoseTree A
| N : A -> list (RoseTree A) -> RoseTree A.

Arguments E {A}.
Arguments N {A} _ _.

(** Rzućmy okiem na powyższy typ drzew różanych. Elementy tego typu są albo
    puste, albo są węzłami, które trzymają element typu [A] i listę poddrzew.

    A jak się ma reguła indukcji, którą Coq wygenerował nam dla tego typu?
    Mogłoby się wydawać, że jest najzwyczajniejsza w świecie, ale nic bardziej
    mylnego. *)

Check RoseTree_ind.
(* ===>
  RoseTree_ind :
    forall (A : Type) (P : RoseTree A -> Prop),
      P E ->
      (forall (a : A) (l : list (RoseTree A)), P (N a l)) ->
        forall r : RoseTree A, P r
*)

(** Jeśli dobrze się przyjrzeć tej regule, to widać od razu, że nie ma w niej
    żadnej ale to żadnej indukcji. Są tylko dwa przypadki bazowe: jeden dla
    drzewa pustego, a drugi dla węzła z dowolną wartością i dowolną listą
    poddrzew.

    Dzieje się tak dlatego, że induktywne wystąpienie typu [RoseTree A] jest
    zawinięte w [list], a Coq nie potrafi sam z siebie wygenerować czegoś w
    stylu "jedna hipoteza indukcyjna dla każdego drzewa t z listy ts". Musimy
    mu w tym pomóc!
*)

Print Forall.
(* ===>
Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop :=
| Forall_nil : Forall P []
| Forall_cons :
    forall (x : A) (l : list A),
      P x -> Forall P l -> Forall P (x :: l).
*)

(** W tym celu przyda nam się induktywnie zdefiniowany predykat [Forall].
    Jeżeli [Forall P l] zachodzi, to każdy element listy [l] spełnia predykat
    [P]. Definicja jest prosta: każdy element pustej listy spełnia [P], a jeżeli
    głowa spełnia [P] i każdy element ogona spełnia [P], to każdy element całej
    listy spełnia [P].

    Dzięki [Forall] możemy już bez trudu wyrazić myśl "dla każdego elementu
    listy mamy hipotezę indukcyjną". Nie pozostaje nic innego, jak sformułować
    i udowodnić porządną regułę indukcji.
*)

Fixpoint RoseTree_ind'
  {A : Type} (P : RoseTree A -> Prop)
  (P_E : P E)
  (P_N : forall (v : A) (ts : list (RoseTree A)), Forall P ts -> P (N v ts))
  (t : RoseTree A) : P t.
Proof.
  destruct t as [| v ts].
  - exact P_E.
  - apply P_N.
    induction ts as [| t ts' IH].
    + constructor.
    + constructor.
      * exact (RoseTree_ind' A P P_E P_N t).
      * exact IH.
Defined.

(** Nasza reguła ma się następująco. Będziemy jej używać do dowodzenia, że każde
    drzewo różane [t] spełnia predykat [P : RoseTree A -> Prop] pod warunkiem, że:
    - drzewo puste spełnia [P]
    - jeżeli każde drzewo z listy [ts] spełnia [P], to dla dowolnego [v : A]
      drzewo [N v ts] również spełnia [P] *)

(** Dowód jest dość prosty. Zauważmy, że zaczyna się on od komendy [Fixpoint],
    ale mimo tego nie piszemy termu, ale odpalamy tryb dowodzenia. Wobec tego
    [RoseeTree_ind'] pojawia się w naszym kontekście jako hipoteza indukcyjna.

    Zaczynamy od rozbicia [t]. Gdy jest puste, kończymy hipotezą [P_E]. Gdy
    jest węzłem, używamy hipotezy [P_N]. Teraz trzeba udowodnić [Forall P ts],
    ale trochę nie ma jak - nasza hipoteza indukcyjna nam w tym nie pomoże, a
    [P_E] i [P_N] też nie za bardzo.

    Kluczową obserwacją w tym momencie jest, że [Forall P ts] jest zdefiniowany
    induktywnie i ma taki sam kształt, jak lista [ts] ([Forall P ts] to w sumie
    "udekorowanie" listy [ts] dowodami [P] dla poszczególnych elementów), więc
    powinniśmy rozumować przez indukcję po [ts].

    W obu przypadkach używamy konstruktora. Pierwszy jest banalny, zaś drugi
    generuje dwa kolejne podcele. W pierwszym używamy naszej "oryginalnej"
    hipotezy induktywnej [RoseTree_ind'], a w drugim hipotezy indukcyjnej
    pochodzącej z indukcji po liście [ts], którą nazwaliśmy [IH]. To kończy
    dowód.
*)

Fixpoint map {A B : Type} (f : A -> B) (t : RoseTree A) : RoseTree B :=
match t with
| E => E
| N v ts => N (f v) (List.map (map f) ts)
end.

(** Zobaczmy jeszcze tylko, jak użyć naszej nowitukiej reguły indukcji. W tym
    celu zdefiniujemy funkcję [map], analogiczną do tej dla list i innych rodzajów
    drzew, która są ci znane, oraz udowodnimy, że mapowanie identyczności to
    to samo co identyczność.
*)

Lemma map_id :
  forall {A : Type} (t : RoseTree A),
    map (fun x => x) t = t.
Proof.
  induction t using @RoseTree_ind'; cbn; [easy |].
  f_equal.
  induction H; cbn; [easy |].
  now rewrite H, IHForall.
Qed.

(** Dowód jest bardzo prosty. Zaczynamy przez indukcję po [t], używając naszej
    nowiutkiej reguły indukcji. Żeby użyć reguły indukcji innej niż domyślna,
    podajemy jej nazwę w klauzuli [using]. Zauważmy też, że musimy poprzedzić
    nazwę reguły indukcji symbolem [@], który sprawia, że argumenty domyślne
    przestają być domyślne. Jeżeli tego nie zrobimy, to Coq powie nam, że nie
    wie, skąd ma wziąć argument [A] (który nie został jeszcze wprowadzony do
    kontekstu).

    Przypadek bazowy jest łatwy, co ilustruje użycie taktyki [easy]. Ponieważ
    [id v = v], to wystarczy teraz pokazać, że twierdzenie zachodzi dla każdego
    drzewa z listy drzew [ts]. Chcemy w tym celu użyć hipotezy indukcyjnej [H],
    ale nie załatwia ona sprawy bezpośrednio: głosi ona, że zmapowanie [id] po
    każdym drzewie z [ts] daje oryginalne drzewo, ale nasz cel jest postaci
    [List.map (map id) ts = ts].

    Jako, że nie ma nigdzie w bibliotece standardowej odpowiedniego lematu,
    musimy znów wykonać indukcję, tym razem po [H]. Bazowy przypadek indukcji
    znów jest łatwy (taktyka [easy]), zaś w przypadku [cons]owym przepisujemy
    [map] w głowie i [List.map (map id)] w ogonie (to jest hipoteza indukcyjna
    z naszej drugiej indukcji) i jest po sprawie.
*)

Lemma map_id' :
  forall {A : Type} (t : RoseTree A),
    map (fun x => x) t = t.
Proof.
  induction t as [| v ts]; cbn; [easy |].
  f_equal.
  induction ts; cbn; [easy |].
  rewrite IHts.
Abort.

(** Zerknijmy jeszcze, co się stanie, jeżeli spróbujemy użyć autogenerowanej
    reguły indukcji. Początek dowodu przebiega tak samo, ale nie mamy do
    dyspozycji żadnych hipotez indukcyjnych, więc drugą indukcję robimy po
    [ts]. Jednak hipoteza indukcyjna z tej drugiej indukcji wystarcza nam
    jedynie do przepisania w ogonie, ale w głowie pozostaje [map id a],
    którego nie mamy czym przepisać. A zatem reguła wygenerowana przez Coqa
    faktycznie jest za mało ogólna.
*)

(** ** Podsumowanie *)

(** Podsumowując: Coq nie radzi sobie z generowaniem reguł indukcji dla
    zagnieżdżonych typów induktywnych, czyli takich, w których definiowany
    typ występuje jako argument innego typu, jak np. [list] w przypadku
    [RoseTree].

    Żeby rozwiązać ten problem, musimy sami sformułować i udowodnić sobie
    bardziej adekwatną regułę indukcji. W tym celu musimy dla zagnieżdżającego
    typu (czyli tego, w którym występuje definiowany przez nas typ, np. [list]
    dla [RoseTree]) zdefiniować predykat [Forall], który pozwoli nam wyrazić,
    że chcemy mieć hipotezę indukcją dla każdego jego elementu. Dowód reguły
    indukcji jest dość prosty i przebiega przez zagnieżdżoną indukcję - na
    zewnątrz w postaci komendy [Fixpoint], a wewnątrz w postaci indukcji po
    dowodzie [Forall].

    Powstałej w ten sposób reguły indukcji możemy używać za pomocą komendy
    [induction ... using ...], przy czym zazwyczaj i tak będziemy musieli
    użyć jeszcze jednej zagnieżdżonej indukcji, żeby cokolwiek osiągnąć.
*)

(** ** Papiery *)

(** Generowanie reguł indukcji dla zagnieżdżonych typów induktywnych:
    #<a class='link' href='https://www.ps.uni-saarland.de/~ullrich/bachelor/thesis.pdf'>
    Generating Induction Principles for Nested Inductive Types in MetaCoq</a>#

    Patrz też: #<a class='link' href='https://hal.inria.fr/hal-01897468/document'>
    Deriving proved equality tests in Coq-elpi: Stronger induction principles for
    containers in Coq</a># (unarna translacja parametryczna)
*)

(** * Głęboka indukcja (TODO) *)

(** Zacznijmy od krótkiego podsumowania naszej dotychczasowej podróży przez
    świat reguł indukcji.

    Standardowe reguły indukcji dla danego typu to te, które kształtem
    odpowiadają dokładnie kształtowi tego typu. Dla [nat] jest to reguła
    z przypadkiem bazowym zero oraz przypadkiem indukcyjnym (czyli "krokiem")
    następnikowym. Dla list jest to reguły z przypadkiem bazowym [nil] i
    "krokiem" [cons]. Dostajemy je od Coqa za darmo po zdefiniowaniu typu.

    Niestandardowe reguły indukcji to te, które musimy zdefiniować sobie sami.
    Dla [nat] może to być np. reguła z bazowymi przypadkami 0 i 1 oraz krokiem
    "co 2". Definiujemy je przez dopasowanie do wzorca i rekursję strukturalną.
    Bywają przydatne w dowodzeniu twierdzeń, których "kształt" niezbyt pasuje
    do kształtu danego typu.

    Proste, prawda? Otóż nie do końca.
*)

Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
| ForallT_nil  : ForallT P []
| ForallT_cons :
    forall {h : A} {t : list A},
      P h -> ForallT P t -> ForallT P (h :: t).

Fixpoint list_ind_deep
  {A : Type} (P : list A -> Type) (Q : A -> Type)
  (nil : P [])
  (cons : forall {h : A} {t : list A}, Q h -> P t -> P (h :: t))
  (l : list A) (l' : ForallT Q l) {struct l'} : P l.
Proof.
  destruct l' as [| h t Qh FQh].
  - exact nil.
  - apply cons.
    + exact Qh.
    + apply (list_ind_deep _ P Q); assumption.
Defined.

Module RecursiveDeepInd.

Fixpoint ForallT' {A : Type} (P : A -> Type) (l : list A) : Type :=
match l with
| [] => unit
| h :: t => P h * ForallT' P t
end.

Fixpoint list_ind_deep'
  {A : Type} (P : list A -> Type) (Q : A -> Type)
  (nil : P [])
  (cons : forall (h : A) (t : list A),
            Q h -> P t -> P (h :: t))
  (l : list A) (l' : ForallT' Q l) {struct l} : P l.
Proof.
  destruct l as [| h t].
  - exact nil.
  - destruct l' as [Qh FQh].
    apply cons.
    + exact Qh.
    + apply (list_ind_deep' _ P Q); assumption.
Defined.

End RecursiveDeepInd.

(** Dla drzewek różanych. *)

Inductive RoseTree' {A : Type} (P : A -> Type) : RoseTree A -> Type :=
| E' : RoseTree' P E
| N' : forall (x : A) (ts : list (RoseTree A)),
         P x -> ForallT (RoseTree' P) ts -> RoseTree' P (N x ts).

Arguments E' {A P}.
Arguments N' {A P x ts} _ _.

Fixpoint RoseTree_ind_deep'
  {A : Type} (P : RoseTree A -> Type) (Q : A -> Type)
  (e : P E)
  (n : forall (x : A) (ts : list (RoseTree A)),
         Q x -> ForallT P ts -> P (N x ts))
  {t : RoseTree A} (t' : RoseTree' Q t) {struct t'} : P t.
Proof.
  destruct t' as [| x l Qx FQt].
    exact e.
    apply n.
      exact Qx.
      induction FQt as [| hFQt tFQt]; constructor.
        apply (RoseTree_ind_deep' _ P Q); assumption.
        apply IHFQt.
Defined.