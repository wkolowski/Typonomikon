Context {A B : Type}.

Inductive traceF (X : Type) : Type :=
| Tnil'  : A -> traceF X
| Tcons' : A -> B -> X -> traceF X.

#[global] Arguments Tnil'  {X} _.
#[global] Arguments Tcons' {X}  _ _ _.

#[projections(primitive)]
CoInductive trace : Type := Trace
{
  Out : traceF trace;
}.

Notation Tnil a := (Trace (Tnil' a)).
Notation Tcons a b t := (Trace (Tcons' a b t)).

(**
  Tutaj prawilne definicje, w których destruktor jest nałożony na dopasowywany
  term (samego tr nie można dopasować, bo prymitywne projekcje zabraniają). *)

Definition hd tr :=
match Out tr with
| Tnil' a => a
| Tcons' a b tr0 => a
end.

Definition trace_decompose (tr: trace): trace :=
match Out tr with
| Tnil' a => Trace (Tnil' a)
| Tcons' a b tr' => Trace (Tcons' a b tr')
end.

(**
  Tutaj super zakamuflowane złe definicje, w których konstruktor pojawia się
  jako część wzorca, ale nie widać tego bo jest schowane pod elegancką notacją.
*)

Definition evil_hd tr :=
match tr with
| Tnil a => a
| Tcons a b tr0 => a
end.

Definition evil_trace_decompose (tr: trace): trace :=
match tr with
| Tnil a => Tnil a
| Tcons a b tr' => Tcons a b tr'
end.

(** Nie da się udowodnić reguły unikalności. *)
Lemma trace_destr: forall tr, tr = trace_decompose tr.
Proof.
  intros.
  unfold trace_decompose.
  destruct (Out tr).
Abort.

(** Takiej reguły unikalności też się nie da. *)
Lemma unfold : forall tr, tr = Trace (Out tr).
Proof.
  intros.
  assert (Out tr = Out {| Out := Out tr |}) by easy.
Abort.

(** ** Bisimulations between traces *)

Inductive bisimF (R : trace -> trace -> Type) (t1 t2 : trace) : Type :=
| bisim_nil :
    forall a1 a2 : A,
      Out t1 = Tnil' a1 -> Out t2 = Tnil' a2 -> a1 = a2 -> bisimF R t1 t2
| bisim_cons :
    forall a1 a2 b1 b2 tr1' tr2',
      Out t1 = Tcons' a1 b1 tr1' -> Out t2 = Tcons' a2 b2 tr2' ->
      a1 = a2 -> b1 = b2 -> R tr1' tr2' -> bisimF R t1 t2.

Arguments bisim_nil  {R t1 t2 a1 a2} _ _ _.
Arguments bisim_cons {R t1 t2 a1 a2 b1 b2 tr1' tr2'} _ _ _ _ _.

#[projections(primitive)]
CoInductive bisim (t1 t2 : trace) : Type := Bisim
{
  Out' : bisimF bisim t1 t2;
}.

Arguments Out' {t1 t2} _.

(**
  Używając prawilnej definicji [hd] idzie łatwo, choć nie tak łatwo jak przy
  pozytywnych typach koinduktywnych - musimy robić inwersję na hipotezie,
  zamiast po prostu rozbić [tr0] i [tr1].

  Swoją drogą, nie wiem dlaczego wolno robić inwersję na dowodzie bipodobieństwa,
  skoro ono też jest zdefiniowane jako negatywny typ koinduktywny...
*)
Lemma bisim_hd : forall tr0 tr1, bisim tr0 tr1 -> hd tr0 = hd tr1.
Proof.
  unfold hd.
  inversion 1 as [[]].
  - now rewrite e, e0.
  - now rewrite e, e0.
Qed.

(**
  Używającej evilnej definicji zaczynają się dziać podejrzane rzeczy -
  identycznie wyglądające termy nie są konwertowalne, i nie da się ich
  rozróżnić nawet włączając "Display all low-level contents".
*)

(** Używając prawilnej definicji [hd] idzie łatwo. *)
Lemma bisim_evil_hd : forall tr0 tr1, bisim tr0 tr1 -> evil_hd tr0 = evil_hd tr1.
Proof.
  unfold evil_hd.
  inversion 1 as [[]].
  - Fail rewrite e.
Abort.

(**
  Bipodobieństwo jest równoważnością - dowody są dość ociężałe.
*)

Lemma bisim_refl : forall tr, bisim tr tr.
Proof.
  cofix CH.
  constructor.
  destruct (Out tr) eqn: Heq.
  - now econstructor 1; [eassumption.. |].
  - econstructor 2; [eassumption.. | easy | easy | apply CH].
Qed.

Lemma bisim_sym : forall tr1 tr2, bisim tr1 tr2 -> bisim tr2 tr1.
Proof.
  cofix CIH.
  intros tr1 tr2 [[]].
  - now do 2 econstructor 1; [eassumption.. |].
  - now constructor; econstructor 2; [eassumption.. | | | apply CIH].
Qed.

Lemma bisim_trans : forall tr1 tr2 tr3,
  bisim tr1 tr2 -> bisim tr2 tr3 -> bisim tr1 tr3.
Proof.
  cofix CIH.
  intros tr1 tr2 tr3 H12 H23.
  inversion H12 as [[a1 a2 H1 H2 -> | a1 a2 b1 b2 tr1' tr2' H1 H2 -> -> Hbisim12]].
  - inversion H23 as [[a2' a3 H2' H3' -> |]]; [| now congruence].
    now do 2 econstructor 1; [eassumption.. | congruence].
  - inversion H23 as [[| a2' a3 b2' b3 tr2'' tr3' H2' H3 -> -> Hbisim23]]; [now congruence |].
    constructor; econstructor 2; [eassumption | eassumption | congruence.. |].
    eapply CIH; [eassumption |].
    now congruence.
Qed.