(** * BC2b: Inne kwantyfikatory? [TODO] *)

From Typonomikon Require Export BC2a.

(** Poznaliśmy jak dotąd trzy kwantyfikatory: uniwersalny ([forall]), egzystencjalny
    ([exists]) oraz unikalny, który był zdefiniowany za pomocą dwóch poprzednich
    oraz relacji równości ([=]).

    Skoro mogliśmy zdefiniować nowy kwantyfikator ze starych, to należy zadać
    sobie pytanie: czy istnieją jeszcze jakieś inne kwantyfikatory? I czy są
    one ciekawe?

    Odpowiedź na pierwsze pytanie brzmi: tak, i to nieskończenie wiele. Na drugie
    zaś: większość z nich nie jest zbyt ciekawa. Nie na tyle, żeby o nich tutaj
    wspominać. *)

(** * Kwantyfikator [xor]owy *)

(** Zauważmy, że kwantyfikator egzystencjalny jest podobny do "nieskończonej"
    dysjunkcji: [exists x : A, P x] znaczyłoby to samo, co [P x_0 \/ P x_1 \/ ...],
    gdyby rzecz jasna dało się takie nieskończenie długaśne zdanie zapisać. Ale
    się nie da - i dlatego właśnie mamy kwantyfikator egzystencjalny.

    W poprzednim podrozdziale poznaliśmy spójnik [xor], który możemy interpretować
    jako polskie "albo". [xor P Q] znaczy "albo zachodzi P (i nie zachodzi Q), albo
    zachodzi Q (i nie zachodzi P)", a zatem [xor] to wariant zwykłej dysjunkcji [\/],
    który jednak wyklucza możliwość zajścia więcej niż jednego ze swoich członów.

    Nieco sztucznym, acz potencjalnie ciekawym, kwantyfikatorem może być
    "kwantyfikator xorowy", który działa jak nieskończony [xor] - ma się
    on do [xor]a tak, jak kwantyfikator egzystencjalny do dysjunkcji. Zdefiniuj
    ten kwantyfikator, a następnie sprawdź, czy ma jakieś ciekawe właściwości. *)

(* begin hide *)
Definition qxor {A : Type} (P : A -> Prop) : Prop :=
  exists x : A, P x /\ forall y : A, x <> y -> ~ P y.
(* end hide *)

Lemma ex_qxor :
  forall {A : Type} (P : A -> Prop),
    qxor P -> ex P.
(* begin hide *)
Proof.
  intros A P (x & p & _).
  exists x. assumption.
Qed.
(* end hide *)

Lemma qxor_True_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ qxor (fun _ : A => True).
(* begin hide *)
Proof.
  intros A x y Hneq (z & _ & H).
  apply (H x).
  - intros ->. apply (H y); trivial.
  - trivial.
Qed.
(* end hide *)

Lemma qxor_False :
  forall A : Type,
    ~ qxor (fun _ : A => False).
(* begin hide *)
Proof.
  intros A (z & e & _).
  assumption.
Qed.
(* end hide *)

(** * Kwantyfikatory liczące (TODO) *)

(** Tutaj o kwantyfikatorach w stylu "co najmniej dwa", "dokładnie pięć", etc. *)

(** * Jakich kwantyfikatorów nie da się wyrazić w logice pierwszego rzędu? (TODO) *)

(** Tutaj o kwantyfikatorach, których nie da się wyrazić, np. "skończenie wiele",
    "większość", etc. *)