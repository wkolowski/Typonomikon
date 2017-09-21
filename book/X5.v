(** * X5: Relacje *)

(** Prerekwizyty:
    - definicje induktywne
    - klasy (?) *)

(** W tym rozdziale zajmiemy się badaniem relacji. Poznamy podstawowe rodzaje
    relacji, ich właściwości, a także zależności i przekształcenia między
    nimi. Rozdział będzie raczej matematyczny. *)

(** * Relacje *)

(** Zacznijmy od przypomnienia klasyfikacji zdań, predykatów i relacji:
    - zdania to obiekty typu [Prop]. Twierdzą one coś na temat świata:
      "niebo jest niebieskie", [P -> Q] etc. W uproszczeniu możemy myśleć o
      nich, że są prawdziwe lub fałszywe, co nie znaczy wcale, że można to
      automatycznie rozstrzygnąć. Udowodnienie zdania [P] to skonstruowanie
      obiektu [p : P]. W Coqu zdania służą nam do podawania specyfikacji
      programów. W celach klasyfikacyjnych możemy uznać, że są to funkcje
      biorące zero argumentów i zwracające [Prop].
    - predykaty to funkcje typu [A -> Prop] dla jakiegoś [A : Type]. Można
      za ich pomocą przedstawiać stwierdzenia na temat właściwości obiektów:
      "liczba 5 jest parzysta", [odd 5]. Dla niektórych argumentów zwracane
      przez nie zdania mogą być prawdziwe, a dla innych już nie. Dla celów
      klasyfikacji uznajemy je za funkcje biorące jeden argument i zwracające
      [Prop].
    - relacje to funkcje biorące dwa lub więcej argumentów, niekoniecznie
      o takich samych typach, i zwracające [Prop]. Służą one do opisywania
      zależności między obiektami, np. "Grażyna jest matką Karyny",
      [Permutation (l ++ l') (l' ++ ')]. Niektóre kombinacje obiektów mogą
      być ze sobą w relacji, tzn. zdanie zwracane dla nich przez relację
      może być prawdziwe, a dla innych nie. *)

(** * Heterogeniczne relacje binarne *)

Definition hrel (A B : Type) : Type := A -> B -> Prop.

(** Najważniejszym rodzajem relacji są relacje binarne, czyli relacje
    biorące dwa argumenty. To właśnie im poświęcimy ten rozdział, pominiemy
    zaś relacje biorące trzy i więcej argumentów. *)

Class LeftUnique {A B : Type} (R : hrel A B) : Prop :=
{
    left_unique : forall (a a' : A) (b : B), R a b -> R a' b -> a = a'
}.

Class RightUnique {A B : Type} (R : hrel A B) : Prop :=
{
    right_unique : forall (a : A) (b b' : B), R a b -> R a b' -> b = b'
}.

Class LeftTotal {A B : Type} (R : hrel A B) : Prop :=
{
    left_total : forall a : A, exists b : B, R a b
}.

Class RightTotal {A B : Type} (R : hrel A B) : Prop :=
{
    right_total : forall b : B, exists a : A, R a b
}.

(** * Homogeniczne relacje binarne *)

Definition rel (A : Type) : Type := hrel A A.

Class Reflexive {A : Type} (R : rel A) : Prop :=
{
    reflexive : forall x : A, R x x
}.

Class Irreflexive {A : Type} (R : rel A) : Prop :=
{
    irreflexive : exists x : A, ~ R x x
}.

Class Antireflexive {A : Type} (R : rel A) : Prop :=
{
    antireflexive : forall x : A, ~ R x x
}.

Class WeakReflexive {A : Type} (R : rel A) : Prop :=
{
    wreflexive : forall x y : A, R x y -> x = y
}.

Class Symmetric {A : Type} (R : rel A) : Prop :=
{
    symmetric : forall x y : A, R x y -> R y x
}.

Class Asymmetric {A : Type} (R : rel A) : Prop :=
{
    asymmetric : exists x y : A, R x y /\ ~ R y x
}.

Class Antisymmetric {A : Type} (R : rel A) : Prop :=
{
    antisymmetric : forall x y : A, R x y -> ~ R x y
}.

Class WeakAntisymmetric {A : Type} (R : rel A) : Prop :=
{
    wantisymmetric : forall x y : A, R x y -> R y x -> x = y
}.

Class Transitive {A : Type} (R : rel A) : Prop :=
{
    transitive : forall x y z : A, R x y -> R y z -> R x z
}.

Class Total {A : Type} (R : rel A) : Prop :=
{
    total : forall x y : A, R x y \/ R y x
}.

Class Trichotomous {A : Type} (R : rel A) : Prop :=
{
    trichotomous : forall x y : A, R x y \/ x = y \/ R y x
}.
