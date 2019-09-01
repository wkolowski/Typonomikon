(** * F1: Koindukcja i korekursja - pusty *)

(** Chwilowo nic tu nie ma. *)

(* begin hide *)

(** Pamiętać o tym, że przy negatywnej koindukcji kryterium ścisłej
    pozytywnośći też obowiązuje. Powody są mniej więcej takie jak dla
    typów induktywnych. *)

Fail CoInductive wut : Type :=
{
    haha : wut -> Prop;
}.

(** Ciężko mi jednak stwierdzić w tej chwili, czy jest jakiś odpowiednik
    problemów z nieterminacją. *)

(* end hide *)