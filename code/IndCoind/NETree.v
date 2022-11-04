CoInductive NETree (A : Type) : Type :=
{
  root  : A;
  left  : option (NETree A);
  right : option (NETree A);
}.

Arguments root  {A} _.
Arguments left  {A} _.
Arguments right {A} _.

Inductive WFL {A : Type} : NETree A -> Prop :=
| WFL_None : forall {t : NETree A}, left t = None -> WFL t
| WFL_Some : forall {t t' : NETree A}, left t = Some t' -> WFL t' ->
 WFL t.

Arguments WFL_None {A t} _.

CoInductive WF {A : Type} (t : NETree A) : Prop :=
{
    rootWF : WFL t;
    rightWF : right t = None \/ exists t' : NETree A, right t = Some t' /\ WF t'
}.

(* TODO: fix *)
(*
Fixpoint leftmost {A : Type} {t : NETree A} (wf : WFL t) {struct t} : A :=
match left t with
| None => root t
| Some t' =>
match wf with
| WFL_None _ => root t
| WFL_Some _ wf' => leftmost wf'
end.
*)