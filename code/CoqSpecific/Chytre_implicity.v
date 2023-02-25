Inductive ColistF {X A : Type} : Type :=
| ConilF  : ColistF
| CoconsF : A -> X -> ColistF.

Arguments ColistF : clear implicits.