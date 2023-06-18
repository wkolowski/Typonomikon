Module List.

Inductive List (A : Type) : Type :=
| Nil : List A
| Cons : A -> List A -> List A.

Arguments Nil  {A}.
Arguments Cons {A} _ _.

Module Constructor.

Inductive Constructor : Type :=
| Nil
| Cons.

End Constructor.

Import Constructor.

Module Args.

Inductive Args (A X : Type) : Constructor -> Type :=
| Nil : Args A X Nil
| Cons : A -> X -> Args A X Cons.

End Args.

End List.

Import List.

(*
Print List.Constructor.
Check Nil.
Check Constructor.Nil.
Print List.Args.
Check Args.Nil.
*)