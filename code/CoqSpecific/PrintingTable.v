Module xd.

Record R : Type := MkR
{
  field : unit;
}.

Print Tables.
Print Table Printing Record.
Print Table Printing Coercion.
Print Table Printing If.
Print Table Printing Let.
Print Table Printing Record.
Print Table Printing Constructor.

Local Unset Printing Records.

Goal forall u1 u2 : unit, MkR u1 = MkR u2.
Abort.

End xd.

Import xd.

Goal forall u1 u2 : unit, MkR u1 = MkR u2.
Abort.