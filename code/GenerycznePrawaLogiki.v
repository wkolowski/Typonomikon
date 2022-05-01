Inductive Dir : Type :=
| L
| R.

Inductive Connective : Type :=
| Impl
| Or
| And
| Iff
| Xor
| Nimpl
| Nor
| Nand.

Definition con (c : Connective) (P Q : Prop) : Prop :=
match c with
| Impl  => P -> Q
| Or    => P \/ Q
| And   => P /\ Q
| Iff   => P <-> Q
| Xor   => (P /\ ~ Q) \/ (~ P /\ Q)
| Nimpl => ~ (P -> Q)
| Nor   => ~ (P \/ Q)
| Nand  => ~ (P /\ Q)
end.

Inductive Constant : Type :=
| Top
| Bot.

Definition const (c : Constant) : Prop :=
match c with
| Top => True
| Bot => False
end.

Inductive Law1 : Type :=
| IsC (c : Prop)
| IsArg
| IsNeg.

Definition law1 (l : Law1) (C : Prop -> Prop) : Prop :=
match l with
| IsC c => forall P : Prop, C P <-> c
| IsArg => forall P : Prop, C P <-> P
| IsNeg => forall P : Prop, C P <-> ~ P
end.

Inductive ReflIdem : Type :=
| Refl
| Irrefl
| Idempotent
| Antiidempotent.

Definition reflIdem (ri : ReflIdem) (C : Prop -> Prop -> Prop) : Prop :=
match ri with
| Refl => law1 (IsC True) (fun P => C P P)
| Irrefl => law1 (IsC False) (fun P => C P P)
| Idempotent => law1 IsArg (fun P => C P P)
| Antiidempotent => law1 IsNeg (fun P => C P P)
end.

Eval simpl in reflIdem Irrefl (con Xor).
Check ltac:(cbn; tauto) : reflIdem Irrefl (con Xor).

Definition neutr (d : Dir) (N : Prop) (C : Prop -> Prop -> Prop) : Prop :=
match d with
| L => law1 IsArg (C N)
| R => law1 IsArg (fun P => C P N)
end.

Definition antineutr (d : Dir) (N : Prop) (C : Prop -> Prop -> Prop) : Prop :=
match d with
| L => law1 IsNeg (C N)
| R => law1 IsNeg (fun P => C P N)
end.

Definition absorb (d : Dir) (A : Prop) (C : Prop -> Prop -> Prop) : Prop :=
match d with
| L => law1 (IsC A) (C A)
| R => law1 (IsC A) (fun P => C P A)
end.

Eval simpl in absorb L False (con Xor).

Inductive DistrLaw : Type :=
| DistrLaw' (d : Dir) (c1 c2 : Connective).

Definition distrLaw (d : DistrLaw) : Prop :=
match d with
| DistrLaw' L c1 c2 =>
    forall P Q R : Prop, con c1 P (con c2 Q R) <-> con c2 (con c1 P Q) (con c1 P R)
| _ => False
end.

Eval simpl in distrLaw (DistrLaw' L Or And).
Check ltac:(cbn; tauto) : distrLaw (DistrLaw' L Or And).

Definition distrL (C D : Prop -> Prop -> Prop) : Prop :=
  forall P Q R : Prop, C P (D Q R) <-> D (C P Q) (C P R).

Definition distrR (C D : Prop -> Prop -> Prop) : Prop :=
  forall P Q R : Prop, C (D P Q) R <-> D (C P R) (C Q R).

Check ltac:(compute; tauto) : distrL or and.
Check ltac:(compute; tauto) : distrR and or.
Eval compute in distrL or and.

Inductive Law2 : Type :=
| Comm.

Definition law2 (l : Law2) (Con : Prop -> Prop -> Prop) : Prop :=
match l with
| Comm => forall P Q : Prop, Con P Q <-> Con Q P
end.

Inductive Law3 : Type :=
| Assoc.

Definition law3 (l : Law3) (Con : Prop -> Prop -> Prop) : Prop :=
match l with
| Assoc => forall P Q R : Prop, Con (Con P Q) R <-> Con P (Con Q R)
end.

Module wut.

Inductive LAW : Type :=
| Neutr (d : Dir) (c : Constant) (naive : bool)
| Antineutr (d : Dir) (c : Constant) (naive : bool)
| Absorb (d : Dir) (c : Constant) (naive : bool)
| Reflexive
| Irreflexive
| Idempotent
| Antiidempotent
| Commutative
| Associative
| Monotone (d : Dir)
| Distributive (d : Dir) (Con : Connective).

Definition unconst (c : Constant) (P : Prop) : Prop :=
match c with
| Top => P
| Bot => ~ P
end.

Definition law (l : LAW) (Con : Connective) : Prop :=
match l with
| Neutr L c true => forall P : Prop, con Con (const c) P <-> P
| Neutr R c true => forall P : Prop, con Con P (const c) <-> P
| Neutr L c false => forall P Q : Prop, unconst c P -> con Con P Q <-> Q
| Neutr R c false => forall P Q : Prop, unconst c Q -> con Con P Q <-> P
| Antineutr L c true => forall P : Prop, con Con (const c) P <-> ~ P
| Antineutr R c true => forall P : Prop, con Con P (const c) <-> ~ P
| Antineutr L c false => forall P Q : Prop, unconst c P -> con Con P Q <-> ~ Q
| Antineutr R c false => forall P Q : Prop, unconst c Q -> con Con P Q <-> ~ P
| Absorb L c true => forall P : Prop, con Con (const c) P <-> const c
| Absorb R c true => forall P : Prop, con Con P (const c) <-> const c
| Absorb L c false => forall P Q : Prop, unconst c P -> con Con P Q <-> True
| Absorb R c false => forall P Q : Prop, unconst c Q -> con Con P Q <-> True
| _ => False
end.

(* | Antineutr (d : Dir) (c : Constant) (naive : bool)
| Absorb (d : Dir) (c : Constant) (naive : bool)
| Reflexive
| Irreflexive
| Idempotent
| Antiidempotent
| Commutative
| Associative
| Monotone (d : Dir)
| Distributive (d : Dir) (Con : Connective). *)

Eval simpl in law (Neutr L Top true) Impl.
Eval simpl in law (Absorb L Top true) Or.
Eval simpl in law (Absorb L Top false) Or.
Eval simpl in law (Neutr L Bot false) Or.

End wut.