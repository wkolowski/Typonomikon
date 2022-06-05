Inductive TernarySystem : Type :=
| A : TernarySystem
| B : TernarySystem
| C : TernarySystem
| mid : TernarySystem -> TernarySystem -> TernarySystem.

