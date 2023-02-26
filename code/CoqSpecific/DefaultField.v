Class Test : Type := MkTest
{
  wut : nat := 5;
}.

#[export]
Instance Test_1 : Test.
Proof.
  split.
Defined.