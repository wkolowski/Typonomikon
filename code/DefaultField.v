Class Test : Type := MkTest
{
    wut : nat := 5;
}.

Check MkTest.

Instance Test_1 : Test.
Proof.
  split.
Abort.