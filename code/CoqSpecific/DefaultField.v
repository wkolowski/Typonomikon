Class Test : Type := MkTest
{
    wut : nat := 5;
}.

Check MkTest.

Instance Test_1 : Test.
Proof.
  split.
Defined.

Check Test_1.
Print Test_1.
Check Test.
Print Test.
Check MkTest.
Print MkTest.
Check wut.
Print wut.