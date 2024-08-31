Module Test.

Context
  (Account Token Signature : Type).

Record State : Type :=
{
  balances : Account -> Token -> nat;
  time : nat;
}.

Variant TxType : Type :=
| CreateToken (id : Token) (total_supply : nat)
| Transfer (destination : Account) (token : Token) (amount : nat).

Record Tx : Type :=
{
  author : Account;
  tx_type : TxType;
  signature : Signature;
}.

End Test.

Print Test.