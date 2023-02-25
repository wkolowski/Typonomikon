(**
  Reprezentacja prostego Ledgera w stylu UTxO.
*)

Require Import List.
Import ListNotations.

Record Coin : Type := coin
{
  uncoin : nat;
}.

Parameter Addr : Type.

Record Out : Type := out
{
  adr : Addr;
  val : Coin;
}.

Inductive Tx : Type := tx
{
  ins  : list Inp;
  outs : list Out;
}

with Inp : Type := inp
{
  _ : Tx;
  _ : nat;
}.

Definition Ledger : Type := list Tx.

Parameter a0 a1 a2 : Addr.

Definition t0 : Tx := tx [] [out a0 (coin 1000)].
Definition t1 : Tx := tx [inp t0 0] [out a1 (coin 50); out a0 (coin 950)].
Definition t2 : Tx := tx [inp t1 0] [out a2 (coin 50)].

Definition l : Ledger := [t0; t1; t2].

Definition UTxO : Type := list (Inp * Out).

Record Wallet : Type :=
{
  ours : list Addr;
  utxo : UTxO;
}.

Lemma Coin_eq_dec :
  forall c1 c2 : Coin, {c1 = c2} + {c1 <> c2}.
Proof.
  do 2 decide equality.
Defined.

Parameter Addr_eq_dec :
  forall a1 a2 : Addr, {a1 = a2} + {a1 <> a2}.

Lemma Out_eq_dec :
  forall o1 o2 : Out, {o1 = o2} + {o1 <> o2}.
Proof.
  decide equality.
  - apply Coin_eq_dec.
  - apply Addr_eq_dec.
Defined.

Lemma Tx_eq_dec :
  forall t1 t2 : Tx, {t1 = t2} + {t1 <> t2}
with Inp_eq_dec :
  forall i1 i2 : Inp, {i1 = i2} + {i1 <> i2}.
Proof.
  - decide equality.
    + apply list_eq_dec, Out_eq_dec.
    + apply list_eq_dec, Inp_eq_dec.
  - do 2 decide equality.
Defined.

Lemma Ledger_eq_dec :
  forall l1 l2 : Ledger, {l1 = l2} + {l1 <> l2}.
Proof.
  apply list_eq_dec, Tx_eq_dec.
Defined.

Definition restrictDomain (ins : list Inp) (utxo : UTxO) : UTxO :=
  filter (fun '(i, _) => if in_dec Inp_eq_dec i ins then true else false) utxo.

Definition subtractDomain (ins : list Inp) (utxo : UTxO) : UTxO :=
  filter (fun '(i, _) => if in_dec Inp_eq_dec i ins then false else true) utxo.

Definition restrictRange (utxo : UTxO) (addrs : list Addr) : UTxO :=
  filter (fun '(_, o) => if in_dec Addr_eq_dec (adr o) addrs then true else false) utxo.

Fixpoint imap {A B : Type} (f : nat -> A -> B) (l : list A) : list B :=
match l with
| [] => []
| h :: t => f 0 h :: imap (fun n a => f (S n) a) t
end.

Definition txouts (tx : Tx) : UTxO :=
  imap (fun n o => (inp tx n, o)) (outs tx).

Definition txins (tx : Tx) : list Inp := ins tx.

Definition apply (tx : Tx) (w : Wallet) : Wallet :=
{|
  ours := ours w;
  utxo := subtractDomain (txins tx) (utxo w) ++ restrictRange (txouts tx) (ours w);
|}.

Definition correctWallet (w : Wallet) : Prop :=
  Forall (fun '(_, o) => In (adr o) (ours w)) (utxo w).

Definition EmptyWallet (addrs : list Addr) : Wallet :=
{|
  ours := addrs;
  utxo := [];
|}.

Fixpoint balance' (utxo : UTxO) : nat :=
match utxo with
| [] => 0
| (_, o) :: utxo' => uncoin (val o) + balance' utxo'
end.

Definition balance (utxo : UTxO) : Coin :=
  coin (balance' utxo).

Record CachedWallet : Type :=
{
  wallet  : Wallet;
  cachedBalance : Coin;
}.

Definition cachesCorrectly (cw : CachedWallet) : Prop :=
  balance (utxo (wallet cw)) = cachedBalance cw.

Definition cachedApply (tx : Tx) (cw : CachedWallet) : CachedWallet :=
  let w' := apply tx (wallet cw) in
{|
  wallet  := w';
  cachedBalance := balance (utxo w');
|}.

Definition EmptyCachedWallet (addrs : list Addr) : CachedWallet :=
{|
  wallet := EmptyWallet addrs;
  cachedBalance := coin 0;
|}.