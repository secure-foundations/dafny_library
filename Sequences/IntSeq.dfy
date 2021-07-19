include "../NativeTypes.dfy"
include "../Nonlinear_Arithmetic/Power.dfy"
include "Seq.dfy"

module IntSeq {

  import opened NativeTypes
  import opened Power
  import opened Seq

  const BASE: int := BASE_32
  type BaseType = i | 0 <= i < BASE

  //////////////////////////////////////////////////////////////////////////////
  //
  // to_nat definitions and lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  function method {:opaque} to_nat(xs: seq<BaseType>): nat
  {
    if |xs| == 0 then 0
    else to_nat(drop_last(xs)) + last(xs) * power(BASE, |xs| - 1)
  }

  lemma lemma_to_nat_len_1(xs: seq<BaseType>)
    requires |xs| == 1
    ensures to_nat(xs) == xs[0]
  {
    reveal to_nat();
    reveal power();
  }

  lemma lemma_to_nat_len_2(xs: seq<BaseType>)
    requires |xs| == 2
    ensures to_nat(xs) == xs[0] + xs[1] * BASE
  {
    reveal to_nat();
    lemma_to_nat_len_1(drop_last(xs));
    reveal power();
  }


}
