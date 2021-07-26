include "NatSeq.dfy"

abstract module NatSeqConversions refines NatSeq {

  function method BASE1(): nat
		ensures BASE1() > 1
  type uint1 = i: int | 0 <= i < BASE1()

  function method BASE2(): nat
		ensures BASE2() > 1
  type uint2 = i: int | 0 <= i < BASE2()

  function method BASE(): nat { BASE2() }

  function {:opaque} to_smaller_base(xs: seq<uint1>): seq<uint2>
    requires exists n :: BASE1() == power(BASE2(), n) && n > 1
  {
    if xs == [] then []
    else to_seq(first(xs)) + to_smaller_base(drop_first(xs))
  }

  function {:opaque} to_larger_base(xs: seq<uint2>): seq<uint1>
    requires exists n :: BASE1() == power(BASE2(), n) && n > 1
  {
    if xs == [] then []
    else
      var n: nat :| BASE1() == power(BASE2(), n) && n > 1;
      if |xs| < n then
        lemma_seq_nat_bound(xs);
        lemma_power_strictly_increases(BASE2(), |xs|, n);
        [to_nat(xs) as uint1]
      else
        lemma_seq_nat_bound(xs[..n]);
        lemma_mod_sub_multiples_vanish_auto();
        [to_nat(xs[..n]) as uint1] + to_larger_base(xs[n..])
  }

}
