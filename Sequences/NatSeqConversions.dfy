include "NatSeq.dfy"

abstract module NatSeqConversions refines NatSeq {

  import NatSeq1
  import NatSeq2

  function {:opaque} to_lower_base(xs: seq<NatSeq1.uint>): seq<NatSeq2.uint>
  {
    if xs == [] then []
    else NatSeq2.to_seq(first(xs)) + to_lower_base(drop_first(xs))
  }

  function {:opaque} to_higher_base(xs: seq<NatSeq2.uint>): seq<NatSeq1.uint>
  {
    if xs == [] then []
    else
      var n: nat :| NatSeq1.BASE() == power(NatSeq2.BASE(), n) && n > 1;
      if |xs| < n then
        NatSeq2.lemma_seq_nat_bound(xs);
        lemma_power_strictly_increases(NatSeq2.BASE(), |xs|, n);
        [NatSeq2.to_nat(xs) as NatSeq1.uint]
      else
        NatSeq2.lemma_seq_nat_bound(xs[..n]);
        lemma_mod_sub_multiples_vanish_auto();
        [NatSeq2.to_nat(xs[..n]) as NatSeq1.uint] + to_higher_base(xs[n..])
  }

}
