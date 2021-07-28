include "NatSeq.dfy"

abstract module NatSeqConversions refines NatSeq {

  import NatSeq1
  import NatSeq2

  function N(): nat
  {
    var n: nat :| NatSeq1.BASE() == power(NatSeq2.BASE(), n) && n > 1;
    n
  }

  function {:opaque} to_lower_base(xs: seq<NatSeq1.uint>): seq<NatSeq2.uint>
  {
    if |xs| == 0 then []
    else NatSeq2.to_seq_with_len(first(xs), N()) + to_lower_base(drop_first(xs))
  }

  function {:opaque} to_higher_base(xs: seq<NatSeq2.uint>): seq<NatSeq1.uint>
  {
    if |xs| == 0 then []
    else
      if |xs| < N() then
        NatSeq2.lemma_seq_nat_bound(xs);
        lemma_power_strictly_increases(NatSeq2.BASE(), |xs|, N());
        [NatSeq2.to_nat(xs) as NatSeq1.uint]
      else
        NatSeq2.lemma_seq_nat_bound(xs[..N()]);
        lemma_mod_sub_multiples_vanish_auto();
        [NatSeq2.to_nat(xs[..N()]) as NatSeq1.uint] + to_higher_base(xs[N()..])
  }

  lemma lemma_lower_base_to_nat(xs: seq<NatSeq1.uint>)
    ensures NatSeq2.to_nat(to_lower_base(xs)) == NatSeq1.to_nat(xs)
  {
    reveal NatSeq1.to_nat();
    reveal NatSeq2.to_nat();
    reveal to_lower_base();
    if |xs| > 0 {
      calc {
        NatSeq2.to_nat(to_lower_base(xs));
        NatSeq2.to_nat(NatSeq2.to_seq_with_len(first(xs), N()) + to_lower_base(drop_first(xs)));
          { NatSeq2.lemma_seq_prefix(NatSeq2.to_seq_with_len(first(xs), N())
            + to_lower_base(drop_first(xs)), N()); }
        NatSeq2.to_nat(NatSeq2.to_seq_with_len(first(xs), N())) + NatSeq2.to_nat(to_lower_base(drop_first(xs))) * power(NatSeq2.BASE(), N());
          {
            NatSeq2.lemma_to_seq_with_len_eq_to_seq(first(xs), N());
            NatSeq2.lemma_nat_seq_nat(first(xs));
            lemma_lower_base_to_nat(drop_first(xs));
          }
        first(xs) + NatSeq1.to_nat(drop_first(xs)) * power(NatSeq2.BASE(), N());
          { assert power(NatSeq2.BASE(), N()) == NatSeq1.BASE(); }
        NatSeq1.to_nat(xs);
      }
    }
  }

  lemma lemma_higher_base_to_nat(xs: seq<NatSeq2.uint>)
    ensures NatSeq1.to_nat(to_higher_base(xs)) == NatSeq2.to_nat(xs)
  {
    reveal NatSeq1.to_nat();
    reveal NatSeq2.to_nat();
    reveal to_higher_base();
    if |xs| >= N() {
      calc {
        NatSeq1.to_nat(to_higher_base(xs));
          { NatSeq2.lemma_seq_nat_bound(xs[..N()]); }
        NatSeq1.to_nat([NatSeq2.to_nat(xs[..N()]) as NatSeq1.uint] + to_higher_base(xs[N()..]));
        NatSeq2.to_nat(xs[..N()]) as NatSeq1.uint + NatSeq1.to_nat(to_higher_base(xs[N()..])) * NatSeq1.BASE();
          { lemma_higher_base_to_nat(xs[N()..]); }
        NatSeq2.to_nat(xs[..N()]) + NatSeq2.to_nat(xs[N()..]) * power(NatSeq2.BASE(), N());
          { NatSeq2.lemma_seq_prefix(xs, N()); }
        NatSeq2.to_nat(xs);
      }
    }
  }

  lemma lemma_to_lower_base_is_injective(xs: seq<NatSeq1.uint>,
                                         ys: seq<NatSeq1.uint>)
    requires |xs| == |ys|
    requires NatSeq1.to_nat(xs) == NatSeq1.to_nat(ys)
    ensures to_lower_base(xs) == to_lower_base(ys)
  {
    calc ==> {
      to_lower_base(xs) != to_lower_base(ys);
        { NatSeq1.lemma_seq_neq(xs, ys, |xs|); }
      NatSeq1.to_nat(xs) != NatSeq1.to_nat(ys);
      false;
    }
  }

  lemma lemma_to_higher_base_is_injective(xs: seq<NatSeq2.uint>,
                                          ys: seq<NatSeq2.uint>)
    requires |xs| == |ys|
    requires NatSeq2.to_nat(xs) == NatSeq2.to_nat(ys)
    ensures to_higher_base(xs) == to_higher_base(ys)
  {
    calc ==> {
      to_higher_base(xs) != to_higher_base(ys);
        { NatSeq2.lemma_seq_neq(xs, ys, |xs|); }
      NatSeq2.to_nat(xs) != NatSeq2.to_nat(ys);
      false;
    }
  }

  lemma lemma_to_lower_base_is_injective_inv(xs: seq<NatSeq1.uint>,
                                             ys: seq<NatSeq1.uint>)
    requires to_lower_base(xs) == to_lower_base(ys)
    ensures NatSeq1.to_nat(xs) == NatSeq1.to_nat(ys)
  {
    lemma_lower_base_to_nat(xs);
    lemma_lower_base_to_nat(ys);
  }

  lemma lemma_to_higher_base_is_injective_inv(xs: seq<NatSeq2.uint>,
                                              ys: seq<NatSeq2.uint>)
    requires to_higher_base(xs) == to_higher_base(ys)
    ensures NatSeq2.to_nat(xs) == NatSeq2.to_nat(ys)
  {
    lemma_higher_base_to_nat(xs);
    lemma_higher_base_to_nat(ys);
  }

}
