include "NatSeq.dfy"

abstract module NatSeqConversions refines NatSeq {

  import NatSeq1
  import NatSeq2

  /* BASE2() to the power of P() is BASE1(). */
  function P(): nat
  {
    var n: nat :| NatSeq1.BASE() == power(NatSeq2.BASE(), n) && n > 1;
    n
  }

  /* Converts a sequence from BASE1() to BASE2(). */
  function {:opaque} to_lower_base(xs: seq<NatSeq1.uint>): seq<NatSeq2.uint>
  {
    if |xs| == 0 then []
    else NatSeq2.to_seq_with_len(first(xs), P()) + to_lower_base(drop_first(xs))
  }

  /* Converts a sequence from BASE2() to BASE1(). */
  function {:opaque} to_higher_base(xs: seq<NatSeq2.uint>): seq<NatSeq1.uint>
  {
    if |xs| == 0 then []
    else
      if |xs| < P() then
        NatSeq2.lemma_seq_nat_bound(xs);
        lemma_power_strictly_increases(NatSeq2.BASE(), |xs|, P());
        [NatSeq2.to_nat(xs) as NatSeq1.uint]
      else
        NatSeq2.lemma_seq_nat_bound(xs[..P()]);
        lemma_mod_sub_multiples_vanish_auto();
        [NatSeq2.to_nat(xs[..P()]) as NatSeq1.uint] + to_higher_base(xs[P()..])
  }

  /* Sequence conversion from BASE1() to BASE2() does not change its nat
  representation. */
  lemma lemma_lower_base_to_nat(xs: seq<NatSeq1.uint>)
    ensures NatSeq2.to_nat(to_lower_base(xs)) == NatSeq1.to_nat(xs)
  {
    reveal NatSeq1.to_nat();
    reveal NatSeq2.to_nat();
    reveal to_lower_base();
    if |xs| > 0 {
      calc {
        NatSeq2.to_nat(to_lower_base(xs));
        NatSeq2.to_nat(NatSeq2.to_seq_with_len(first(xs), P()) + to_lower_base(drop_first(xs)));
          { NatSeq2.lemma_seq_prefix(NatSeq2.to_seq_with_len(first(xs), P())
            + to_lower_base(drop_first(xs)), P()); }
        NatSeq2.to_nat(NatSeq2.to_seq_with_len(first(xs), P())) + NatSeq2.to_nat(to_lower_base(drop_first(xs))) * power(NatSeq2.BASE(), P());
          {
            NatSeq2.lemma_to_seq_with_len_eq_to_seq(first(xs), P());
            NatSeq2.lemma_nat_seq_nat(first(xs));
            lemma_lower_base_to_nat(drop_first(xs));
          }
        first(xs) + NatSeq1.to_nat(drop_first(xs)) * power(NatSeq2.BASE(), P());
          { assert power(NatSeq2.BASE(), P()) == NatSeq1.BASE(); }
        NatSeq1.to_nat(xs);
      }
    }
  }

  /* Sequence conversion from BASE2() to BASE1() does not change its nat
  representation. */
  lemma lemma_higher_base_to_nat(xs: seq<NatSeq2.uint>)
    ensures NatSeq1.to_nat(to_higher_base(xs)) == NatSeq2.to_nat(xs)
  {
    reveal NatSeq1.to_nat();
    reveal NatSeq2.to_nat();
    reveal to_higher_base();
    if |xs| >= P() {
      calc {
        NatSeq1.to_nat(to_higher_base(xs));
          { NatSeq2.lemma_seq_nat_bound(xs[..P()]); }
        NatSeq1.to_nat([NatSeq2.to_nat(xs[..P()]) as NatSeq1.uint] + to_higher_base(xs[P()..]));
        NatSeq2.to_nat(xs[..P()]) as NatSeq1.uint + NatSeq1.to_nat(to_higher_base(xs[P()..])) * NatSeq1.BASE();
          { lemma_higher_base_to_nat(xs[P()..]); }
        NatSeq2.to_nat(xs[..P()]) + NatSeq2.to_nat(xs[P()..]) * power(NatSeq2.BASE(), P());
          { NatSeq2.lemma_seq_prefix(xs, P()); }
        NatSeq2.to_nat(xs);
      }
    }
  }

  /* to_lower_base is injective. */
  lemma lemma_to_lower_base_is_injective(xs: seq<NatSeq1.uint>,
                                         ys: seq<NatSeq1.uint>)
    requires to_lower_base(xs) == to_lower_base(ys)
    requires |xs| == |ys|
    ensures xs == ys
  {
    lemma_lower_base_to_nat(xs);
    lemma_lower_base_to_nat(ys);
    assert NatSeq1.to_nat(xs) == NatSeq1.to_nat(ys);
    NatSeq1.lemma_seq_eq(xs, ys);
  }

  /* to_higher_base is injective. */
  lemma lemma_to_higher_base_is_injective(xs: seq<NatSeq2.uint>,
                                          ys: seq<NatSeq2.uint>)
    requires to_higher_base(xs) == to_higher_base(ys)
    requires |xs| == |ys|
    ensures xs == ys
  {
    lemma_higher_base_to_nat(xs);
    lemma_higher_base_to_nat(ys);
    assert NatSeq2.to_nat(xs) == NatSeq2.to_nat(ys);
    NatSeq2.lemma_seq_eq(xs, ys);
  }

}
