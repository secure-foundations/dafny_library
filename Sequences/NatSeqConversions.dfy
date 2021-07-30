include "NatSeq.dfy"

abstract module NatSeqConversions refines NatSeq {

  import SmallBound
  import LargeBound

  /* SmallBound.BOUND() to the power of E() is LargeBound.BOUND(). */
  function method E(): nat
    ensures power(SmallBound.BOUND(), E()) == LargeBound.BOUND()
  {
    lemma_div_basics_auto();
    lemma_power_multiplies_auto();
    lemma_fundamental_div_mod(LargeBound.BITS(), SmallBound.BITS());
    LargeBound.BITS() / SmallBound.BITS()
  }

  lemma lemma_mod_eq_zero(x: nat, y: nat)
    requires x > 0 && y > 0
    requires x % y == 0
    ensures x >= y
  {
    calc ==> {
      x < y;
        { lemma_small_mod(x, y); }
      x % y == x;
      false;
    }
  }

  /* Converts a sequence from LargeBound.BOUND() to SmallBound.BOUND(). */
  function method {:opaque} to_smaller_base(xs: seq<LargeBound.uint>): (ys: seq<SmallBound.uint>)
    ensures |ys| == |xs| * E()
  {
    if |xs| == 0 then []
    else
      lemma_mul_is_distributive_add_other_way(E(), 1, |xs| - 1);
      SmallBound.from_nat_with_len(first(xs), E()) + to_smaller_base(drop_first(xs))
  }

  /* Converts a sequence from SmallBound.BOUND() to LargeBound.BOUND(). */
  function method {:opaque} to_larger_base(xs: seq<SmallBound.uint>): (ys: seq<LargeBound.uint>)
    requires |xs| % E() == 0
    ensures |ys| == |xs| / E()
  {
    if |xs| == 0 then lemma_div_basics_auto(); []
    else
      lemma_mod_eq_zero(|xs|, E());
      assert |xs| >= E();

      SmallBound.lemma_seq_nat_bound(xs[..E()]);
      lemma_mod_sub_multiples_vanish_auto();
      lemma_div_minus_one(|xs|, E());
      [SmallBound.to_nat(xs[..E()]) as LargeBound.uint] + to_larger_base(xs[E()..])
  }

  /* Sequence conversion from LargeBound.BOUND() to SmallBound.BOUND() does not
  change its nat representation. */
  lemma lemma_smaller_base_to_nat(xs: seq<LargeBound.uint>)
    ensures SmallBound.to_nat(to_smaller_base(xs)) == LargeBound.to_nat(xs)
  {
    reveal LargeBound.to_nat();
    reveal SmallBound.to_nat();
    reveal to_smaller_base();
    if |xs| > 0 {
      calc {
        SmallBound.to_nat(to_smaller_base(xs));
        SmallBound.to_nat(SmallBound.from_nat_with_len(first(xs), E()) + to_smaller_base(drop_first(xs)));
          { SmallBound.lemma_seq_prefix(SmallBound.from_nat_with_len(first(xs), E()) + to_smaller_base(drop_first(xs)), E()); }
        SmallBound.to_nat(SmallBound.from_nat_with_len(first(xs), E())) + SmallBound.to_nat(to_smaller_base(drop_first(xs))) * power(SmallBound.BOUND(), E());
          {
            SmallBound.lemma_from_nat_with_len_eq_from_nat(first(xs), E());
            SmallBound.lemma_nat_seq_nat(first(xs));
            lemma_smaller_base_to_nat(drop_first(xs));
          }
        first(xs) + LargeBound.to_nat(drop_first(xs)) * power(SmallBound.BOUND(), E());
          { assert power(SmallBound.BOUND(), E()) == LargeBound.BOUND(); }
        LargeBound.to_nat(xs);
      }
    }
  }

  /* Sequence conversion from SmallBound.BOUND() to LargeBound.BOUND() does not
  change its nat representation. */
  lemma lemma_larger_base_to_nat(xs: seq<SmallBound.uint>)
    requires |xs| % E() == 0
    ensures LargeBound.to_nat(to_larger_base(xs)) == SmallBound.to_nat(xs)
  {
    reveal LargeBound.to_nat();
    reveal SmallBound.to_nat();
    reveal to_larger_base();
    if |xs| > 0 {
      calc {
        LargeBound.to_nat(to_larger_base(xs));
          {
            lemma_mod_eq_zero(|xs|, E());
            lemma_mod_sub_multiples_vanish_auto();
            SmallBound.lemma_seq_nat_bound(xs[..E()]);
          }
        LargeBound.to_nat([SmallBound.to_nat(xs[..E()]) as LargeBound.uint] + to_larger_base(xs[E()..]));
          { lemma_larger_base_to_nat(xs[E()..]); }
        SmallBound.to_nat(xs[..E()]) + SmallBound.to_nat(xs[E()..]) * power(SmallBound.BOUND(), E());
          { SmallBound.lemma_seq_prefix(xs, E()); }
        SmallBound.to_nat(xs);
      }
    }
  }

  /* to_smaller_base is injective. */
  lemma lemma_to_smaller_base_is_injective(xs: seq<LargeBound.uint>,
                                         ys: seq<LargeBound.uint>)
    requires to_smaller_base(xs) == to_smaller_base(ys)
    requires |xs| == |ys|
    ensures xs == ys
  {
    lemma_smaller_base_to_nat(xs);
    lemma_smaller_base_to_nat(ys);
    assert LargeBound.to_nat(xs) == LargeBound.to_nat(ys);
    LargeBound.lemma_seq_eq(xs, ys);
  }

  /* to_larger_base is injective. */
  lemma lemma_to_larger_base_is_injective(xs: seq<SmallBound.uint>,
                                          ys: seq<SmallBound.uint>)
    requires |xs| % E() == |ys| % E() == 0 
    requires to_larger_base(xs) == to_larger_base(ys)
    requires |xs| == |ys|
    ensures xs == ys
  {
    lemma_larger_base_to_nat(xs);
    lemma_larger_base_to_nat(ys);
    assert SmallBound.to_nat(xs) == SmallBound.to_nat(ys);
    SmallBound.lemma_seq_eq(xs, ys);
  }

}
