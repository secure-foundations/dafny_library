include "NatSeq.dfy"
// TODO: Add examples of how these modules are used with assert statements
// TODO: Add instantiation with common bounds - 8, 16, 32

include "NatSeq.dfy"

abstract module NatSeqConversions refines NatSeq {

  import Small
  import Large

  /* Small.BOUND() to the power of E() is Large.BOUND(). */
  function method E(): nat
    ensures power(Small.BOUND(), E()) == Large.BOUND()
  {
    lemma_div_basics_auto();
    lemma_power_multiplies_auto();
    lemma_fundamental_div_mod(Large.BITS(), Small.BITS());
    Large.BITS() / Small.BITS()
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

  /* Converts a sequence from Large.BOUND() to Small.BOUND(). */
  function method {:opaque} to_small(xs: seq<Large.uint>): (ys: seq<Small.uint>)
    ensures |ys| == |xs| * E()
  {
    if |xs| == 0 then []
    else
      lemma_mul_is_distributive_add_other_way(E(), 1, |xs| - 1);
      Small.from_nat_with_len(first(xs), E()) + to_small(drop_first(xs))
  }

  /* Converts a sequence from Small.BOUND() to Large.BOUND(). */
  function method {:opaque} to_large(xs: seq<Small.uint>): (ys: seq<Large.uint>)
    requires |xs| % E() == 0
    ensures |ys| == |xs| / E()
  {
    if |xs| == 0 then lemma_div_basics_auto(); []
    else
      lemma_mod_eq_zero(|xs|, E());
      assert |xs| >= E();

      Small.lemma_seq_nat_bound(xs[..E()]);
      lemma_mod_sub_multiples_vanish_auto();
      lemma_div_minus_one(|xs|, E());
      [Small.to_nat(xs[..E()]) as Large.uint] + to_large(xs[E()..])
  }

  /* Sequence conversion from Large.BOUND() to Small.BOUND() does not
  change its nat representation. */
  lemma lemma_to_small(xs: seq<Large.uint>)
    ensures Small.to_nat(to_small(xs)) == Large.to_nat(xs)
  {
    reveal Large.to_nat();
    reveal Small.to_nat();
    reveal to_small();
    if |xs| > 0 {
      calc {
        Small.to_nat(to_small(xs));
        Small.to_nat(Small.from_nat_with_len(first(xs), E()) + to_small(drop_first(xs)));
          {
            Small.lemma_seq_prefix(Small.from_nat_with_len(first(xs), E()) + to_small(drop_first(xs)), E());
            lemma_to_small(drop_first(xs));
          }
        first(xs) + Large.to_nat(drop_first(xs)) * power(Small.BOUND(), E());
          { assert power(Small.BOUND(), E()) == Large.BOUND(); }
        Large.to_nat(xs);
      }
    }
  }

  /* Sequence conversion from Small.BOUND() to Large.BOUND() does not
  change its nat representation. */
  lemma lemma_to_large(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures Large.to_nat(to_large(xs)) == Small.to_nat(xs)
  {
    reveal Large.to_nat();
    reveal Small.to_nat();
    reveal to_large();
    if |xs| > 0 {
      calc {
        Large.to_nat(to_large(xs));
          {
            lemma_mod_eq_zero(|xs|, E());
            lemma_mod_sub_multiples_vanish_auto();
            Small.lemma_seq_nat_bound(xs[..E()]);
          }
        Large.to_nat([Small.to_nat(xs[..E()]) as Large.uint] + to_large(xs[E()..]));
          { lemma_to_large(xs[E()..]); }
        Small.to_nat(xs[..E()]) + Small.to_nat(xs[E()..]) * power(Small.BOUND(), E());
          { Small.lemma_seq_prefix(xs, E()); }
        Small.to_nat(xs);
      }
    }
  }

  /* to_small is injective. */
  lemma lemma_to_small_is_injective(xs: seq<Large.uint>, ys: seq<Large.uint>)
    requires to_small(xs) == to_small(ys)
    requires |xs| == |ys|
    ensures xs == ys
  {
    lemma_to_small(xs);
    lemma_to_small(ys);
    assert Large.to_nat(xs) == Large.to_nat(ys);
    Large.lemma_seq_eq(xs, ys);
  }

  /* to_large is injective. */
  lemma lemma_to_large_is_injective(xs: seq<Small.uint>, ys: seq<Small.uint>)
    requires |xs| % E() == |ys| % E() == 0 
    requires to_large(xs) == to_large(ys)
    requires |xs| == |ys|
    ensures xs == ys
  {
    lemma_to_large(xs);
    lemma_to_large(ys);
    assert Small.to_nat(xs) == Small.to_nat(ys);
    Small.lemma_seq_eq(xs, ys);
  }

  lemma lemma_small_large_small(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures to_small(to_large(xs)) == xs
  {
    reveal to_small();
    reveal to_large();
    if |xs| > 0 {
      calc {
        to_small(to_large(xs));
          {
            lemma_mod_eq_zero(|xs|, E());
            Small.lemma_seq_nat_bound(xs[..E()]);
            lemma_mod_sub_multiples_vanish_auto();
          }
        to_small([Small.to_nat(xs[..E()]) as Large.uint] + to_large(xs[E()..]));
        Small.from_nat_with_len(Small.to_nat(xs[..E()]), E()) + to_small(to_large(xs[E()..]));
          {
            Small.lemma_seq_nat_seq(xs[..E()]);
            lemma_small_large_small(xs[E()..]);
          }
        xs;
      }
    }
  }

  lemma lemma_large_small_large(xs: seq<Large.uint>)
    ensures |to_small(xs)| % E() == 0
    ensures to_large(to_small(xs)) == xs
  {
    reveal to_small();
    reveal to_large();
    lemma_mod_multiples_basic_auto();
    if |xs| > 0 {
      calc {
        to_large(to_small(xs));
        to_large(Small.from_nat_with_len(first(xs), E()) + to_small(drop_first(xs)));
        [Small.to_nat(Small.from_nat_with_len(first(xs), E())) as Large.uint] + to_large(to_small(drop_first(xs)));
        [first(xs)] + to_large(to_small(drop_first(xs)));
          { lemma_large_small_large(drop_first(xs)); }
        [first(xs)] + drop_first(xs);
        xs;
      }
    }
  }

}
