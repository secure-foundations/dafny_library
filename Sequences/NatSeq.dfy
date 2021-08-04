/* The first element of a sequence is the least significant word; the last
element is the most significant word. */

include "../Nonlinear_Arithmetic/DivMod.dfy"
include "../Nonlinear_Arithmetic/Mul.dfy"
include "../Nonlinear_Arithmetic/Power.dfy"
include "../Nonlinear_Arithmetic/Power2.dfy"
include "Seq.dfy"

abstract module NatSeq {

  import opened DivMod
  import opened Mul
  import opened Power
  import opened Power2
  import opened Seq

  /* Upper bound of a word */
  function method BOUND(): nat
		ensures BOUND() > 1

  type uint = i: int | 0 <= i < BOUND()

  //////////////////////////////////////////////////////////////////////////////
  //
  // to_nat definition and lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Converts a sequence to a nat beginning from the least significant word. */
  function method {:opaque} to_nat(xs: seq<uint>): nat
  {
    if |xs| == 0 then 0
    else
      lemma_mul_nonnegative_auto();
      to_nat(drop_first(xs)) * BOUND() + first(xs)
  }

  /* Converts a sequence to a nat beginning from the most significant word. */
  function method {:opaque} to_nat_rev(xs: seq<uint>): nat
  {
    if |xs| == 0 then 0
    else
      lemma_power_positive_auto();
      lemma_mul_nonnegative_auto();
      to_nat_rev(drop_last(xs)) + last(xs) * power(BOUND(), |xs| - 1)
  }

  /* Given the same sequence, to_nat and to_nat_rev return the same nat. */
  lemma lemma_to_nat_eq_to_nat_rev(xs: seq<uint>)
    ensures to_nat(xs) == to_nat_rev(xs)
  {
    reveal to_nat();
    reveal to_nat_rev();
    if xs != [] {
      if drop_last(xs) == [] {
        calc {
          to_nat_rev(xs);
          last(xs) * power(BOUND(), |xs| - 1);
            { lemma_power_0_auto(); }
          to_nat(xs);
        }
      } else {
        calc {
          to_nat_rev(xs);
          to_nat_rev(drop_last(xs)) + last(xs) * power(BOUND(), |xs| - 1);
            { lemma_to_nat_eq_to_nat_rev(drop_last(xs)); }
          to_nat(drop_last(xs)) + last(xs) * power(BOUND(), |xs| - 1);
          to_nat(drop_first(drop_last(xs))) * BOUND() + first(xs) + last(xs)
            * power(BOUND(), |xs| - 1);
            { lemma_to_nat_eq_to_nat_rev(drop_first(drop_last(xs))); }
          to_nat_rev(drop_first(drop_last(xs))) * BOUND() + first(xs) + last(xs)
            * power(BOUND(), |xs| - 1);
            {
              assert drop_first(drop_last(xs)) == drop_last(drop_first(xs));
              reveal power();
              lemma_mul_properties();
            }
          to_nat_rev(drop_last(drop_first(xs))) * BOUND() + first(xs) + last(xs)
            * power(BOUND(), |xs| - 2) * BOUND();
            { lemma_mul_is_distributive_add_other_way_auto(); }
          to_nat_rev(drop_first(xs)) * BOUND() + first(xs);
            { lemma_to_nat_eq_to_nat_rev(drop_first(xs)); }
          to_nat(xs);
        }
      }
    }
  }

  lemma lemma_to_nat_eq_to_nat_rev_auto()
    ensures forall xs: seq<uint> {:trigger to_nat_rev(xs)}{:trigger to_nat(xs)}
      :: to_nat(xs) == to_nat_rev(xs)
  {
    reveal to_nat();
    reveal to_nat_rev();
    forall xs: seq<uint> {:trigger to_nat_rev(xs)}{:trigger to_nat(xs)}
      ensures to_nat(xs) == to_nat_rev(xs)
    {
      lemma_to_nat_eq_to_nat_rev(xs);
    }
  }

  /* The nat representation of a sequence of length 1 is its first (and only)
  word. */
  lemma lemma_seq_len_1(xs: seq<uint>)
    requires |xs| == 1
    ensures to_nat(xs) == first(xs)
  {
    reveal to_nat();
  }

  /* The nat representation of a sequence of length 2 is sum of its first
  word and the product of its second word and BOUND(). */
  lemma lemma_seq_len_2(xs: seq<uint>)
    requires |xs| == 2
    ensures to_nat(xs) == first(xs) + xs[1] * BOUND()
  {
    reveal to_nat();
    lemma_seq_len_1(drop_last(xs));
  }

  /* Prepending a zero is equal to multiplying the nat representation of the
  sequence by BOUND(). */
  lemma lemma_seq_prepend_zero(xs: seq<uint>)
    ensures to_nat([0] + xs) == to_nat(xs) * BOUND()
  {
    reveal to_nat();
  }

  /* Appending a zero does not change the nat representation of the sequence. */
  lemma lemma_seq_append_zero(xs: seq<uint>) 
    ensures to_nat(xs + [0]) == to_nat(xs)
  {
    reveal to_nat_rev();
    lemma_to_nat_eq_to_nat_rev_auto();
    calc == {
      to_nat(xs + [0]);
      to_nat_rev(xs + [0]);
      to_nat_rev(xs) + 0 * power(BOUND(), |xs|);
        { lemma_mul_basics_auto(); }
      to_nat_rev(xs);
      to_nat(xs);
    }
  }

  /* The nat representation of a sequence is bounded by BOUND() to the power of
  the sequence length. */
  lemma lemma_seq_nat_bound(xs: seq<uint>)
    ensures to_nat(xs) < power(BOUND(), |xs|)
  {
    reveal power();
    if |xs| == 0 {
      reveal to_nat();
    } else {
      var len' := |xs| - 1;
      var pow := power(BOUND(), len');
      calc {
        to_nat(xs);
           { lemma_to_nat_eq_to_nat_rev(xs); }
        to_nat_rev(xs);
           { reveal to_nat_rev(); }
        to_nat_rev(drop_last(xs)) + last(xs) * pow;
        <  {
             lemma_to_nat_eq_to_nat_rev(drop_last(xs));
             lemma_seq_nat_bound(drop_last(xs));
           }
        pow + last(xs) * pow;
        <= {
            lemma_power_positive_auto();
            lemma_mul_inequality_auto();
           }
        pow + (BOUND() - 1) * pow;
           { lemma_mul_is_distributive_auto(); }
        power(BOUND(), len' + 1);
      }
    }
  }

  /* The nat representation of a sequence can be calculated using the nat
  representation of its prefix. */
  lemma lemma_seq_prefix(xs: seq<uint>, i: nat)
    requires 0 <= i <= |xs|
    ensures to_nat(xs[..i]) + to_nat(xs[i..]) * power(BOUND(), i) == to_nat(xs)
  {
    reveal to_nat();
    reveal power();
    if i == 1 {
      assert to_nat(xs[..1]) == first(xs);
    } else if i > 1 {
      calc {
        to_nat(xs[..i]) + to_nat(xs[i..]) * power(BOUND(), i);
        to_nat(drop_first(xs[..i])) * BOUND() + first(xs) + to_nat(xs[i..]) * power(BOUND(), i);
          {
            assert drop_first(xs[..i]) == drop_first(xs)[..i-1];
            lemma_mul_properties();
          }
        to_nat(drop_first(xs)[..i-1]) * BOUND() + first(xs) + (to_nat(xs[i..]) * power(BOUND(), i - 1)) * BOUND();
          { lemma_mul_is_distributive_add_other_way_auto(); }
        (to_nat(drop_first(xs)[..i-1]) + to_nat(drop_first(xs)[i-1..]) * power(BOUND(), i - 1)) * BOUND() + first(xs);
          { lemma_seq_prefix(drop_first(xs), i - 1); }
        to_nat(xs);
      }
    }
  }

  /* If there is an inequality between the most significant words of two
  sequences, then there is an inequality between the nat representations of
  those sequences. Helper lemma for lemma_seq_neq. */
  lemma lemma_seq_msw_inequality(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys| > 0
    requires last(xs) < last(ys)
    ensures to_nat(xs) < to_nat(ys)
  {
    reveal to_nat_rev();
    lemma_to_nat_eq_to_nat_rev_auto();
    var len' := |xs| - 1;
    calc {
      to_nat(xs);
      to_nat_rev(xs);
      <  { lemma_seq_nat_bound(drop_last(xs)); }
      power(BOUND(), len') + last(xs) * power(BOUND(), len');
      == { lemma_mul_is_distributive_auto(); }
      (1 + last(xs)) * power(BOUND(), len');
      <= { lemma_power_positive_auto(); lemma_mul_inequality_auto(); }
      to_nat_rev(ys);
      to_nat(ys);
    }
  }

  /* Two sequences do not have the same nat representations if their prefixes
  do not have the same nat representations. Helper lemma for lemma_seq_neq. */
  lemma lemma_seq_prefix_neq(xs: seq<uint>, ys: seq<uint>, i: nat)
    requires 0 <= i <= |xs| == |ys|
    requires to_nat(xs[..i]) != to_nat(ys[..i])
    ensures to_nat(xs) != to_nat(ys)
    decreases |xs| - i
  {
    if i == |xs| {
      assert xs[..i] == xs;
      assert ys[..i] == ys;
    } else {
      if xs[i] == ys[i] {
        reveal to_nat_rev();
        assert drop_last(xs[..i+1]) == xs[..i];
        assert drop_last(ys[..i+1]) == ys[..i];

        lemma_to_nat_eq_to_nat_rev_auto();
        assert to_nat(xs[..i+1]) == to_nat_rev(xs[..i+1]);
      } else {
        if xs[i] < ys[i]  { lemma_seq_msw_inequality(xs[..i+1], ys[..i+1]); }
        else              { lemma_seq_msw_inequality(ys[..i+1], xs[..i+1]); }
      }
      lemma_seq_prefix_neq(xs, ys, i + 1);
    }
  }

  /* If two sequences of the same length are not equal, their nat
  representations are not equal. */
  lemma lemma_seq_neq(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys|
    requires xs != ys
    ensures to_nat(xs) != to_nat(ys)
  {
    ghost var i: nat, n: nat := 0, |xs|;

    while i < n
      invariant 0 <= i < n
      invariant xs[..i] == ys[..i]
    {
      if xs[i] != ys[i] {
        break;
      }
      i := i + 1;
    }
    assert to_nat_rev(xs[..i]) == to_nat_rev(ys[..i]);

    reveal to_nat_rev();
    assert xs[..i+1][..i] == xs[..i];
    assert ys[..i+1][..i] == ys[..i];
    lemma_power_positive_auto();
    lemma_mul_strict_inequality_auto();
    assert to_nat_rev(xs[..i+1]) != to_nat_rev(ys[..i+1]);
    lemma_to_nat_eq_to_nat_rev_auto();

    lemma_seq_prefix_neq(xs, ys, i+1);
  }

  /* If the nat representations of two sequences of the same length are equal
  to each other, the sequences are the same. */
  lemma lemma_seq_eq(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys|
    requires to_nat(xs) == to_nat(ys)
    ensures xs == ys
  {
    calc ==> {
      xs != ys;
        { lemma_seq_neq(xs, ys); }
      to_nat(xs) != to_nat(ys);
      false;
    }
  }

  /* The nat representation of a sequence and its least significant word are
  congruent. */
  lemma lemma_seq_lsw_mod_equivalence(xs: seq<uint>)
    requires |xs| >= 1;
    ensures is_mod_equivalent(to_nat(xs), first(xs), BOUND());
  {
    if |xs| == 1 {
      lemma_seq_len_1(xs);
      lemma_mod_equivalence_auto();
    } else {
      assert is_mod_equivalent(to_nat(xs), first(xs), BOUND()) by {
        reveal to_nat();
        calc ==> {
          true;
            { lemma_mod_equivalence_auto(); }
          is_mod_equivalent(to_nat(xs), to_nat(drop_first(xs)) * BOUND() + first(xs), BOUND());
            { lemma_mod_multiples_basic_auto(); }
          is_mod_equivalent(to_nat(xs), first(xs), BOUND());
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // from_nat definition and lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Converts a nat to a sequence. */
  function method {:opaque} from_nat(n: nat): (xs: seq<uint>)
  {
    if n == 0 then []
    else
      lemma_div_basics_auto();
      lemma_div_decreases_auto();
      [n % BOUND()] + from_nat(n / BOUND())
  }

  /* Ensures length of the sequence generated by from_nat is less than len.
  Helper lemma for from_nat_with_len. */
  lemma lemma_from_nat_length(n: nat, len: nat)
    requires power(BOUND(), len) > n
    ensures |from_nat(n)| <= len
    decreases n
  {
    reveal from_nat();
    if n > 0 {
      calc {
        |from_nat(n)|;
        == { lemma_div_basics_auto(); }
        1 + |from_nat(n / BOUND())|;
        <= {
             lemma_multiply_divide_lt_auto();
             lemma_div_decreases_auto();
             reveal power();
             lemma_from_nat_length(n / BOUND(), len - 1);
           }
        len;
      }
    }
  }

  /* If we start with a nat, convert it to a sequence, and convert it back, we
  get the same nat we started with. */
  lemma lemma_nat_seq_nat(n: nat)
    ensures to_nat(from_nat(n)) == n
    decreases n
  {
    reveal to_nat();
    reveal from_nat();
    if n > 0 {
      calc {
        to_nat(from_nat(n));
          { lemma_div_basics_auto(); }
        to_nat([n % BOUND()] + from_nat(n / BOUND()));
        n % BOUND() + to_nat(from_nat(n / BOUND())) * BOUND();
          {
            lemma_div_decreases_auto();
            lemma_nat_seq_nat(n / BOUND());
          }
        n % BOUND() + n / BOUND() * BOUND();
          { lemma_fundamental_div_mod(n, BOUND()); }
        n;
      }
    }
  }

  /* Extends a sequence to a specified length. */
  function method {:opaque} seq_extend(xs: seq<uint>, n: nat): (ys: seq<uint>)
    requires |xs| <= n
    ensures |ys| == n
    ensures to_nat(ys) == to_nat(xs)
    decreases n - |xs|
  {
    if |xs| >= n then xs else lemma_seq_append_zero(xs); seq_extend(xs + [0], n)
  }

  /* Extends a sequence to a length that is a multiple of n. */
  function method {:opaque} seq_extend_multiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
    requires n > 0
    ensures |ys| % n == 0
    ensures to_nat(ys) == to_nat(xs)
  {
    var newLen := |xs| + n - (|xs| % n);
    lemma_sub_mod_noop_right(|xs| + n, |xs|, n);
    lemma_mod_basics_auto();
    assert newLen % n == 0;

    lemma_seq_nat_bound(xs);
    lemma_power_increases_auto();
    seq_extend(xs, newLen)
  }

  /* Converts a nat to a sequence of a specified length. */
  function method {:opaque} from_nat_with_len(n: nat, len: nat): (xs: seq<uint>)
    requires power(BOUND(), len) > n
    ensures |xs| == len
    ensures to_nat(xs) == n
  {
    lemma_from_nat_length(n, len);
    lemma_nat_seq_nat(n);
    seq_extend(from_nat(n), len)
  }

  /* Generates a sequence of zeros of a specified length. */
  function method {:opaque} seq_zero(len: nat): (zs: seq<uint>)
    ensures |zs| == len
    ensures to_nat(zs) == 0
  {
    lemma_power_positive(BOUND(), len);
    from_nat_with_len(0, len)
  }

  /* If we start with a sequence, convert it to a nat, and convert it back to a
  sequence with the same length as the original sequence, we get the same
  sequence we started with. */
  lemma lemma_seq_nat_seq(xs: seq<uint>)
    ensures power(BOUND(), |xs|) > to_nat(xs)
    ensures from_nat_with_len(to_nat(xs), |xs|) == xs
  {
    reveal from_nat();
    reveal to_nat();
    lemma_seq_nat_bound(xs);
    if |xs| > 0 {
      calc {
        from_nat_with_len(to_nat(xs), |xs|) != xs;
          { lemma_seq_neq(from_nat_with_len(to_nat(xs), |xs|), xs); }
        to_nat(from_nat_with_len(to_nat(xs), |xs|)) != to_nat(xs);
        to_nat(xs) != to_nat(xs);
        false;
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Addition and subtraction
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Adds two sequences. */
  function method {:opaque} seq_add(xs: seq<uint>,
                                    ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs, cout) := seq_add(xs, ys); |zs| == |xs|
    decreases xs
  {
    reveal seq_add();
    if |xs| == 0 then ([], 0)
    else
      var (zs', cin) := seq_add(drop_last(xs), drop_last(ys));
      var sum: int := last(xs) + last(ys) + cin;
      var (sum_out, cout) := if sum < BOUND() then (sum, 0)
                             else (sum - BOUND(), 1);
      (zs' + [sum_out], cout)
  }

  /* seq_add returns the same value as converting the sequences to nats, then
  adding them. */
  lemma lemma_seq_add(xs: seq<uint>,
                      ys: seq<uint>,
                      zs: seq<uint>,
                      cout: nat)
    requires |xs| == |ys|
    requires seq_add(xs, ys) == (zs, cout)
    ensures to_nat(xs) + to_nat(ys) == to_nat(zs) + cout * power(BOUND(), |xs|)
  {
    reveal seq_add();
    if |xs| == 0 {
      reveal to_nat();
    } else {
      var pow := power(BOUND(), |xs| - 1);
      var (zs', cin) := seq_add(drop_last(xs), drop_last(ys));
      var sum: int := last(xs) + last(ys) + cin;
      var z := if sum < BOUND() then sum else sum - BOUND();
      assert sum == z + cout * BOUND();

      reveal to_nat_rev();
      lemma_to_nat_eq_to_nat_rev_auto();
      calc {
        to_nat(zs);
        to_nat_rev(zs);
        to_nat_rev(zs') + z * pow;
          { lemma_seq_add(drop_last(xs), drop_last(ys), zs', cin); }
        to_nat_rev(drop_last(xs)) + to_nat_rev(drop_last(ys)) - cin * pow + z * pow;
          {
            lemma_mul_equality_auto();
            assert sum * pow == (z + cout * BOUND()) * pow;
            lemma_mul_is_distributive_auto();
          } 
        to_nat_rev(xs) + to_nat_rev(ys) - cout * BOUND() * pow;
          {
            lemma_mul_is_associative(cout, BOUND(), pow);
            reveal power();
          }
        to_nat_rev(xs) + to_nat_rev(ys) - cout * power(BOUND(), |xs|);
        to_nat(xs) + to_nat(ys) - cout * power(BOUND(), |xs|);
      }
    }
  }

  /* Subtracts two sequences. */
  function method {:opaque} seq_sub(xs: seq<uint>,
                                    ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs, cout) := seq_sub(xs, ys); |zs| == |xs|
    decreases xs
  {
    reveal seq_sub();
    if |xs| == 0 then ([], 0)
    else 
      var (zs, cin) := seq_sub(drop_last(xs), drop_last(ys));
      var (diff_out, cout) := if last(xs) >= last(ys) + cin
                              then (last(xs) - last(ys) - cin, 0)
                              else (BOUND() + last(xs) - last(ys) - cin, 1);
      (zs + [diff_out], cout)
  }

  /* seq_sub returns the same value as converting the sequences to nats, then
  subtracting them. */
  lemma lemma_seq_sub(xs: seq<uint>,
                      ys: seq<uint>,
                      zs: seq<uint>,
                      cout: nat)
    requires |xs| == |ys|
    requires seq_sub(xs, ys) == (zs, cout)
    ensures to_nat(xs) - to_nat(ys) + cout * power(BOUND(), |xs|) == to_nat(zs)
  {
    reveal seq_sub();
    if |xs| == 0 {
      reveal to_nat();
    } else {
      var pow := power(BOUND(), |xs| - 1);
      var (zs', cin) := seq_sub(drop_last(xs), drop_last(ys));
      var z := if last(xs) >= last(ys) + cin
               then last(xs) - last(ys) - cin
               else BOUND() + last(xs) - last(ys) - cin;
      assert cout * BOUND() + last(xs) - cin - last(ys) == z;

      reveal to_nat_rev();
      lemma_to_nat_eq_to_nat_rev_auto();
      calc {
        to_nat(zs);
        to_nat_rev(zs);
        to_nat_rev(zs') + z * pow;
          { lemma_seq_sub(drop_last(xs), drop_last(ys), zs', cin); }
        to_nat_rev(drop_last(xs)) - to_nat_rev(drop_last(ys)) + cin * pow + z * pow;
          {
            lemma_mul_equality_auto();
            assert pow * (cout * BOUND() + last(xs) - cin - last(ys)) == pow * z;
            lemma_mul_is_distributive_auto();
          }
        to_nat_rev(xs) - to_nat_rev(ys) + cout * BOUND() * pow;
          {
            lemma_mul_is_associative(cout, BOUND(), pow);
            reveal power();
          }
        to_nat_rev(xs) - to_nat_rev(ys) + cout * power(BOUND(), |xs|);
        to_nat(xs) - to_nat(ys) + cout * power(BOUND(), |xs|);
      }
    }
  }

}
