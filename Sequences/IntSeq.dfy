include "../Nonlinear_Arithmetic/DivMod.dfy"
include "../Nonlinear_Arithmetic/Mul.dfy"
include "../NativeTypes.dfy"
include "../Nonlinear_Arithmetic/Power.dfy"
include "Seq.dfy"

module IntSeq {

  import opened DivMod
  import opened Mul
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
    else
      lemma_power_positive_auto();
      lemma_mul_nonnegative_auto();
      to_nat(drop_last(xs)) + last(xs) * power(BASE, |xs| - 1)
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

  // unstable
  lemma lemma_lsw_mod_equivalence(xs: seq<BaseType>)
    requires |xs| >= 1;
    ensures is_mod_equivalent(to_nat(xs), xs[0], BASE);
  {
    if |xs| == 1 {
      lemma_to_nat_len_1(xs);
    } else {
      assert is_mod_equivalent(to_nat(xs), xs[0], BASE) by {
        var len' := |xs| - 1;
        var xs' := drop_last(xs);

        assert is_mod_equivalent(last(xs) * power(BASE, len'), 0, BASE) by {
          lemma_power_mod_auto();
          lemma_mul_mod_noop_general_auto();
          lemma_mul_basics_auto();
        }

        calc ==> {
          true;
            { reveal to_nat(); }
          is_mod_equivalent(to_nat(xs), to_nat(xs') + xs[len'] * power(BASE, len'), BASE);
            {
              lemma_power_mod_auto();
              lemma_mul_basics_auto();
            }
          is_mod_equivalent(to_nat(xs), to_nat(xs'), BASE);
            {
              lemma_lsw_mod_equivalence(xs');
              assert xs'[0] == xs[0];
            }
          is_mod_equivalent(to_nat(xs), xs[0], BASE);
        }
        assert is_mod_equivalent(to_nat(xs), xs[0], BASE);
      }
    }
  }

  function method {:opaque} seq_zero(len: nat): (zs: seq<BaseType>)
    ensures |zs| == len
  {
    if len == 0 then [] else seq_zero(len - 1) + [0]
  }

  lemma lemma_seq_zero_to_nat(len: nat)
    ensures to_nat(seq_zero(len)) == 0
  {
    reveal to_nat();
    reveal seq_zero();
    if len > 0 {
      calc {
        to_nat(seq_zero(len));
        to_nat(seq_zero(len - 1) + [0]);
        to_nat(seq_zero(len - 1)) + 0 * power(BASE, len - 1);
          {
            lemma_seq_zero_to_nat(len - 1);
            lemma_mul_basics_auto();
          }
        0;
      }
    }
  }

  lemma lemma_to_nat_bound(xs: seq<BaseType>)
    ensures to_nat(xs) < power(BASE, |xs|)
  {
    reveal to_nat();
    reveal power();
    if |xs| != 0 {
      var len' := |xs| - 1;
      calc {
        to_nat(xs);
        to_nat(drop_last(xs)) + last(xs) * power(BASE, len');
        < { lemma_to_nat_bound(drop_last(xs)); }
        power(BASE, len') + last(xs) * power(BASE, len');
        <=
          {
            assert last(xs) <= BASE - 1;
            lemma_power_positive_auto();
            lemma_mul_inequality_auto(); 
          }
        power(BASE, len') + (BASE - 1) * power(BASE, len');
        BASE * power(BASE, len');
        power(BASE, len' + 1);
      }
    }
  }

  lemma lemma_to_nat_zero_prepend (xs: seq<BaseType>)
    ensures to_nat([0] + xs) == to_nat(xs) * BASE
  {
    reveal to_nat();
    if |xs| == 0 {
      lemma_mul_basics_auto();
    } else {
      reveal power();
      calc {
        to_nat([0] + xs);
          { assert drop_last([0] + xs) == [0] + drop_last(xs); }
        to_nat([0] + drop_last(xs)) + last(xs) * power(BASE, |xs|);
          { lemma_to_nat_zero_prepend(drop_last(xs)); }
        to_nat(drop_last(xs)) * BASE + last(xs) * power(BASE, |xs|);
          {
            lemma_mul_is_associative_auto();
            lemma_mul_is_distributive_add_other_way_auto();
          }
        (to_nat(drop_last(xs)) + last(xs) * power(BASE, |xs| - 1)) * BASE;
        to_nat(xs) * BASE;
      }
    }
  }

  lemma lemma_to_nat_prefix(xs: seq<BaseType>, i: nat)
    requires 1 <= i < |xs|
    ensures to_nat(xs[..i]) == to_nat(xs[..i-1]) + xs[i-1] * power(BASE, i - 1)
  {
    assert xs[..i][..i-1] == xs[..i-1];
    reveal to_nat();
  }

  lemma lemma_to_nat_zero_extend(xs': seq<BaseType>, xs: seq<BaseType>) 
    requires |xs'| < |xs|
    requires var len' := |xs'|;
      && drop_last(xs) == xs'
      && xs[len'.. ] == seq(|xs| - len', i => 0)
    ensures to_nat(xs') == to_nat(xs)
  {
    var len, len' := |xs|, |xs'|;
    reveal to_nat();
    if len != len' + 1 {
      calc == {
        to_nat(xs);
        to_nat(drop_last(xs)) + last(xs) * power(BASE, len - 1);
        to_nat(drop_last(xs));
        { lemma_to_nat_zero_extend(xs', drop_last(xs)); }
        to_nat(xs');
      }
    }
  }

  function method {:opaque} seq_addc(xs: seq<BaseType>,
                                     ys: seq<BaseType>): (seq<BaseType>, nat)
    requires |xs| == |ys|
    ensures var (zs, cout) := seq_addc(xs, ys); |zs| == |xs|
  {
    reveal seq_addc();
    if |xs| == 0 then ([], 0)
    else
      var (zs', cin) := seq_addc(drop_last(xs), drop_last(ys));
      var sum: int := last(xs) + last(ys) + cin;
      var (sum_out, cout) := if sum < BASE then (sum, 0)
                             else assert 0 <= sum - BASE; (sum - BASE, 1);
      (zs' + [sum_out], cout)
  }

  lemma lemma_seq_addc_nat(xs: seq<BaseType>,
                           ys: seq<BaseType>,
                           zs: seq<BaseType>,
                           cout: nat)
    requires |xs| == |ys|
    requires seq_addc(xs, ys) == (zs, cout)
    ensures to_nat(xs) + to_nat(ys) == to_nat(zs) + cout * power(BASE, |xs|)
  {
    reveal seq_addc();
    reveal to_nat();
    if |xs| == 0 {
      reveal power();
    } else {
      var len' := |xs| - 1;
      var (zs', cin) := seq_addc(drop_last(xs), drop_last(ys));
      var sum: int := last(xs) + last(ys) + cin;
      var z := if sum < BASE then sum
               else assert 0 <= sum - BASE; sum - BASE;
      assert sum == z + cout * BASE;

      calc {
        to_nat(zs);
        to_nat(zs') + z * power(BASE, len');
          { lemma_seq_addc_nat(drop_last(xs), drop_last(ys), zs', cin); }
        to_nat(drop_last(xs)) + to_nat(drop_last(ys)) - cin * power(BASE, len') + z * power(BASE, len');
          {
            lemma_mul_equality_auto();
            assert (last(xs) + last(ys) + cin) * power(BASE, len') == (z + cout * BASE) * power(BASE, len');
            lemma_mul_is_distributive_add_other_way_auto();
          } 
        to_nat(drop_last(xs)) + to_nat(drop_last(ys)) + last(xs) * power(BASE, len') + last(ys) * power(BASE, len') - cout * BASE * power(BASE, len');
        to_nat(xs) + to_nat(ys) - cout * BASE * power(BASE, len');
          {
            lemma_mul_is_associative(cout, BASE, power(BASE, len'));
            reveal power();
          }
        to_nat(xs) + to_nat(ys) - cout * power(BASE, |xs|);
      }
      assert to_nat(zs) + cout * power(BASE, |xs|) == to_nat(xs) + to_nat(ys);
    }
  }

  function method {:opaque} seq_subb(xs: seq<BaseType>,
                                     ys: seq<BaseType>): (seq<BaseType>, nat)
    requires |xs| == |ys|
    ensures var (zs, bout) := seq_subb(xs, ys); |zs| == |xs|
  {
    reveal seq_subb();
    if |xs| == 0 then ([], 0)
    else 
      var (zs, bin) := seq_subb(drop_last(xs), drop_last(ys));
      var (diff_out, bout) := if last(xs) >= last(ys) + bin
                              then (last(xs) - last(ys) - bin, 0)
                              else (BASE + last(xs) - last(ys) - bin, 1);
      (zs + [diff_out], bout)
  }

  lemma lemma_seq_subb_nat(xs: seq<BaseType>,
                           ys: seq<BaseType>,
                           zs: seq<BaseType>,
                           bout: nat)
    requires |xs| == |ys|
    requires seq_subb(xs, ys) == (zs, bout)
    ensures to_nat(xs) - to_nat(ys) + bout * power(BASE, |xs|) == to_nat(zs)
  {
    reveal seq_subb();
    reveal to_nat();
    if |xs| == 0 {
      reveal power();
    } else {
      var len' := |xs| - 1;
      var (zs', bin) := seq_subb(drop_last(xs), drop_last(ys));
      var z := if last(xs) >= last(ys) + bin
               then last(xs) - last(ys) - bin
               else BASE + last(xs) - last(ys) - bin;
      assert bout * BASE + last(xs) - bin - last(ys) == z;
      
      calc {
        to_nat(zs);
        to_nat(zs') + z * power(BASE, len');
          { lemma_seq_subb_nat(drop_last(xs), drop_last(ys), zs', bin); }
        to_nat(drop_last(xs)) - to_nat(drop_last(ys)) + bin * power(BASE, len')
          + z * power(BASE, len');
          {
            lemma_mul_equality_auto();
            assert power(BASE, len') * (bout * BASE + last(xs) - bin - last(ys)) == power(BASE, len') * z;
            lemma_mul_is_distributive_sub_auto();
            lemma_mul_is_distributive_add_auto();
            lemma_mul_is_commutative_auto();
          }
        to_nat(drop_last(xs)) - to_nat(drop_last(ys)) + last(xs) 
          * power(BASE, len') - last(ys) * power(BASE, len') + bout * BASE
          * power(BASE, len');
        to_nat(xs) - to_nat(ys) + bout * BASE * power(BASE, len');
          {
            lemma_mul_is_associative(bout, BASE, power(BASE, len'));
            reveal power();
          }
        to_nat(xs) - to_nat(ys) + bout * power(BASE, |xs|);
      }
    }
  }

}
