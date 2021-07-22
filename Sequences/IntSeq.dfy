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
  // to_nat definition and lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Converts a sequence to nat. */
  function method {:opaque} to_nat(xs: seq<BaseType>): nat
  {
    if |xs| == 0 then 0
    else
      lemma_power_positive_auto();
      lemma_mul_nonnegative_auto();
      to_nat(drop_last(xs)) + last(xs) * power(BASE, |xs| - 1)
  }

  /* Proves the nat representation of a sequence of length 1. */
  lemma lemma_seq_len_1_nat(xs: seq<BaseType>)
    requires |xs| == 1
    ensures to_nat(xs) == xs[0]
  {
    reveal to_nat();
    reveal power();
  }

  /* Proves the nat representation of a sequence of length 2. */
  lemma lemma_seq_len_2_nat(xs: seq<BaseType>)
    requires |xs| == 2
    ensures to_nat(xs) == xs[0] + xs[1] * BASE
  {
    reveal to_nat();
    lemma_seq_len_1_nat(drop_last(xs));
    reveal power();
  }

  lemma lemma_seq_equivalence(xs: seq<BaseType>, ys: seq<BaseType>)
    requires xs == ys
    ensures to_nat(xs) == to_nat(ys)
  {
    reveal to_nat();
  }

  /* Proves the nat representation of a sequence is bounded by BASE to the
  power of the sequence length. */
  lemma lemma_seq_nat_bound(xs: seq<BaseType>)
    ensures to_nat(xs) < power(BASE, |xs|)
  {
    reveal to_nat();
    reveal power();
    if |xs| != 0 {
      var len' := |xs| - 1;
      var pow := power(BASE, len');
      calc {
        to_nat(xs);
        to_nat(drop_last(xs)) + last(xs) * pow;
        < { lemma_seq_nat_bound(drop_last(xs)); }
        pow + last(xs) * pow;
        <=
          {
            assert last(xs) <= BASE - 1;
            lemma_power_positive_auto();
            lemma_mul_inequality_auto();
          }
        pow + (BASE - 1) * pow;
        power(BASE, len' + 1);
      }
    }
  }

  function method {:opaque} prefix_nat(xs: seq<BaseType>, i: nat): nat
    requires 0 <= i <= |xs|
  {
    to_nat(xs[..i])
  }

  lemma lemma_prefix_equivalence(xs: seq<BaseType>, ys: seq<BaseType>, i: nat)
    requires 0 <= i <= |xs| && 0 <= i <= |ys|
    requires xs[..i] == ys[..i]
    ensures prefix_nat(xs, i) == prefix_nat(ys, i)
  {
    reveal prefix_nat();
  }

  /* Proves the nat representation of a prefix based on a smmaller prefix. */
  lemma lemma_prefix_nat(xs: seq<BaseType>, i: nat)
    requires 1 <= i < |xs|
    ensures prefix_nat(xs, i)
         == prefix_nat(xs, i - 1) + xs[i - 1] * power(BASE, i - 1)
  {
    assert xs[..i][..i-1] == xs[..i-1];
    reveal prefix_nat();
    reveal to_nat();
  }

  /* Proves mod equivalence between the nat representation of a sequence and
  the lsw of the sequence.*/
  lemma lemma_seq_lsw_mod_equivalence(xs: seq<BaseType>)
    requires |xs| >= 1;
    ensures is_mod_equivalent(to_nat(xs), xs[0], BASE);
  {
    if |xs| == 1 {
      lemma_seq_len_1_nat(xs);
    } else {
      assert is_mod_equivalent(to_nat(xs), xs[0], BASE) by {
        var len' := |xs| - 1;
        var pow := power(BASE, len');
        var xs' := drop_last(xs);

        calc ==> {
          true;
            { reveal to_nat(); }
          is_mod_equivalent(to_nat(xs), to_nat(xs') + last(xs) * pow, BASE);
            {
              lemma_power_mod_auto();
              lemma_mul_mod_noop_general_auto();
              assert is_mod_equivalent(last(xs) * pow, 0, BASE);
            }
          is_mod_equivalent(to_nat(xs), to_nat(xs'), BASE);
            { lemma_seq_lsw_mod_equivalence(xs'); }
          is_mod_equivalent(to_nat(xs), xs[0], BASE);
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // to_seq definition and lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Converts a nat to a sequence. */
  function method {:opaque} to_seq(x: nat): seq<BaseType>
    decreases x
  {
    if x == 0 then []
    else
      lemma_div_basics_auto();
      to_seq(x / BASE) + [x % BASE]
  }


  //////////////////////////////////////////////////////////////////////////////
  //
  // Sequences with zeros
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Generates a sequence of zeros with length len. */
  function method {:opaque} seq_zero(len: nat): (zs: seq<BaseType>)
    ensures |zs| == len
  {
    if len == 0 then [] else seq_zero(len - 1) + [0]
  }

  /* nat representation of an all zero sequence is 0. */
  lemma lemma_seq_zero_nat(len: nat)
    ensures to_nat(seq_zero(len)) == 0
  {
    reveal to_nat();
    if len > 0{
      calc {
        to_nat(seq_zero(len));
          { reveal seq_zero(); }
        to_nat(seq_zero(len - 1) + [0]);
        to_nat(seq_zero(len - 1)) + 0 * power(BASE, len - 1);
          {
            lemma_seq_zero_nat(len - 1);
            lemma_mul_basics_auto();
          }
        0;
      }
    }
  }

  /* Adding a zero as the least significant bit is equal to multiplying the
  number by BASE. */
  lemma lemma_seq_prepend_zero(xs: seq<BaseType>)
    ensures to_nat([0] + xs) == to_nat(xs) * BASE
  {
    reveal to_nat();
    if |xs| == 0 {
      lemma_mul_basics_auto();
    } else {
      calc {
        to_nat([0] + xs);
          { assert drop_last([0] + xs) == [0] + drop_last(xs); }
        to_nat([0] + drop_last(xs)) + last(xs) * power(BASE, |xs|);
          { lemma_seq_prepend_zero(drop_last(xs)); }
        to_nat(drop_last(xs)) * BASE + last(xs) * power(BASE, |xs|);
          {
            reveal power();
            lemma_mul_properties();
          }
        (to_nat(drop_last(xs)) + last(xs) * power(BASE, |xs| - 1)) * BASE;
        to_nat(xs) * BASE;
      }
    }
  }

  /* Adding zero(s) as the most significant bit(s) does not change the value of
  the number. */
  lemma lemma_seq_append_zero(xs': seq<BaseType>, xs: seq<BaseType>) 
    requires |xs'| < |xs|
    requires var len' := |xs'|;
      && drop_last(xs) == xs'
      && xs[len'..] == seq(|xs| - len', i => 0)
    ensures to_nat(xs') == to_nat(xs)
  {
    var len, len' := |xs|, |xs'|;
    reveal to_nat();
    if len != len' + 1 {
      calc == {
        to_nat(xs);
        to_nat(drop_last(xs)) + last(xs) * power(BASE, len - 1);
        to_nat(drop_last(xs));
          { lemma_seq_append_zero(xs', drop_last(xs)); }
        to_nat(xs');
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Addition and subtraction
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Adds two sequences. */
  function method {:opaque} seq_add(xs: seq<BaseType>,
                                    ys: seq<BaseType>): (seq<BaseType>, nat)
    requires |xs| == |ys|
    ensures var (zs, cout) := seq_add(xs, ys); |zs| == |xs|
  {
    reveal seq_add();
    if |xs| == 0 then ([], 0)
    else
      var (zs', cin) := seq_add(drop_last(xs), drop_last(ys));
      var sum: int := last(xs) + last(ys) + cin;
      var (sum_out, cout) := if sum < BASE then (sum, 0) else (sum - BASE, 1);
      (zs' + [sum_out], cout)
  }

  /* Proves seq_add yields the same value as converting the sequences to nats,
  then adding them. */
  lemma lemma_seq_add_nat(xs: seq<BaseType>,
                          ys: seq<BaseType>,
                          zs: seq<BaseType>,
                          cout: nat)
    requires |xs| == |ys|
    requires seq_add(xs, ys) == (zs, cout)
    ensures to_nat(xs) + to_nat(ys) == to_nat(zs) + cout * power(BASE, |xs|)
  {
    reveal seq_add();
    reveal to_nat();
    if |xs| == 0 {
      reveal power();
    } else {
      var len' := |xs| - 1;
      var pow := power(BASE, len');
      var (zs', cin) := seq_add(drop_last(xs), drop_last(ys));
      var sum: int := last(xs) + last(ys) + cin;
      var z := if sum < BASE then sum else sum - BASE;
      assert sum == z + cout * BASE;

      calc {
        to_nat(zs);
        to_nat(zs') + z * pow;
          { lemma_seq_add_nat(drop_last(xs), drop_last(ys), zs', cin); }
        to_nat(drop_last(xs)) + to_nat(drop_last(ys)) - cin * pow + z * pow;
          {
            lemma_mul_equality_auto();
            assert sum * pow == (z + cout * BASE) * pow;
            lemma_mul_is_distributive_auto();
          } 
        to_nat(xs) + to_nat(ys) - cout * BASE * pow;
          {
            lemma_mul_is_associative(cout, BASE, pow);
            reveal power();
          }
        to_nat(xs) + to_nat(ys) - cout * power(BASE, |xs|);
      }
    }
  }

  /* Subtracts two sequences. */
  function method {:opaque} seq_sub(xs: seq<BaseType>,
                                    ys: seq<BaseType>): (seq<BaseType>, nat)
    requires |xs| == |ys|
    ensures var (zs, cout) := seq_sub(xs, ys); |zs| == |xs|
  {
    reveal seq_sub();
    if |xs| == 0 then ([], 0)
    else 
      var (zs, cin) := seq_sub(drop_last(xs), drop_last(ys));
      var (diff_out, cout) := if last(xs) >= last(ys) + cin
                              then (last(xs) - last(ys) - cin, 0)
                              else (BASE + last(xs) - last(ys) - cin, 1);
      (zs + [diff_out], cout)
  }

  /* Proves seq_sub yields the same value as converting the sequences to nats,
  then subtracting them. */
  lemma lemma_seq_sub_nat(xs: seq<BaseType>,
                          ys: seq<BaseType>,
                          zs: seq<BaseType>,
                          cout: nat)
    requires |xs| == |ys|
    requires seq_sub(xs, ys) == (zs, cout)
    ensures to_nat(xs) - to_nat(ys) + cout * power(BASE, |xs|) == to_nat(zs)
  {
    reveal seq_sub();
    reveal to_nat();
    if |xs| == 0 {
      reveal power();
    } else {
      var len' := |xs| - 1;
      var pow := power(BASE, len');
      var (zs', cin) := seq_sub(drop_last(xs), drop_last(ys));
      var z := if last(xs) >= last(ys) + cin
               then last(xs) - last(ys) - cin
               else BASE + last(xs) - last(ys) - cin;
      assert cout * BASE + last(xs) - cin - last(ys) == z;
      
      calc {
        to_nat(zs);
        to_nat(zs') + z * pow;
          { lemma_seq_sub_nat(drop_last(xs), drop_last(ys), zs', cin); }
        to_nat(drop_last(xs)) - to_nat(drop_last(ys)) + cin * pow + z * pow;
          {
            lemma_mul_equality_auto();
            assert pow * (cout * BASE + last(xs) - cin - last(ys)) == pow * z;
            lemma_mul_is_distributive_auto();
          }
        to_nat(xs) - to_nat(ys) + cout * BASE * pow;
          {
            lemma_mul_is_associative(cout, BASE, pow);
            reveal power();
          }
        to_nat(xs) - to_nat(ys) + cout * power(BASE, |xs|);
      }
    }
  }

}
