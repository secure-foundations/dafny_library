include "DivMod.dfy"
include "../Mathematics.dfy"
include "Internals/ModInternalsNonlinear.dfy"
include "Internals/MulInternals.dfy"
include "Mul.dfy"
include "Power.dfy"

module Power2 {
  import opened DivMod
  import opened Mathematics
  import opened ModInternalsNonlinear
  import opened Mul
  import opened MulInternals
  import opened Power

  function method {:opaque} power2(e: nat): nat
    ensures power2(e) > 0
  {
    if e == 0 then
      1
    else
      2 * power2(e - 1)
  }

  lemma lemma_power2_0()
    ensures power2(0) == 1
  {
    reveal_power2();
  }

  lemma lemma_power2_1()
    ensures power2(1) == 2
  {
    reveal_power2();
  }

  /* power2() is equivalent to power() with base 2. */
  lemma lemma_power2_is_power_2(e: nat)
    ensures power2(e) == power(2, e)
  {
    reveal_power();
    reveal_power2();
  
    if e != 0 {
      lemma_power2_is_power_2(e - 1);
    }
  }

  lemma lemma_power2_is_power_2_auto()
    ensures forall e: nat {:trigger power2(e)} :: power2(e) == power(2, e)
  {
    reveal_power();
    reveal_power2();
    
    forall e: nat {:trigger power2(e)}
      ensures power2(e) == power(2, e)
    {
      lemma_power2_is_power_2(e);
    }
  }

  /* Groups properties of powers with base 2. */
  lemma lemma_power2_auto()
    ensures power2(0) == 1
    ensures power2(1) == 2
    ensures forall e1: nat, e2: nat {:trigger power2(e1 + e2)} :: power2(e1 + e2) == power2(e1) * power2(e2)
    ensures forall e1: nat, e2: nat {:trigger power2(e1 - e2)} :: e1 >= e2 ==> power2(e1 - e2) * power2(e2) == power2(e1)
  {
    reveal_power2();
    lemma_power2_is_power_2_auto();
    lemma_power_auto();
  }

  /* Add exponents when multiplying powers with base 2. */
  lemma lemma_power2_adds(e1: nat, e2: nat)
    decreases e2
    ensures power2(e1 + e2) == power2(e1) * power2(e2)
  {
    reveal_power2();
    lemma_power2_auto();
  }

  lemma lemma_power_adds_auto()
    ensures forall e1: nat, e2: nat {:trigger power2(e1 + e2)}
      :: power2(e1 + e2) == power2(e1) * power2(e2)
  {
    reveal_power2();
    forall e1: nat, e2: nat {:trigger power2(e1 + e2)}
      ensures power2(e1 + e2) == power2(e1) * power2(e2)
    {
      lemma_power2_adds(e1, e2);
    }
  }

  /* Subtract exponents when dividing powers with base 2. */
  lemma lemma_power2_subtracts(e1: nat, e2: nat)
    requires e1 <= e2
    ensures power2(e2 - e1) == power2(e2) / power2(e1) >= 0
  {
    calc {
      power2(e2) / power2(e1);
        { lemma_power2_adds(e2 - e1, e1); }
      power2(e2 - e1) * power2(e1) / power2(e1);
        { lemma_div_by_multiple(power2(e2 - e1), power2(e1)); }
      power2(e2 - e1);
    }
  }

  lemma lemma_power2_subtracts_auto()
    ensures forall e1: nat, e2: nat {:trigger power2(e2 - e1)}
      :: e1 <= e2 ==> power2(e2 - e1) == power2(e2) / power2(e1) >= 0
  {
    reveal_power2();
    forall e1: nat, e2: nat {:trigger power2(e2 - e1)} | e1 <= e2
      ensures power2(e2 - e1) == power2(e2) / power2(e1) >= 0
    {
      lemma_power2_subtracts(e1, e2);
    }
  }

  /* Multiply exponents to find the power of a power of 2. */
  lemma lemma_power2_multiplies(e1: nat, e2: nat)
    ensures 0 <= e1 * e2
    ensures power(power2(e1), e2) == power2(e1 * e2)
  {
    lemma_mul_nonnegative(e1, e2);
    lemma_power2_is_power_2(e1);
    lemma_power_multiplies(2, e1, e2);
    lemma_power2_is_power_2(e1 * e2);
  }

  lemma lemma_power2_multiplies_auto()
    ensures forall e1: nat, e2: nat {:trigger power(power2(e1), e2)} :: 0 <= e1 * e2 && power(power2(e1), e2) == power2(e1 * e2)
  {
    reveal_power();
    reveal_power2();

    forall e1: nat, e2: nat
      ensures 0 <= e1 * e2 && power(power2(e1), e2) == power2(e1 * e2)
    {
      lemma_power2_multiplies(e1, e2);
      lemma_power2_auto();
      lemma_power2_is_power_2_auto();
    }
  }

  /* 2 raised to a power strictly increases as the power strictly increases. */
  lemma lemma_power2_strictly_increases(e1: nat, e2: nat)
    requires e1 < e2
    ensures power2(e1) < power2(e2)
  {
    lemma_power2_auto();
    lemma_mul_induction_auto(e2 - e1, e => 0 < e ==> power2(e1) < power2(e1 + e));
  }

  lemma lemma_power2_strictly_increases_auto()
    ensures forall e1: nat, e2: nat {:trigger power2(e1), power2(e2)}
      :: e1 < e2 ==> power2(e1) < power2(e2)
  {
    reveal_power2();
    forall e1: nat, e2: nat {:trigger power2(e1), power2(e2)} | e1 < e2
      ensures power2(e1) < power2(e2)
    {
      lemma_power2_strictly_increases(e1, e2);
    }
  }

  /* 2 raised to a power increases as the power increases. */
  lemma lemma_power2_increases(e1: nat, e2: nat)
    requires e1 <= e2
    ensures power2(e1) <= power2(e2)
  {
    lemma_power2_auto();
    lemma_mul_induction_auto(e2 - e1, e => 0 <= e ==> power2(e1) <= power2(e1 + e));
  }

  lemma lemma_power2_increases_auto()
    ensures forall e1: nat, e2: nat {:trigger power2(e1), power2(e2)}
      :: e1 <= e2 ==> power2(e1) <= power2(e2)
  {
    reveal_power2();
    forall e1: nat, e2: nat {:trigger power2(e1), power2(e2)} | e1 <= e2
      ensures power2(e1) <= power2(e2)
    {
      lemma_power2_increases(e1, e2);
    }
  }

  /* A power strictly increases as 2 raised to the power strictly increases. */
  lemma lemma_power2_strictly_increases_converse(e1: nat, e2: nat)
    requires power2(e1) < power2(e2)
    ensures e1 < e2
  {
    if e1 >= e2 {
      lemma_power2_increases(e2, e1);
      assert false;
    }
  }

  lemma lemma_power2_strictly_increases_converse_auto()
    ensures forall e1: nat, e2: nat {:trigger power2(e1), power2(e2)}
      :: power2(e1) < power2(e2) ==> e1 < e2
  {
    reveal_power2();
    forall e1: nat, e2: nat {:trigger power2(e1), power2(e2)}
      | power2(e1) < power2(e2)
      ensures e1 < e2
    {
      lemma_power2_strictly_increases_converse(e1, e2);
    }
  }

  /* A power increases as 2 raised to the power increases. */
  lemma lemma_power2_increases_converse(e1: nat, e2: nat)
    requires power2(e1) <= power2(e2)
    ensures e1 <= e2
  {
    if e1 > e2 {
      lemma_power2_strictly_increases(e2, e1);
      assert false;
    }
  }

  lemma lemma_power2_increases_converse_auto()
    ensures forall e1: nat, e2: nat {:trigger power2(e1), power2(e2)}
      :: power2(e1) <= power2(e2) ==> e1 <= e2
  {
    reveal_power2();
    forall e1: nat, e2: nat {:trigger power2(e1), power2(e2)}
      | power2(e1) <= power2(e2)
      ensures e1 <= e2
    {
      lemma_power2_increases_converse(e1, e2);
    }
  }

  /* (2^xy)^z = (2^x)^yz */
  lemma lemma_pull_out_powers_of_2(x: nat, y: nat, z: nat)
    ensures 0 <= x * y
    ensures 0 <= y * z
    ensures power(power2(x * y), z) == power(power2(x), y * z)
  {
    lemma_mul_nonnegative(x, y);
    lemma_mul_nonnegative(y, z);
    lemma_power_positive(2, x);
    calc {
      power(power2(x * y), z);
        { lemma_power2_is_power_2(x * y); }
      power(power(2, x * y), z);
        { lemma_power_multiplies(2, x, y); }
      power(power(power(2, x), y), z);
        { lemma_power_multiplies(power(2, x), y, z); }
      power(power(2, x), y * z);
        { lemma_power2_is_power_2(x); }
      power(power2(x), y * z);
    }
  }

  lemma lemma_pull_out_powers_of_2_auto()
    ensures forall y: nat, z: nat {:trigger z * y} :: 0 <= z * y && 0 <= y * z
    ensures forall x: nat, y: nat, z: nat {:trigger power(power2(x * y), z)}
      :: power(power2(x * y), z) == power(power2(x), y * z)
  {
    reveal_power();
    reveal_power2();
    lemma_mul_nonnegative_auto();
    forall x: nat, y: nat, z: nat {:trigger power(power2(x * y), z)}
      ensures power(power2(x * y), z) == power(power2(x), y * z)
    {
      lemma_pull_out_powers_of_2(x, y, z);
    }
  }

  /* (2^e - 1) / 2 = 2^(e - 1) - 1 */
  lemma lemma_power2_mask_div_2(e: nat)
    requires 0 < e
    ensures (power2(e) - 1) / 2 == power2(e - 1) - 1
  {
    lemma_power2_auto();
    var f := e => 0 < e ==> (power2(e) - 1) / 2 == power2(e - 1) - 1;
    assert forall i {:trigger is_le(0, i)} :: is_le(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger is_le(i, 0)} :: is_le(i, 0) && f(i) ==> f(i - 1);
    lemma_mul_induction_auto(e, f);
  }

  lemma lemma_power2_mask_div_2_auto()
    ensures forall e: nat {:trigger power2(e)} :: 0 < e ==>
      (power2(e) - 1) / 2 == power2(e - 1) - 1
  {
    reveal_power2();
    forall e: nat {:trigger power2(e)} | 0 < e
      ensures (power2(e) - 1) / 2 == power2(e - 1) - 1
    {
      lemma_power2_mask_div_2(e);
    }
  }

  /* Inequality due to smaller numerator, same denominator. */
  lemma lemma_power2_division_inequality(x: nat, e1: nat, e2: nat)
    requires e2 <= e1
    requires x < power2(e1)
    ensures x / power2(e2) < power2(e1 - e2)
  {
    calc ==> {
      x / power2(e2) >= power2(e1 - e2);
        { lemma_mul_inequality(power2(e1 - e2), x / power2(e2), power2(e2)); }
      x / power2(e2) * power2(e2) >= power2(e1 - e2) * power2(e2);
        { lemma_fundamental_div_mod(x, power2(e2));
          lemma_mul_is_commutative_auto(); }
      x - x % power2(e2) >= power2(e1 - e2) * power2(e2);
        { lemma_power2_adds(e1 - e2, e2); }
      x - x % power2(e2) >= power2(e1);
        { lemma_mod_properties(); }
      x >= power2(e1);
      false;
    }
  }

  lemma lemma_power2_division_inequality_auto()
    ensures forall x: nat, e1: nat, e2: nat
      {:trigger x / power2(e2), power2(e1 - e2)}
      :: e2 <= e1 && x < power2(e1) ==> x / power2(e2) < power2(e1 - e2)
  {
    reveal_power2();
    forall x: nat, e1: nat, e2: nat {:trigger x / power2(e2), power2(e1 - e2)}
      | e2 <= e1 && x < power2(e1)
      ensures x / power2(e2) < power2(e1 - e2)
    {
      lemma_power2_division_inequality(x, e1, e2);
    }
  }

  lemma lemma_power2_2to64()
    ensures power2(0) == 0x1
    ensures power2(1) == 0x2
    ensures power2(2) == 0x4
    ensures power2(3) == 0x8
    ensures power2(4) == 0x10
    ensures power2(5) == 0x20
    ensures power2(6) == 0x40
    ensures power2(7) == 0x80
    ensures power2(8) == 0x100
    ensures power2(9) == 0x200
    ensures power2(10) == 0x400
    ensures power2(11) == 0x800
    ensures power2(12) == 0x1000
    ensures power2(13) == 0x2000
    ensures power2(14) == 0x4000
    ensures power2(15) == 0x8000
    ensures power2(16) == 0x10000
    ensures power2(17) == 0x20000
    ensures power2(18) == 0x40000
    ensures power2(19) == 0x80000
    ensures power2(20) == 0x100000
    ensures power2(21) == 0x200000
    ensures power2(22) == 0x400000
    ensures power2(23) == 0x800000
    ensures power2(24) == 0x1000000
    ensures power2(25) == 0x2000000
    ensures power2(26) == 0x4000000
    ensures power2(27) == 0x8000000
    ensures power2(28) == 0x10000000
    ensures power2(29) == 0x20000000
    ensures power2(30) == 0x40000000
    ensures power2(31) == 0x80000000
    ensures power2(32) == 0x100000000
    ensures power2(64) == 0x10000000000000000
  {
    reveal_power2();
  }

} 
