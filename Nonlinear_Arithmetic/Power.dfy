include "Mul.dfy"
include "Mul-Internals.dfy"

module Power {
  import opened Mul
  import opened MulInternals

  function method {:opaque} power(b:int, e:nat) : int
    decreases e
  {
    if (e==0) then
      1
    else
      b*power(b,e-1)
  }

  /* A number raised to the power of 0 equals 1. */
  lemma lemma_power_0(b:int)
    ensures power(b,0) == 1
  {
    reveal power();
  }

  /* A number raised to the power of 1 equals the number itself. */
  lemma lemma_power_1(b:int)
    ensures power(b,1) == b
  {
    calc {
      power(b,1);
        { reveal power(); }
      b*power(b,0);
        { lemma_power_0(b); }
      b*1;
        { lemma_mul_basics_auto(); }
      b;
    }
  }

  /* 0 raised to a positive power equals 0. */
  lemma lemma_0_power(e:nat)
    requires e > 0
    ensures power(0,e) == 0
  {
    reveal power();
    lemma_mul_basics_auto();
    if (e != 1)
    {
      lemma_0_power(e - 1);
    }
  }

  /* 1 raised to any power equals 1. */
  lemma lemma_1_power(e:nat)
    ensures power(1,e) == 1
  {
    reveal power();
    lemma_mul_basics_auto();
    if (e != 0)
    {
      lemma_1_power(e - 1);
    }
  }

  /* Add exponents when multiplying powers with the same base. */
  lemma lemma_power_adds(b:int, e1:nat, e2:nat)
    decreases e1
    ensures power(b,e1)*power(b,e2) == power(b,e1+e2)
  {
    if (e1==0)
    {
      calc {
        power(b,e1)*power(b,e2);
          { lemma_power_0(b); }
        1*power(b,e2);
          { lemma_mul_basics_auto(); }
        power(b,0+e2);
      }
    }
    else
    {
      calc {
        power(b,e1)*power(b,e2);
          { reveal power(); }
        (b*power(b,e1-1))*power(b,e2);
          { lemma_mul_is_associative_auto(); }
        b*(power(b,e1-1)*power(b,e2));
          { lemma_power_adds(b, e1-1, e2); }
        b*power(b,e1-1+e2);
          { reveal power(); }
        power(b,e1+e2);
      }
    }
  }

  /* Multiply exponents to find the power of a power. */
  lemma lemma_power_multiplies(a:int,b:nat,c:nat)
    decreases c
    ensures 0<=b*c
    ensures power(a,b*c) == power(power(a,b),c)
  {
    lemma_mul_nonnegative(b,c);
    if (0==c)
    {
      lemma_mul_basics_auto();
      calc {
        power(a,b*c);
          { lemma_power_0(a); }
        1;
          { lemma_power_0(power(a,b)); }
        power(power(a,b),c);
      }
    }
    else
    {
      calc {
        b*c - b;
          { lemma_mul_basics_auto(); }
        b*c - mul(b,1);
          { lemma_mul_is_distributive_auto(); }
        b*(c-1);
      }
      lemma_mul_nonnegative(b,c-1);
      assert 0 <= b*c-b;

      calc {
        power(a,b*c);
        power(a,b+b*c-b);
          { lemma_power_adds(a,b,b*c-b); }
        power(a,b)*power(a,b*c-b);
        power(a,b)*power(a,b*(c-1));
          { lemma_power_multiplies(a,b,c-1); }
        power(a,b)*power(power(a,b),c-1);
          { reveal power(); }
        power(power(a,b),c);
      }
    }
  }

  /* Distribute the power to each factor of a product. */
  lemma lemma_power_distributes(a:int, b:int, e:nat)
    decreases e
    ensures power(a*b, e) == power(a, e) * power(b, e)
  {
    reveal power();
    lemma_mul_basics_auto();
    if (e > 0)
    {
      calc {
        power(a*b, e);
        (a*b) * power(a*b, e - 1);
          { lemma_power_distributes(a, b, e - 1); }
        (a*b) * (power(a, e - 1) * power(b, e - 1));
          { lemma_mul_is_associative_auto(); lemma_mul_is_commutative_auto(); }
        (a*power(a, e - 1)) * (b*power(b, e - 1));
        power(a,e) * power(b,e);
      }
      lemma_mul_is_distributive_auto();
    }
  }

  lemma lemma_power_auto()
    ensures  forall x:int {:trigger power(x, 0)} :: power(x, 0) == 1
    ensures  forall x:int {:trigger power(x, 1)} :: power(x, 1) == x
    ensures  forall x:int, y:int {:trigger power(x, y)} :: y == 0 ==> power(x, y) == 1
    ensures  forall x:int, y:int {:trigger power(x, y)} :: y == 1 ==> power(x, y) == x // ...
    ensures  forall x:int, y:int {:trigger x * y} :: 0 < x && 0 < y ==> x <= x * y
    ensures  forall x:int, y:int {:trigger x * y} :: 0 < x && 1 < y ==> x < x * y
    ensures  forall x:int, y:nat, z:nat {:trigger power(x, y + z)} :: power(x, y + z) == power(x, y) * power(x, z)
    ensures  forall x:int, y:nat, z:nat {:trigger power(x, y - z)} :: y >= z ==> power(x, y - z) * power(x, z) == power(x, y)
    ensures  forall x:int, y:int, z:nat {:trigger power(x * y, z)} :: power(x * y, z) == power(x, z) * power(y, z)
  {
    reveal power();

    forall x:int
      ensures power(x, 0) == 1
      ensures power(x, 1) == x
    {
      lemma_power_0(x);
      lemma_power_1(x);
    }

    forall x:int, y:int, z:nat {:trigger power(x * y, z)}
      ensures power(x * y, z) == power(x, z) * power(y, z)
    {
      lemma_power_distributes(x, y, z);
    }

    forall x:int, y:nat, z:nat {:trigger power(x, y + z)}
      ensures power(x, y + z) == power(x, y) * power(x, z)
    {
      lemma_power_adds(x, y, z);
    }

    forall x:int, y:nat, z:nat {:trigger power(x, y - z)} | y >= z
      ensures power(x, y - z) * power(x, z) == power(x, y)
    {
      lemma_power_adds(x, y - z, z);
    }

    forall x:int, y:int {:trigger x * y} | 0 < x && 0 < y
      ensures x <= x * y
    {
      lemma_mul_auto();
      lemma_mul_increases_auto();
      lemma_mul_strictly_increases_auto();
    }

    forall x:int, y:int {:trigger x * y} | 0 < x && 1 < y
      ensures x < x * y
    {
      lemma_mul_auto();
      lemma_mul_increases_auto();
      lemma_mul_strictly_increases_auto();
    }
  }

  /* A positive number raised to any power is positive. */
  lemma lemma_power_positive(b:int, e:nat)
    requires 0<b
    ensures  0<power(b,e)
  {
    lemma_power_auto();
    lemma_mul_auto_induction(e, u => 0 <= u ==> 0 < power(b, u));
  }

  /* A positive number raised to a power increases as the power increases. */
  lemma lemma_power_increases(b:nat,e1:nat,e2:nat)
    requires 0<b
    requires e1 <= e2
    ensures power(b,e1) <= power(b,e2)
  {
    lemma_power_auto();
    var f := e => 0 <= e ==> power(b, e1) <= power(b, e1 + e);
    forall i {:trigger is_le(0, i)} | is_le(0, i) && f(i)
      ensures f(i + 1)
    {
      calc {
        power(b, e1 + i);
        <= { lemma_power_positive(b, e1 + i);
            lemma_mul_left_inequality(power(b, e1 + i), 1, b); }
          power(b, e1 + i) * b;
        == { lemma_power_1(b); }
          power(b, e1 + i) * power(b, 1);
        == { lemma_power_adds(b, e1 + i, 1); }
          power(b, e1 + i + 1);
      }
    }
    lemma_mul_auto_induction(e2 - e1, f);
  }

  /* A positive number raised to a power strictly increases as the power
  strictly increases. */
  lemma lemma_power_strictly_increases(b:nat,e1:nat,e2:nat)
    requires 1<b
    requires e1 < e2
    ensures power(b,e1) < power(b,e2)
  {
    lemma_power_auto();
    var f := e => 0 < e ==> power(b, e1) < power(b, e1 + e);
    forall i {:trigger is_le(0, i)} | is_le(0, i) && f(i)
      ensures f(i + 1)
    {
      calc {
        power(b, e1 + i);
        <= { lemma_power_positive(b, e1 + i);
            lemma_mul_left_inequality(power(b, e1 + i), 1, b); }
          power(b, e1 + i) * b;
        == { lemma_power_1(b); }
          power(b, e1 + i) * power(b, 1);
        == { lemma_power_adds(b, e1 + i, 1); }
          power(b, e1 + i + 1);
      }
    }
    lemma_mul_auto_induction(e2 - e1, f);
  }

  /* Squaring a number is equal to raising the number to a power of 2. */
  lemma lemma_square_is_power_2(x:nat)
    ensures power(x,2) == x*x
  {
    reveal power();
  }

}
