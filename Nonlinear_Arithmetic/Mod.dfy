include "Mod-Internals.dfy"
include "Power.dfy"

module Mod {

  import opened ModInternals
  import opened ModNonlinear
  import opened Power
  import opened MulInternals
  import opened MulNonlinear
  import opened Mul
    
    /*  */
  lemma lemma_mod_basics()
    ensures forall m:int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x:int, m:int {:trigger (x%m) % m} :: m > 0 ==> (x%m) % m == x%m
  {
    forall m:int | m > 0
      ensures m % m == 0
    {
      lemma_mod_auto(m);
    }
    forall x:int, m:int | m > 0
      ensures (x % m) % m == x % m
    {
      lemma_mod_auto(m);
    }
  }

  lemma lemma_mod_properties()
    ensures forall m:int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x:int, m:int {:trigger (x%m) % m} :: m > 0 ==> (x%m) % m == x%m
    ensures forall x:int, m:int {:trigger x%m} :: m > 0 ==> 0 <= x%m < m
  {
    lemma_mod_basics();

    forall x:int, m:int | m > 0
      ensures m > 0 ==> 0 <= x%m < m
    {
      lemma_mod_auto(m);
    }
  }

  /* the remainder of a natural number x divided by a natural number d will be less
  than or equal to x */
  lemma lemma_mod_decreases(x:nat, d:nat)
    requires 0 < d
    ensures x%d <= x
  {
    lemma_mod_auto(d);
  }

  /* the remainder of adding the divisor m to the dividend b will be the same
  as simply performing b % m */
  lemma lemma_mod_add_multiples_vanish(b:int, m:int)
    requires 0 < m
    ensures (m + b) % m == b % m
  {
    lemma_mod_auto(m);
  }

  /* the remainder of aubtracting the divisor m from the dividend b will be the same
  as simply performing b % m */
  lemma lemma_mod_sub_multiples_vanish(b:int, m:int)
    requires 0 < m
    ensures (-m + b) % m == b % m
  {
    lemma_mod_auto(m);
  }

  /* the remainder of adding any multiple of the divisor m to the dividend b will be the same
  as simply performing b % m */ 
  lemma lemma_mod_multiples_vanish(a:int, b:int, m:int)
    decreases if a>0 then a else -a
    requires 0 < m
    ensures (m*a + b) % m == b % m
  {
    lemma_mod_auto(m);
    lemma_mul_induction_auto(a, u => (m*u + b) % m == b % m);
  }

  /* describes expanded and succinct version of modulus operator in relation to addition (read "ensures") */
  lemma lemma_add_mod_noop(x:int, y:int, m:int)
    requires 0 < m
    ensures ((x % m) + (y % m)) % m == (x+y) % m
  {
    lemma_mod_auto(m);
  }

  /* describes expanded and succinct version of modulus operator in relation to addition (read "ensures") */
  lemma lemma_add_mod_noop_right(x:int, y:int, m:int)
    requires 0 < m
    ensures (x + (y % m)) % m == (x+y) % m
  {
    lemma_mod_auto(m);
  }

  /* proves modulus equivalence in two forms */
  lemma lemma_mod_equivalence(x:int, y:int, m:int)
    requires 0 < m
    ensures x % m == y % m <==> (x - y) % m == 0
  {
    lemma_mod_auto(m);
  }

  /* describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures") */
  lemma lemma_sub_mod_noop(x:int, y:int, m:int)
    requires 0 < m
    ensures ((x % m) - (y % m)) % m == (x-y) % m
  {
    lemma_mod_auto(m);
  }

  /* describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures") */
  lemma lemma_sub_mod_noop_right(x:int, y:int, m:int)
    requires 0 < m
    ensures (x - (y % m)) % m == (x-y) % m
  {
    lemma_mod_auto(m);
  }

  /*  */
  lemma lemma_mod_adds(a:int, b:int, d:int)
    requires 0<d
    ensures a%d + b%d == (a+b)%d + d*((a%d + b%d)/d)
    ensures (a%d + b%d) < d ==> a%d + b%d == (a+b)%d
  {
    lemma_mul_auto();
    lemma_div_auto(d);
  }

  lemma {:timeLimitMultiplier 2} lemma_mod_neg_neg(x:int, d:int)
    requires d > 0
    ensures x%d == (x*(1-d))%d
  {
    forall ensures (x - x * d) % d == x % d
    {
      lemma_mod_auto(d);
      var f := i => (x - i * d) % d == x % d;
      assert  mul_auto() ==> && f(0)
                            && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && f(i) ==> f(i + 1))
                            && (forall i {:trigger is_le(i, 0)} :: is_le(i, 0) && f(i) ==> f(i - 1));
      lemma_mul_induction_auto(x, f);
    }
    lemma_mul_auto();
  }

  lemma {:timeLimitMultiplier 2} lemma_fundamental_div_mod_converse(x:int, d:int, q:int, r:int)
    requires d != 0
    requires 0 <= r < d
    requires x == q * d + r
    ensures q == x/d
    ensures r == x%d
  {
    lemma_div_auto(d);
    lemma_mul_induction_auto(q, u => u == (u * d + r) / d);
    lemma_mul_induction_auto(q, u => r == (u * d + r) % d);
  }

  lemma lemma_mod_pos_bound(x:int, m:int)
    decreases x
    requires 0 <= x
    requires 0 < m
    ensures  0 <= x%m < m
  {
    lemma_mod_auto(m);
  }

  lemma lemma_mul_mod_noop_left(x:int, y:int, m:int)
    requires 0 < m
    ensures (x % m)*y % m == x*y % m
  {
    lemma_mod_auto(m);
    lemma_mul_induction_auto(y, u => (x % m)*u % m == x*u % m);
  }

  lemma lemma_mul_mod_noop_right(x:int, y:int, m:int)
    requires 0 < m
    ensures x*(y % m) % m == (x*y) % m
  {
    lemma_mod_auto(m);
    lemma_mul_induction_auto(x, u => u*(y % m) % m == (u*y) % m);
  }

  lemma lemma_mul_mod_noop_general(x:int, y:int, m:int)
    requires 0 < m
    ensures ((x % m) * y      ) % m == (x * y) % m
    ensures ( x      * (y % m)) % m == (x * y) % m
    ensures ((x % m) * (y % m)) % m == (x * y) % m
  {
    lemma_mod_properties();
    lemma_mul_mod_noop_left(x, y, m);
    lemma_mul_mod_noop_right(x, y, m);
    lemma_mul_mod_noop_right(x % m, y, m);
  }


  lemma lemma_mul_mod_noop(x:int, y:int, m:int)
    requires 0 < m
    ensures (x % m) * (y % m) % m == (x*y) % m
  {
    lemma_mul_mod_noop_general(x, y, m);
  }

  lemma lemma_power_mod_noop(b:int, e:nat, m:int)
    decreases e
    requires 0 < m
    ensures power(b % m, e) % m == power(b, e) % m
  {
    reveal power();
    lemma_mod_properties();
    if (e > 0)
    {
      calc {
        power(b % m, e) % m;
        ((b % m) * power(b % m, e - 1)) % m;
          { lemma_mul_mod_noop_general(b, power(b % m, e - 1), m); }
        ((b % m) * (power(b % m, e - 1) % m) % m) % m;
          { lemma_power_mod_noop(b, e - 1, m); }
        ((b % m) * (power(b, e - 1) % m) % m) % m;
          { lemma_mul_mod_noop_general(b, power(b, e - 1), m); }
        (b * (power(b, e - 1)) % m) % m;
        (b * (power(b, e - 1))) % m;
        power(b, e) % m;
      }
    }
  }

  lemma lemma_mod_subtraction(x:nat, s:nat, d:nat)
    requires 0<d
    requires 0<=s<=x%d
    ensures x%d - s%d == (x-s)%d
  {
    lemma_mod_auto(d);
  }

  /* the remainder can increase with a larger divisor */
  lemma lemma_mod_ordering(x:nat, k:nat, d:nat)
    requires 1<d
    requires 0<k
    ensures 0<d*k
    ensures x%d <= x%(d*k)
  {
    lemma_mul_strictly_increases(d,k);
    calc {
      x%d + d*(x/d);
        { lemma_fundamental_div_mod(x,d); }
      x;
        { lemma_fundamental_div_mod(x,d*k); }
      x%(d*k) + (d*k)*(x/(d*k));
        { lemma_mul_is_associative_auto(); }
      x%(d*k) + d*(k*(x/(d*k)));
    }
    calc {
      x%d;
        { lemma_mod_properties(); }
      (x%d) % d;
        { lemma_mod_multiples_vanish(x/d - k*(x/(d*k)), x%d, d); }
      (x%d + d*(x/d - k*(x/(d*k)))) % d;
        { lemma_mul_is_distributive_sub_auto(); }
      (x%d + d*(x/d) - d*(k*(x/(d*k)))) % d;
      (x%(d*k)) % d;
        <= { lemma_mod_properties();
            lemma_mod_decreases(x%(d*k), d); }
      x%(d*k);
    }
  }

}