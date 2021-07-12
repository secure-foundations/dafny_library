include "Mod-Internals.dfy"
include "Power.dfy"

module Mod {

  import opened ModInternals
  import opened ModNonlinear
  import opened Power
  import opened MulInternals
  import opened MulNonlinear
  import opened Mul

  /* the common syntax of the modulus operation results in the same remainder as recursively
  calculating the modulus */
  lemma lemma_mod_is_mod_recursive(x:int, m:int)
    requires m > 0
    ensures mod_recursive(x, m) == x % m
    decreases if x < 0 then -x + m else x
  {
    reveal_mod_recursive();
    if x < 0 { 
      calc { 
        mod_recursive(x, m);
        mod_recursive(x + m, m);
          { lemma_mod_is_mod_recursive(x + m, m); }
        (x + m) % m;
          { lemma_add_mod_noop(x, m, m); } 
        ((x % m) + (m % m)) % m;
          { lemma_mod_basics(); }
        (x % m) % m;
          { lemma_mod_basics(); }
        x % m;
      }
    } else if x < m { 
      lemma_small_mod(x, m);
    } else {
      calc { 
        mod_recursive(x, m);
        mod_recursive(x - m, m);
          { lemma_mod_is_mod_recursive(x - m, m); }
        (x - m) % m;
          { lemma_sub_mod_noop(x, m, m); } 
        ((x % m) - (m % m)) % m;
          { lemma_mod_basics(); }
        (x % m) % m;
          { lemma_mod_basics(); }
        x % m;
      }
    }
  }

  /* the common syntax of the modulus operation results in the same remainder as recursively
  calculating the modulus for all integers */
  lemma lemma_mod_is_mod_recursive_auto()
    ensures forall x:int, d:int {:trigger x % d}:: d > 0 ==> mod_recursive(x, d) == x % d
  {
    reveal_mod_recursive();
    forall x:int, d:int | d > 0
      ensures mod_recursive(x, d) == x % d
    {
      lemma_mod_is_mod_recursive(x, d);
    }
  }

  /* proves basic properties of the modulus operation: any integer divided by itself does not have a
  remainder; performing (x % m) % m gives the same result as simply perfoming x % m  */
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

  /* describes the properties of the modulus operation including those described in lemma_mod_basics. 
  This lemma also states that the remainder of any division will be less than the divisor's value  */
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
  
  /* a dividend that is any multiple of the divisor will result in a remainder of 0 */
  lemma lemma_mod_multiples_basic(x:int, m:int)
    requires m > 0
    ensures  (x * m) % m == 0
  {
    lemma_mod_auto(m);
    lemma_mul_induction_auto(x, u => (u * m) % m == 0);
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

  /* proves equivalent forms of modulus addition */
  lemma lemma_mod_adds(a:int, b:int, d:int)
    requires 0<d
    ensures a%d + b%d == (a+b)%d + d*((a%d + b%d)/d)
    ensures (a%d + b%d) < d ==> a%d + b%d == (a+b)%d
  {
    lemma_mul_auto();
    lemma_div_auto(d);
  }

  /* comment more confusing than reading ensures clause */
  lemma {:timeLimitMultiplier 2} lemma_mod_neg_neg(x:int, d:int)
    requires 0 < d
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
  
  /* proves the validity of the quotient and remainder */
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

  /* the remainder of any natural number x divided by a positive integer m is always less than m */
  lemma lemma_mod_pos_bound(x:int, m:int)
    decreases x
    requires 0 <= x
    requires 0 < m
    ensures  0 <= x%m < m
  {
    lemma_mod_auto(m);
  }
  
  /* ensures easier to follow than a comment would be */
  lemma lemma_mul_mod_noop_left(x:int, y:int, m:int)
    requires 0 < m
    ensures (x % m)*y % m == x*y % m
  {
    lemma_mod_auto(m);
    lemma_mul_induction_auto(y, u => (x % m)*u % m == x*u % m);
  }
  
  /* ensures easier to follow than a comment would be */
  lemma lemma_mul_mod_noop_right(x:int, y:int, m:int)
    requires 0 < m
    ensures x*(y % m) % m == (x*y) % m
  {
    lemma_mod_auto(m);
    lemma_mul_induction_auto(x, u => u*(y % m) % m == (u*y) % m);
  }
  
  /* combines previous no-op mod lemmas into a general, overarching lemma */
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
  
  /* exponentiating the remainder of b/m is equivalent to exponentiating b and then 
  dividing that product by m */
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
  
  /* proves equivalent forms of modulus subtraction */
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
  
  lemma lemma_mod_mod(x:int, a:int, b:int)
    requires 0<a
    requires 0<b
    ensures 0<a*b
    ensures (x%(a*b))%a == x%a
  {
    lemma_mul_strictly_positive_auto();
    calc {
      x;
        { lemma_fundamental_div_mod(x, a*b); }
      (a*b)*(x/(a*b)) + x % (a*b);
        { lemma_mul_is_associative_auto(); }
      a*(b*(x/(a*b))) + x % (a*b);
        { lemma_fundamental_div_mod(x%(a*b), a); }
      a*(b*(x/(a*b))) + a*(x%(a*b)/a) + (x%(a*b))%a;
        { lemma_mul_is_distributive_auto(); }
      a*(b*(x/(a*b)) + x%(a*b)/a) + (x%(a*b))%a;
    }
    lemma_mod_properties();
    lemma_mul_is_commutative_auto();
    lemma_fundamental_div_mod_converse(x, a, b*(x/(a*b)) + x%(a*b)/a, (x%(a*b))%a);
  }

  /* ??? */
  lemma lemma_part_bound2(a:int, b:int, c:int)
    requires 0<=a
    requires 0<b
    requires 0<c
    ensures 0<b*c
    ensures (a%b)%(b*c) < b
  {
    lemma_mul_strictly_positive_auto();
    lemma_mod_properties();
    assert a%b < b;
    lemma_mul_increases_auto();
    lemma_mul_is_commutative_auto();
    assert b <= b * c;
    assert 0 <= a%b < b * c;
    lemma_mod_properties();
    lemma_small_mod(a%b,b*c);
    assert (a%b)%(b*c) == a%b;
  }
  
  /* ensures the validity of an expanded for of the modulus operation,
   as expressed in the 'ensures' clause*/
  lemma lemma_mod_breakdown(a:int, b:int, c:int)
    requires 0<=a
    requires 0<b
    requires 0<c
    ensures 0<b*c
    ensures a%(b*c) == b * ((a/b)%c) + a%b
  {
    lemma_mul_strictly_positive_auto();
    lemma_div_pos_is_pos(a,b);
    assert 0<=a/b;

    calc {
      (b*(a/b)) % (b*c) + (a%b) % (b*c);
        <=    { lemma_part_bound1(a, b, c); }
      b*(c-1) + (a%b) % (b*c);
        <    { lemma_part_bound2(a, b, c); }
      b*(c-1) + b;
            { lemma_mul_basics_auto(); }
      b*(c-1) + mul(b,1);
            { lemma_mul_is_distributive_auto(); }
      b*(c-1+1);
      b*c;
    }

    calc {
      a % (b*c);
            { lemma_fundamental_div_mod(a,b); }
    (b*(a/b)+a%b) % (b*c);
            {
              lemma_mod_properties();
              assert 0<=a%b;
              lemma_mul_nonnegative(b,a/b);
              assert (b*(a/b)) % (b*c) + (a%b) % (b*c) < b*c;
              lemma_mod_adds(b*(a/b), a%b, b*c);
            }
    (b*(a/b)) % (b*c) + (a%b) % (b*c);
            {
              lemma_mod_properties();
              lemma_mul_increases(c,b);
              lemma_mul_is_commutative_auto();
              assert a%b<b<=b*c;
              lemma_small_mod(a%b,b*c);
              assert (a%b) % (b*c) == a%b;
            }
    (b*(a/b)) % (b*c) + a%b;
            { lemma_truncate_middle(a/b,b,c); }
    b * ((a/b)%c) + a%b;
    }
  }

}