// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "GeneralInternals.dfy"
include "MulInternals.dfy"
include "../Mul.dfy"
include "ModInternalsNonlinear.dfy"
include "DivInternalsNonlinear.dfy"

module ModInternals {

  import opened GeneralInternals
  import opened Mul
  import opened MulInternalsNonlinear
  import opened MulInternals
  import opened ModInternalsNonlinear
  import opened DivInternalsNonlinear

  /* Performs modulus recursively. */
  function method {:opaque} mod_recursive(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then (d - x) else x
  {
    if x < 0 then
      mod_recursive(d + x, d)
    else if x < d then
      x
    else
      mod_recursive(x - d, d)
  }

  /* performs induction on modulus */ 
  lemma lemma_mod_induction_forall(n: int, f: int -> bool)
    requires n > 0
    requires forall i :: 0 <= i < n ==> f(i)
    requires forall i {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
    requires forall i {:trigger f(i), f(i - n)} :: i < n  && f(i) ==> f(i - n)
    ensures  forall i :: f(i)
  {
    forall i ensures f(i) { lemma_induction_helper(n, f, i); }
  }

  // not used anywhere else in Mod
  /* given an integer x and divisor n, the remainder of x%n is equivalent to the remainder of (x+m)%n
  where m is a multiple of n */
  lemma lemma_mod_induction_forall2(n: int, f:(int, int)->bool)
    requires n > 0
    requires forall i, j :: 0 <= i < n && 0 <= j < n ==> f(i, j)
    requires forall i, j {:trigger f(i, j), f(i + n, j)} :: i >= 0 && f(i, j) ==> f(i + n, j)
    requires forall i, j {:trigger f(i, j), f(i, j + n)} :: j >= 0 && f(i, j) ==> f(i, j + n)
    requires forall i, j {:trigger f(i, j), f(i - n, j)} :: i < n  && f(i, j) ==> f(i - n, j)
    requires forall i, j {:trigger f(i, j), f(i, j - n)} :: j < n  && f(i, j) ==> f(i, j - n)
    ensures  forall i, j :: f(i, j)
  {
    forall x, y
      ensures f(x, y)
    {
      forall i | 0 <= i < n
        ensures f(i, y)
      {
        var fj := j => f(i, j);
        lemma_mod_induction_forall(n, fj);
        assert fj(y);
      }
      var fi := i => f(i, y);
      lemma_mod_induction_forall(n, fi);
      assert fi(x);
    }
  }

  /* proves the basics of the modulus operation */
  lemma lemma_mod_basics(n: int)
    requires n > 0
    ensures  forall x: int {:trigger (x + n) % n} :: (x + n) % n == x % n
    ensures  forall x: int {:trigger (x - n) % n} :: (x - n) % n == x % n
    ensures  forall x: int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures  forall x: int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
    ensures  forall x: int {:trigger x % n} :: 0 <= x < n <==> x % n == x
  {
    forall x: int
      ensures 0 <= x < n <==> x % n == x
    {
      if (0 <= x < n) { lemma_small_mod(x, n); }
      lemma_mod_range(x, n);
    }
    forall x: int
      ensures (x + n) % n == x % n
      ensures (x - n) % n == x % n
      ensures (x + n) / n == x / n + 1
      ensures (x - n) / n == x / n - 1
    {
      lemma_fundamental_div_mod(x, n);
      lemma_fundamental_div_mod(x + n, n);
      lemma_fundamental_div_mod(x - n, n);
      lemma_mod_range(x, n);
      lemma_mod_range(x + n, n);
      lemma_mod_range(x - n, n);
      var zp := (x + n) / n - x / n - 1;
      var zm := (x - n) / n - x / n + 1;
      forall ensures 0 == n * zp + ((x + n) % n) - (x % n) { lemma_mul_auto(); }
      forall ensures 0 == n * zm + ((x - n) % n) - (x % n) { lemma_mul_auto(); }
      if (zp > 0) { lemma_mul_inequality(1, zp, n); }
      if (zp < 0) { lemma_mul_inequality(zp, -1, n); }
      if (zp == 0) { lemma_mul_basics_auto(); }
      if (zm > 0) { lemma_mul_inequality(1, zm, n); }
      if (zm < 0) { lemma_mul_inequality(zm, -1, n); }
    }
  }

  /* proves the quotient remainder theorem */
  lemma lemma_quotient_and_remainder(x: int, q: int, r: int, n: int)
    requires n > 0
    requires 0 <= r < n
    requires x == q * n + r
    ensures  q == x / n
    ensures  r == x % n
    decreases if q > 0 then q else -q
  {
    lemma_mod_basics(n);
    lemma_mul_is_commutative_auto();
    lemma_mul_is_distributive_add_auto();
    lemma_mul_is_distributive_sub_auto();

    if q > 0 {
      assert q * n + r == (q - 1) * n + n + r;
      lemma_quotient_and_remainder(x - n, q - 1, r, n);
    }
    else if q < 0 {
      assert q * n + r == (q + 1) * n - n + r;
      lemma_quotient_and_remainder(x + n, q + 1, r, n);
    }
    else {
      lemma_small_div();
      assert r / n == 0;
    }
  }

  /* automates the modulus operator process */
  predicate mod_auto(n: int)
      requires n > 0;
  {
  && (n % n == (-n) % n == 0)
  && (forall x: int {:trigger (x % n) % n} :: (x % n) % n == x % n)
  && (forall x: int {:trigger x % n} :: 0 <= x < n <==> x % n == x)
  && (forall x: int, y: int {:trigger (x + y) % n} ::
                  (var z := (x % n) + (y % n);
                      (  (0 <= z < n     && (x + y) % n == z)
                      || (n <= z < n + n && (x + y) % n == z - n))))
  && (forall x: int, y: int {:trigger (x - y) % n} ::
                  (var z := (x % n) - (y % n);
                      (   (0 <= z < n && (x - y) % n == z)
                      || (-n <= z < 0 && (x - y) % n == z + n))))
  }

/* ensures that mod_auto is true */
  lemma lemma_mod_auto(n: int)
    requires n > 0
    ensures  mod_auto(n)
  {
    lemma_mod_basics(n);
    lemma_mul_is_commutative_auto();
    lemma_mul_is_distributive_add_auto();
    lemma_mul_is_distributive_sub_auto();

    forall x: int, y: int {:trigger (x + y) % n}
      ensures var z := (x % n) + (y % n);
              || (0 <= z < n && (x + y) % n == z)
              || (n <= z < 2 * n && (x + y) % n == z - n)
    {
      var xq, xr := x / n, x % n;
      lemma_fundamental_div_mod(x, n);
      assert x == xq * n + xr;
      var yq, yr := y / n, y % n;
      lemma_fundamental_div_mod(y, n);
      assert y == yq * n + yr;
      if xr + yr < n {
        lemma_quotient_and_remainder(x + y, xq + yq, xr + yr, n);
      }
      else {
        lemma_quotient_and_remainder(x + y, xq + yq + 1, xr + yr - n, n);
      }
    }

    forall x: int, y: int {:trigger (x - y) % n}
      ensures var z := (x % n) - (y % n);
              || (0 <= z < n && (x - y) % n == z)
              || (-n <= z < 0 && (x - y) % n == z + n)
    {
      var xq, xr := x / n, x % n;
      lemma_fundamental_div_mod(x, n);
      assert x == xq * n + xr;
      var yq, yr := y / n, y % n;
      lemma_fundamental_div_mod(y, n);
      assert y == yq * n + yr;
      if xr - yr >= 0 {
        lemma_quotient_and_remainder(x - y, xq - yq, xr - yr, n);
      }
      else {
        lemma_quotient_and_remainder(x - y, xq - yq - 1, xr - yr + n, n);
      }
    }
  }

  /* performs auto induction for modulus */
  lemma lemma_mod_induction_auto(n: int, x: int, f: int -> bool)
    requires n > 0
    requires mod_auto(n) ==> && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && i < n ==> f(i))
                          && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger is_le(i + 1, n)} :: is_le(i + 1, n) && f(i) ==> f(i - n))
    ensures  mod_auto(n)
    ensures  f(x)
  {
    lemma_mod_auto(n);
    assert forall i :: is_le(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: is_le(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: is_le(i + 1, n) && f(i) ==> f(i - n);
    lemma_mod_induction_forall(n, f);
    assert f(x);
  }

  // not used in other files
  /* performs auto induction on modulus for all i s.t. f(i) exists */
  lemma lemma_mod_induction_auto_forall(n: int, f: int -> bool)
    requires n > 0
    requires mod_auto(n) ==> && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && i < n ==> f(i))
                          && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger is_le(i + 1, n)} :: is_le(i + 1, n) && f(i) ==> f(i - n))
    ensures  mod_auto(n)
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    lemma_mod_auto(n);
    assert forall i :: is_le(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: is_le(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: is_le(i + 1, n) && f(i) ==> f(i - n);
    lemma_mod_induction_forall(n, f);
  }

} 