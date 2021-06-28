include "mod_auto_proofs_i.dfy"

module Math__mod_auto_i {

  import opened Math__mod_auto_proofs_i
  import opened Math__div_nonlinear_i
  import opened Math__mul_nonlinear_i
  import opened Math__mul_i

  predicate eq_mod(x:int, y:int, n:int)
    requires n > 0
  {
    (x - y) % n == 0 // same as x % n == y % n, but easier to do induction on x - y than x and y separately
  }

  predicate mod_auto(n:int)
      requires n > 0;
  {
  && (n % n == (-n) % n == 0)
  && (forall x:int {:trigger (x % n) % n} :: (x % n) % n == x % n)
  && (forall x:int {:trigger x % n} :: 0 <= x < n <==> x % n == x)
  && (forall x:int, y:int {:trigger (x + y) % n} ::
                  (var z := (x % n) + (y % n);
                      (  (0 <= z < n     && (x + y) % n == z)
                      || (n <= z < n + n && (x + y) % n == z - n))))
  && (forall x:int, y:int {:trigger (x - y) % n} ::
                  (var z := (x % n) - (y % n);
                      (   (0 <= z < n && (x - y) % n == z)
                      || (-n <= z < 0 && (x - y) % n == z + n))))
  }

  lemma lemma_quotient_and_remainder_unique(x:int, q:int, r:int, n:int)
    requires n > 0
    requires 0 <= r < n
    requires x == q * n + r
    ensures  q == x / n
    ensures  r == x % n
    decreases if q > 0 then q else -q
  {
    lemma_mod_auto_basics(n);
    lemma_mul_is_commutative_forall();
    lemma_mul_is_distributive_add_forall();
    lemma_mul_is_distributive_sub_forall();

    if q > 0 {
      assert q * n + r == (q - 1) * n + n + r;
      lemma_quotient_and_remainder_unique(x - n, q - 1, r, n);
    }
    else if q < 0 {
      assert q * n + r == (q + 1) * n - n + r;
      lemma_quotient_and_remainder_unique(x + n, q + 1, r, n);
    }
    else {
      lemma_small_div();
      assert r / n == 0;
    }
  }

  lemma lemma_mod_auto(n:int)
    requires n > 0
    ensures  mod_auto(n)
  {
    lemma_mod_auto_basics(n);
    lemma_mul_is_commutative_forall();
    lemma_mul_is_distributive_add_forall();
    lemma_mul_is_distributive_sub_forall();

    forall x:int, y:int {:trigger (x + y) % n}
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
        lemma_quotient_and_remainder_unique(x + y, xq + yq, xr + yr, n);
      }
      else {
        lemma_quotient_and_remainder_unique(x + y, xq + yq + 1, xr + yr - n, n);
      }
    }

    forall x:int, y:int {:trigger (x - y) % n}
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
        lemma_quotient_and_remainder_unique(x - y, xq - yq, xr - yr, n);
      }
      else {
        lemma_quotient_and_remainder_unique(x - y, xq - yq - 1, xr - yr + n, n);
      }
    }
  }

  predicate t_mod_auto_le(x:int, y:int) { x <= y }

  lemma lemma_mod_auto_induction(n:int, x:int, f:int->bool)
    requires n > 0
    requires mod_auto(n) ==> && (forall i {:trigger t_mod_auto_le(0, i)} :: t_mod_auto_le(0, i) && i < n ==> f(i))
                          && (forall i {:trigger t_mod_auto_le(0, i)} :: t_mod_auto_le(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger t_mod_auto_le(i + 1, n)} :: t_mod_auto_le(i + 1, n) && f(i) ==> f(i - n))
    ensures  mod_auto(n)
    ensures  f(x)
  {
    lemma_mod_auto(n);
    assert forall i :: t_mod_auto_le(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: t_mod_auto_le(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: t_mod_auto_le(i + 1, n) && f(i) ==> f(i - n);
    lemma_mod_induction_forall(n, f);
    assert f(x);
  }

  lemma lemma_mod_auto_induction_forall(n:int, f:int->bool)
    requires n > 0
    requires mod_auto(n) ==> && (forall i {:trigger t_mod_auto_le(0, i)} :: t_mod_auto_le(0, i) && i < n ==> f(i))
                          && (forall i {:trigger t_mod_auto_le(0, i)} :: t_mod_auto_le(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger t_mod_auto_le(i + 1, n)} :: t_mod_auto_le(i + 1, n) && f(i) ==> f(i - n))
    ensures  mod_auto(n)
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    lemma_mod_auto(n);
    assert forall i :: t_mod_auto_le(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: t_mod_auto_le(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: t_mod_auto_le(i + 1, n) && f(i) ==> f(i - n);
    lemma_mod_induction_forall(n, f);
  }

} 