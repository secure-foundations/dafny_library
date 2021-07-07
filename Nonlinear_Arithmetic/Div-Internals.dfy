include "Mod-Internals.dfy"

module DivInternals {

  import opened ModInternals
  import opened ModNonlinear
  import opened DivNonlinear
  import m = MulInternals

  lemma lemma_div_basics_auto(n:int)
    requires n > 0
    ensures  n / n == -((-n) / n) == 1
    ensures  forall x:int {:trigger x / n} :: 0 <= x < n <==> x / n == 0
    ensures  forall x:int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures  forall x:int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
  {
    lemma_mod_auto(n);
    lemma_mod_basics(n);
    lemma_small_div();
    lemma_div_by_self(n);
    forall x:int | x / n == 0
      ensures 0 <= x < n
    {
      lemma_fundamental_div_mod(x, n);
    }
  }

  predicate DivAuto(n:int)
    requires n > 0 // TODO: allow n < 0
  {
  && mod_auto(n)
  && (n / n == -((-n) / n) == 1)
  && (forall x:int {:trigger x / n} :: 0 <= x < n <==> x / n == 0)
  && (forall x:int, y:int {:trigger (x + y) / n} ::
                  (var z := (x % n) + (y % n);
                      (  (0 <= z < n     && (x + y) / n == x / n + y / n)
                      || (n <= z < n + n && (x + y) / n == x / n + y / n + 1))))
  && (forall x:int, y:int {:trigger (x - y) / n} ::
                  (var z := (x % n) - (y % n);
                      (   (0 <= z < n && (x - y) / n == x / n - y / n)
                      || (-n <= z < 0 && (x - y) / n == x / n - y / n - 1))))
  }

  lemma lemma_div_auto(n:int)
    requires n > 0
    ensures  DivAuto(n)
  {
    lemma_mod_auto(n);
    lemma_div_basics_auto(n);
    assert (0 + n) / n == 1;
    assert (0 - n) / n == -1;
    forall x:int, y:int {:trigger (x + y) / n}
      ensures  var z := (x % n) + (y % n);
                      (|| (0 <= z < n && (x + y) / n == x / n + y / n)
                        || (n <= z < 2 * n && (x + y) / n == x / n + y / n + 1))
    {
      var f := (xx:int, yy:int) =>
                  (var z := (xx % n) + (yy % n);
                      (   (0 <= z < n && (xx + yy) / n == xx / n + yy / n)
                        || (n <= z < 2 * n && (xx + yy) / n == xx / n + yy / n + 1)));
      forall i, j
        ensures j >= 0 && f(i, j) ==> f(i, j + n)
        ensures i < n  && f(i, j) ==> f(i - n, j)
        ensures j < n  && f(i, j) ==> f(i, j - n)
        ensures i >= 0 && f(i, j) ==> f(i + n, j)
      {
        assert ((i + n) + j) / n == ((i + j) + n) / n;
        assert (i + (j + n)) / n == ((i + j) + n) / n;
        assert ((i - n) + j) / n == ((i + j) - n) / n;
        assert (i + (j - n)) / n == ((i + j) - n) / n;
      }
      forall i, j
        ensures 0 <= i < n && 0 <= j < n ==> f(i, j)
      {
        assert ((i + n) + j) / n == ((i + j) + n) / n;
        assert (i + (j + n)) / n == ((i + j) + n) / n;
        assert ((i - n) + j) / n == ((i + j) - n) / n;
        assert (i + (j - n)) / n == ((i + j) - n) / n;
      }
      lemma_mod_induction_forall2(n, f);
      assert f(x, y);
    }
    forall x:int, y:int {:trigger (x - y) / n}
      ensures  var z := (x % n) - (y % n);
                      (|| (0 <= z < n && (x - y) / n == x / n - y / n)
                        || (-n <= z < 0 && (x - y) / n == x / n - y / n - 1))
    {
      var f := (xx:int, yy:int) =>
                  (var z := (xx % n) - (yy % n);
                      (   (0 <= z < n && (xx - yy) / n == xx / n - yy / n)
                      || (-n <= z < 0 && (xx - yy) / n == xx / n - yy / n - 1)));
      forall i, j
        ensures j >= 0 && f(i, j) ==> f(i, j + n)
        ensures i < n  && f(i, j) ==> f(i - n, j)
        ensures j < n  && f(i, j) ==> f(i, j - n)
        ensures i >= 0 && f(i, j) ==> f(i + n, j)
      {
        assert ((i + n) - j) / n == ((i - j) + n) / n;
        assert (i - (j - n)) / n == ((i - j) + n) / n;
        assert ((i - n) - j) / n == ((i - j) - n) / n;
        assert (i - (j + n)) / n == ((i - j) - n) / n;
      }
      forall i, j
        ensures 0 <= i < n && 0 <= j < n ==> f(i, j)
      {
        assert ((i + n) - j) / n == ((i - j) + n) / n;
        assert (i - (j - n)) / n == ((i - j) + n) / n;
        assert ((i - n) - j) / n == ((i - j) - n) / n;
        assert (i - (j + n)) / n == ((i - j) - n) / n;
      }
      lemma_mod_induction_forall2(n, f);
      assert f(x, y);
    }
  }

  lemma lemma_div_auto_induction(n:int, x:int, f:int->bool)
    requires n > 0
    requires DivAuto(n) ==> && (forall i {:trigger m.is_le(0, i)} :: m.is_le(0, i) && i < n ==> f(i))
                          && (forall i {:trigger m.is_le(0, i)} :: m.is_le(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger m.is_le(i + 1, n)} :: m.is_le(i + 1, n) && f(i) ==> f(i - n))
    ensures  DivAuto(n)
    ensures  f(x)
  {
    lemma_div_auto(n);
    assert forall i :: m.is_le(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: m.is_le(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: m.is_le(i + 1, n) && f(i) ==> f(i - n);
    lemma_mod_induction_forall(n, f);
    assert f(x);
  }

  lemma lemma_div_auto_induction_forall(n:int, f:int->bool)
    requires n > 0
    requires DivAuto(n) ==> && (forall i {:trigger m.is_le(0, i)} :: m.is_le(0, i) && i < n ==> f(i))
                          && (forall i {:trigger m.is_le(0, i)} :: m.is_le(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger m.is_le(i + 1, n)} :: m.is_le(i + 1, n) && f(i) ==> f(i - n))
    ensures  DivAuto(n)
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    lemma_div_auto(n);
    assert forall i :: m.is_le(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: m.is_le(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: m.is_le(i + 1, n) && f(i) ==> f(i - n);
    lemma_mod_induction_forall(n, f);
  }

} 