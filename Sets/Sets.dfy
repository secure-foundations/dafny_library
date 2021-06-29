include "../Mathematics.dfy"

module Sets {

  import Math = Mathematics

  /**
   * If all elements in set x are in set y, x is a subset of y.
   */
  lemma lemma_subset<T>(x: set<T>, y: set<T>)
    requires forall e | e in x :: e in y
    ensures x <= y
  {
  }

  /**
   * If x is a subset of y, then the cardinality of x is less than or equal to
   * the cardinality of y.
   */
  lemma lemma_subset_cardinality<T>(x: set<T>, y: set<T>)
    ensures x < y ==> |x| < |y|
    ensures x <= y ==> |x| <= |y|
  {
    if x != {} {
      var e :| e in x;
      lemma_subset_cardinality(x - {e}, y - {e});
    }
  }

  /**
   * If x is a subset of y and the cardinality of x is equal to the cardinality
   * of y, x is equal to y.
   */
  lemma lemma_subset_equality<T>(x: set<T>, y: set<T>)
    requires x <= y
    requires |x| == |y|
    ensures x == y
    decreases x, y
  {
    if x == {} {
    } else {
      var e :| e in x;
      lemma_subset_equality(x - {e}, y - {e});
    }
  }

  /**
   * A singleton set has a cardinality of 1.
   */
  lemma lemma_singleton_cardinality<T>(x: set<T>, e: T)
    requires x == {e}
    ensures |x| == 1
  {
  }

  /**
   * Elements in a singleton set are equal to each other.
   */
  lemma lemma_singleton_equality<T>(x: set<T>, a: T, b: T)
    requires |x| == 1
    requires a in x
    requires b in x
    ensures a == b
  {
    if a != b {
      assert {a} < x;
      lemma_subset_cardinality({a}, x);
      assert |{a}| < |x|;
      assert |x| > 1;
      assert false;
    }
  }

  /**
   * If an injective function is applied to each element of a set to construct
   * another set, the two sets have the same cardinality. 
   */
  lemma lemma_apply_cardinality<X(!new), Y>(xs: set<X>, ys: set<Y>, f: X-->Y)
    requires forall x :: f.requires(x)
    requires Math.injective(f)
    requires forall x :: x in xs <==> f(x) in ys
    requires forall y :: y in ys ==> exists x :: x in xs && y == f(x)
    ensures |xs| == |ys|
  {
    if xs != {} {
      var x :| x in xs;
      var xs' := xs - {x};
      var ys' := ys - {f(x)};
      lemma_apply_cardinality(xs', ys', f);
    }
  }

  /**
   * Apply an injective function to each element of a set.
   */
  function method {:opaque} apply<X(!new), Y>(xs: set<X>, f: X-->Y): set<Y>
    reads f.reads
    requires forall x :: f.requires(x)
    requires Math.injective(f)
    ensures forall x :: x in xs <==> f(x) in apply(xs, f)
    ensures |xs| == |apply(xs, f)|
  {
    var ys := set x | x in xs :: f(x);
    lemma_apply_cardinality(xs, ys, f);
    ys
  }

  /**
   * If a set ys is constructed using elements of another set xs for which a
   * function returns true, the cardinality of ys is less than or equal to the
   * cardinality of xs.
   */
  lemma lemma_filter_cardinality<X>(xs: set<X>, ys: set<X>, f: X~>bool)
    requires forall x :: x in xs ==> f.requires(x)
    requires forall y :: y in ys ==> y in xs && f(y)
    ensures |ys| <= |xs|
    decreases xs, ys
  {
    if ys != {} {
      var y :| y in ys;
      var xs' := xs - {y};
      var ys' := ys - {y};
      lemma_filter_cardinality(xs', ys', f);
    }
  }

  /**
   * Construct a set using elements of another set for which a function returns
   * true.
   */
  function method {:opaque} filter<X(!new)>(xs: set<X>, f: X~>bool): set<X>
    reads f.reads
    requires forall x :: x in xs ==> f.requires(x)
    ensures forall y :: y in filter(xs, f) <==> y in xs && f(y)
    ensures |filter(xs, f)| <= |xs|
  {
    var ys := set x | x in xs && f(x);
    lemma_filter_cardinality(xs, ys, f);
    ys
  }

  /**
   * The cardinality of a union of two sets is greater than or equal to the
   * cardinality of either individual set.
   */
  lemma lemma_union_cardinality<X>(xs: set<X>, ys: set<X>)
    ensures |xs + ys| >= |xs|
    ensures |xs + ys| >= |ys|
  {
    if ys == {} {
    } else {
      var y :| y in ys;
      if y in xs {
        var xr := xs - {y};
        var yr := ys - {y};
        assert xr + yr == xs + ys - {y};
        lemma_union_cardinality(xr, yr);
      } else {
        var yr := ys - {y};
        assert xs + yr == xs + ys - {y};
        lemma_union_cardinality(xs, yr);
      }
    }
  }

  /**
   * Construct a set with all integers in the range [a, b).
   */
  function method {:opaque} set_range(a: int, b: int): set<int>
    requires a <= b
    ensures forall i :: a <= i < b <==> i
            in set_range(a, b)
    ensures |set_range(a, b)| == b - a
    decreases b - a
  {
    if a == b then {} else {a} + set_range(a + 1, b)
  }

  /**
   * Construct a set with all integers in the range [0, n).
   */
  function method {:opaque} set_range_zero_bound(n: int): set<int>
    requires n >= 0
    ensures forall i :: 0 <= i < n <==> i in set_range_zero_bound(n)
    ensures |set_range_zero_bound(n)| == n
  {
    set_range(0, n)
  }

  /**
   * If a set solely contains integers in the range [a, b), then its cardinality
   * is bounded by b - a.
   */
  lemma lemma_bounded_set_cardinality(x: set<int>, a: int, b: int)
    requires forall i :: i in x ==> a <= i < b
    requires a <= b
    ensures |x| <= b - a
  {
    var range := set_range(a, b);
    forall e | e in x
      ensures e in range;
    {
    }
    assert x <= range;
    lemma_subset_cardinality(x, range);
  }

}
