include "../Mathematics.dfy"

module Set {
  import Math = Mathematics

  lemma lemma_proper_subset_cardinality<T>(x: set<T>, y: set<T>)
    requires x < y
    ensures |x| < |y|
    decreases x, y
  {
    if x != {} {
      var e :| e in x;
      lemma_proper_subset_cardinality(x - {e}, y - {e});
    }
  }

  lemma lemma_subset_cardinality<T>(x: set<T>, y: set<T>)
    ensures x < y ==> |x| < |y|
    ensures x == y ==> |x| == |y|
  {
    if x < y {
      lemma_proper_subset_cardinality(x, y);
    } else if x == y {
    }
  }

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

  lemma lemma_singleton_set_cardinality<T>(x: set<T>, e: T)
    requires x == {e}
    ensures |x| == 1
  {
  }

  lemma lemma_singleton_set_equality<T>(foo: set<T>, x: T, y: T)
    requires |foo| == 1
    requires x in foo
    requires y in foo
    ensures x == y
  {
    if x != y {
      assert {x} < foo;
      lemma_subset_cardinality({x}, foo);
      assert |{x}| < |foo|;
      assert |foo| > 1;
      assert false;
    }
  }

  lemma lemma_map_set_to_set_cardinality<X, Y>(xs: set<X>, ys: set<Y>, f: X-->Y)
    requires forall x :: f.requires(x)
    requires Math.injective(f)
    requires forall x :: x in xs <==> f(x) in ys
    requires forall y :: y in ys ==> exists x :: x in xs && y == f(x)
    ensures |xs| == |ys|
    decreases xs, ys
  {
    if xs != {}
    {
      var x :| x in xs;
      var xs' := xs - {x};
      var ys' := ys - {f(x)};
      lemma_map_set_to_set_cardinality(xs', ys', f);
    }
  }

  function method {:opaque} map_set_to_set<X(!new), Y>(xs: set<X>, f: X-->Y): set<Y>
    reads f.reads
    requires forall x :: f.requires(x)
    requires Math.injective(f)
    ensures forall x :: x in xs <==> f(x) in map_set_to_set(xs, f)
    ensures |xs| == |map_set_to_set(xs, f)|
  {
    var ys := set x | x in xs :: f(x); 
    lemma_map_set_to_set_cardinality(xs, ys, f);
    ys
  }

  function method {:opaque} map_seq_to_set<X(!new), Y>(xs: seq<X>, f: X-->Y): set<Y>
    reads f.reads
    requires forall x :: f.requires(x)
    requires Math.injective(f)
    ensures forall x :: x in xs <==> f(x) in map_seq_to_set(xs, f)
    decreases xs
  {
    if |xs| == 0 then {} else map_seq_to_set(xs[1..], f) + {f(xs[0])}
  }

  lemma lemma_filter_cardinality<X>(xs: set<X>, ys: set<X>, f: X~>bool)
    requires forall x :: x in xs ==> f.requires(x)
    requires forall y :: y in ys ==> y in xs && f(y)
    ensures |ys| <= |xs|
    decreases xs, ys
  {
    if ys != {}
    {
      var y :| y in ys;
      var xs' := xs - {y};
      var ys' := ys - {y};
      lemma_filter_cardinality(xs', ys', f);
    }
  }

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

  lemma lemma_union_cardinality<X>(xs: set<X>, ys: set<X>, us: set<X>)
    requires us == xs + ys
    ensures |us| >= |xs|
    decreases ys
  {
    if ys == {} {
    } else {
      var y :| y in ys;
      if y in xs {
        var xr := xs - {y};
        var yr := ys - {y};
        var ur := us - {y};
        lemma_union_cardinality(xr, yr, ur);
      } else {
        var ur := us - {y};
        var yr := ys - {y};
        lemma_union_cardinality(xs, yr, ur);
      }
    }
  }

  function method set_of_numbers_in_right_exclusive_range(a: int, b: int): set<int>
    requires a <= b
    ensures forall e :: a <= e < b <==> e
            in set_of_numbers_in_right_exclusive_range(a, b)
    ensures |set_of_numbers_in_right_exclusive_range(a, b)| == b - a
    decreases b - a
  {
    if a == b then {}
    else {a} + set_of_numbers_in_right_exclusive_range(a + 1, b)
  }

  lemma lemma_bounded_set_cardinality(s: set<int>, a: int, b: int)
    requires forall e :: e in s ==> a <= e < b
    requires a <= b
    ensures |s| <= b - a
  {
    var range := set_of_numbers_in_right_exclusive_range(a, b);
    forall i | i in s
      ensures i in range;
    {
    }
    assert s <= range;
    lemma_subset_cardinality(s, range);
  }
}
