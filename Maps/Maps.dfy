module Maps {

  predicate {:opaque} is_equal<X(!new), Y>(m: map<X, Y>, m': map<X, Y>) {
    (forall x :: x in m <==> x in m') && (forall x :: x in m ==> m[x] == m'[x])
  }

  function method {:opaque} domain<X(!new), Y>(m: map<X, Y>): set<X>
    ensures forall x :: x in domain(m) <==> x in m
  {
    set x | x in m
  }

  function method {:opaque} range<X, Y(!new)>(m: map<X, Y>) : set<Y>
    ensures forall y :: y in range(m) <==> exists x :: x in m && m[x] == y
  {
    set x | x in m :: m[x]
  }

  function method {:opaque} union<X(!new), Y>(m: map<X, Y>, m': map<X, Y>): map<X, Y>
    requires m.Keys !! m'.Keys
    ensures forall x :: x in union(m, m') <==> x in m || x in m'
    ensures forall x :: x in m ==> union(m, m')[x] == m[x]
    ensures forall x :: x in m' ==> union(m, m')[x] == m'[x]
  {
    map x | x in (domain(m) + domain(m')) :: if x in m then m[x] else m'[x]
  }

  function method {:opaque} remove<X(!new), Y(!new)>(m: map<X, Y>, x: X) : map<X, Y>
    requires x in m
    decreases |m|
    ensures |remove(m, x)| == |m| - 1
    ensures !(x in remove(m, x))
    ensures forall i :: i in remove(m, x) <==> i in m && i != x
  {
    var m' := map x' | x' in m && x' != x :: m[x'];
    lemma_remove_one(m, m', x);
    m'
  }

  lemma lemma_size_is_domain_size<X(!new), Y(!new)>(dom: set<X>,
                                                    m: map<X, Y>)
    requires dom == domain(m)
    ensures |m| == |dom|
  {
    if |m| == 0 {
    } else {
      var x :| x in m;
      var m' := map y | y in m && y != x :: m[y];
      var dom' := dom - {x};
      lemma_size_is_domain_size(dom', m');
      assert m == m'[x := m[x]];
    }
  }

  lemma lemma_remove_decreases_size<X(!new), Y(!new)>(before: map<X, Y>,
                                                      after: map<X, Y>,
                                                      item_removed: X)
    requires item_removed in before
    requires after == map s | s in before && s != item_removed :: before[s]
    ensures |after| < |before|
  {
    var domain_before := set s | s in before;
    var domain_after := set s | s in after;

    lemma_size_is_domain_size(domain_before, before);
    lemma_size_is_domain_size(domain_after, after);

    if |after| == |before| {
      assert |domain_before - domain_after| > 0;
    } else if |after| > |before| {
      assert |domain_after - domain_before| == 0;
    }
  }

  lemma lemma_remove_one<X(!new), Y(!new)>(before: map<X, Y>,
                                           after: map<X, Y>,
                                           item_removed: X)
    requires item_removed in before
    requires after == map i | i in before && i != item_removed :: before[i]
    ensures |after| + 1 == |before|
  {
    var domain_before := domain(before);
    var domain_after := domain(after);

    lemma_size_is_domain_size(domain_before, before);
    lemma_size_is_domain_size(domain_after, after);

    assert domain_after + {item_removed} == domain_before;
  }
 
}
