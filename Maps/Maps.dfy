module Maps {
  predicate is_equal<A(!new), B>(x: map<A, B>, y: map<A, B>)
    ensures is_equal(x, y) ==> x == y
  {
    (forall a :: a in x <==> a in y) && (forall a :: a in x ==> x[a] == y[a])
  }

  function method domain<U(!new), V>(m: map<U, V>): set<U>
    ensures forall i :: i in domain(m) <==> i in m
  {
    set s | s in m
  }

  function method range<U, V(!new)>(m: map<U, V>) : set<V>
    ensures forall i :: i in range(m) <==> exists j :: j in m && m[j] == i
  {
    set s | s in m :: m[s]
  }

  function method union<U(!new), V>(m: map<U, V>, m': map<U, V>): map<U, V>
    requires m.Keys !! m'.Keys
    ensures forall i :: i in union(m, m') <==> i in m || i in m'
    ensures forall i :: i in m ==> union(m, m')[i] == m[i]
    ensures forall i :: i in m' ==> union(m, m')[i] == m'[i]
  {
    map i | i in (domain(m) + domain(m')) :: if i in m then m[i] else m'[i]
  }

  function method remove<U(!new), V(!new)>(m: map<U, V>, u: U) : map<U, V>
    requires u in m
    decreases |m|
    ensures |remove(m, u)| == |m| - 1
    ensures !(u in remove(m, u))
    ensures forall u' :: u' in remove(m, u) <==> u' in m && u' != u
  {
    var m' := map u' | u' in m && u' != u :: m[u'];
    lemma_map_remove_one(m, m', u);
    m'
  }

  lemma lemma_size_is_domain_size<S(!new), T(!new)>(dom: set<S>,
                                                    m: map<S, T>)
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

  lemma lemma_remove_decreases_size<S(!new), T(!new)>(before: map<S, T>,
                                                      after: map<S, T>,
                                                      item_removed: S)
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

  lemma lemma_map_remove_one<S(!new), T(!new)>(before: map<S, T>,
                                               after: map<S, T>,
                                               item_removed: S)
    requires item_removed in before
    requires after == map s | s in before && s != item_removed :: before[s]
    ensures |after| + 1 == |before|
  {
    var domain_before := domain(before);
    var domain_after := domain(after);

    lemma_size_is_domain_size(domain_before, before);
    lemma_size_is_domain_size(domain_after, after);

    assert domain_after + {item_removed} == domain_before;
  }  
} 