// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Options.dfy"

module Maps {
  import opened Options

  function method {:opaque} get_option<X, Y>(m: map<X, Y>, x: X): Option<Y> {
	  if x in m then Some(m[x]) else None
	}

  function to_imap<X, Y>(m: map<X, Y>): imap<X, Y> {
	  imap x | x in m :: m[x]
	}

  /**
   * The size of a map is equal to the size of its domain.
   */
  lemma lemma_size_is_domain_size<X(!new), Y(!new)>(dom: set<X>,
                                                    m: map<X, Y>)
    requires dom == m.Keys
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

  /**
   * Remove all map items with keys that are elements of a set.
   */
  function method {:opaque} remove_set<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures forall x :: x in m && x !in xs ==> x in m'
    ensures forall x :: x in m' ==> x in m && x !in xs && m'[x] == m[x]
    ensures m'.Keys == m.Keys - xs
  {
    map x | x in m && x !in xs :: m[x]
  }

  /**
   * Remove a map item.
   */
  function method {:opaque} remove<X(!new), Y(!new)>(m: map<X, Y>, x: X): (m': map<X, Y>)
    requires x in m
    ensures forall i :: i in m && i != x ==> i in m'
    ensures forall i :: i in m' <==> i in m && i != x && m'[i] == m[i]
    ensures |m'| == |m| - 1
  {
    var m' := map x' | x' in m && x' != x :: m[x'];
    lemma_remove_one(m, m', x);
    m'
  }

  /**
   * Removing a map item decreases map size by 1.
   */
  lemma lemma_remove_one<X(!new), Y(!new)>(before: map<X, Y>,
                                           after: map<X, Y>,
                                           item_removed: X)
    requires item_removed in before
    requires after == map i | i in before && i != item_removed :: before[i]
    ensures |after| + 1 == |before|
  {
    var domain_before := before.Keys;
    var domain_after := after.Keys;

    lemma_size_is_domain_size(domain_before, before);
    lemma_size_is_domain_size(domain_after, after);

    assert domain_after + {item_removed} == domain_before;
  }

  /**
   * Keep all map items with keys that are elements of a set.
   */
  function method {:opaque} restrict<X, Y>(m: map<X, Y>, xs: set<X>): map<X, Y> {
    map x | x in xs && x in m :: m[x]
  }

  /**
   * Returns true if a map contains the key-value pair (x, y).
   */
  predicate {:opaque} contains<X(!new), Y>(m: map<X, Y>, x: X, y: Y) {
    x in m && m[x] == y
  }

  /**
   * Returns true if two maps are equal for intersecting keys.
   */
  predicate {:opaque} equals_on_key<X(!new), Y>(m: map<X, Y>, m': map<X, Y>, x: X) {
    (x !in m && x !in m') || (x in m && x in m' && m[x] == m'[x])
  }

  /**
   * Returns true if two maps are equal.
   */
  predicate {:opaque} equals<X(!new), Y>(m: map<X, Y>, m': map<X, Y>) {
    (forall x :: x in m <==> x in m') && (forall x :: x in m ==> m[x] == m'[x])
  }

  /**
   * Returns true if m.Keys is a subset of m'.Keys.
   */
  predicate {:opaque} is_subset<X(!new), Y>(m: map<X, Y>, m': map<X, Y>) {
    m.Keys <= m'.Keys && (forall x :: x in m ==> equals_on_key(m, m', x))
  }

  /**
   * Finds the union of two maps. Does not require disjoint domains; on the 
   * intersection, values from the first map are chosen.
   */
  function method {:opaque} union_prefer_first<X, Y>(m: map<X, Y>, m': map<X, Y>): (m'': map<X, Y>)
    ensures m''.Keys == m.Keys + m'.Keys
    ensures forall k :: k in m ==> m''[k] == m[k]
    ensures forall k :: k in m'.Keys - m.Keys ==> m''[k] == m'[k]
    ensures forall k :: k in m' && k !in m ==> m''[k] == m'[k]
  {
    map x | x in m.Keys + m'.Keys :: if x in m then m[x] else m'[x]
  }

  /**
   * Finds the union of two maps. Does not require disjoint domains; on the 
   * intersection, values from the second map are chosen.
   */
  function method {:opaque} union_prefer_second<X, Y>(m: map<X, Y>, m': map<X, Y>): (m'': map<X, Y>)
    ensures m''.Keys == m.Keys + m'.Keys
    ensures forall k :: k in m' ==> m''[k] == m'[k]
    ensures forall k :: k in m.Keys - m'.Keys ==> m''[k] == m[k]
    ensures forall k :: k in m && k !in m' ==> m''[k] == m[k]
  {
    map x | x in m.Keys + m'.Keys :: if x in m' then m'[x] else m[x]
  }

  /**
   * Finds the union of two maps. Does not require disjoint domains; no
   * promises on which value is chosen on the intersection.
   */
  function method {:opaque} union<X, Y>(m: map<X, Y>, m': map<X, Y>): (m'': map<X, Y>)
		ensures m''.Keys == m.Keys + m'.Keys
		ensures forall k :: k in m.Keys - m'.Keys ==> m[k] == m''[k]
		ensures forall k :: k in m'.Keys - m.Keys ==> m'[k] == m''[k]
		ensures forall k :: k in m.Keys * m'.Keys ==>	m'[k] == m''[k] ||
                                                  m[k] == m''[k]
	{
		union_prefer_first(m, m')
	}

  /**
   * Finds the union of two maps. Requires disjoint domains.
   */
  function method {:opaque} disjoint_union<X, Y>(m: map<X, Y>, m': map<X, Y>): (m'': map<X, Y>)
		requires m.Keys !! m'.Keys
		ensures m''.Keys == m.Keys + m'.Keys
		ensures forall k :: k in m ==> m[k] == m''[k]
		ensures forall k :: k in m' ==> m'[k] == m''[k]
	{
		map x | x in m.Keys + m'.Keys :: if x in m then m[x] else m'[x]
	}

  /**
   * The size of the disjoint union is equal to the sum of the sizes of
   * individual maps.
   */
  lemma lemma_disjoint_union_size<X, Y>(m: map<X, Y>, m': map<X, Y>)
    requires m.Keys !! m'.Keys
    ensures |disjoint_union(m, m')| == |m| + |m'|
  {
    var u := disjoint_union(m, m');
    assert |u.Keys| == |m.Keys| + |m'.Keys|;
  }

}
