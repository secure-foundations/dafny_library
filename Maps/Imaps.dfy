// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Options.dfy"

module Imaps {
  import opened Options

  function method {:opaque} get_option<X, Y>(m: imap<X, Y>, x: X): Option<Y> {
	  if x in m then Some(m[x]) else None
	}

  /**
   * Remove all imap items with keys that are elements of an iset.
   */
  function {:opaque} remove_iset<X, Y>(m: imap<X, Y>, xs: iset<X>): (m': imap<X, Y>)
    ensures forall x :: x in m && x !in xs ==> x in m'
    ensures forall x :: x in m' ==> x in m && x !in xs && m'[x] == m[x]
    ensures m'.Keys == m.Keys - xs
  {
    imap x | x in m && x !in xs :: m[x]
  }

  /**
   * Remove an imap item.
   */
  function {:opaque} remove<X, Y>(m:imap<X, Y>, x: X): (m': imap<X, Y>)
    ensures m'.Keys == m.Keys - iset{x}
    ensures forall x' :: x' in m' ==> m'[x'] == m[x']
  {
    imap i | i in m && i != x :: m[i]
  }

  /**
   * Keep all imap items with keys that are elements of a set.
   */
  function {:opaque} restrict<X, Y>(m: imap<X, Y>, xs: iset<X>): imap<X, Y> {
    imap x | x in xs && x in m :: m[x]
  }

  /**
   * Returns true if an imap contains the key-value pair (x, y).
   */
  predicate {:opaque} contains<X(!new), Y>(m: imap<X, Y>, x: X, y: Y) {
    x in m && m[x] == y
  }

  /**
   * Returns true if two imaps are equal for intersecting keys.
   */
  predicate {:opaque} equals_on_key<X(!new), Y>(m: imap<X, Y>, m': imap<X, Y>, x: X) {
    (x !in m && x !in m') || (x in m && x in m' && m[x] == m'[x])
  }

  /**
   * Returns true if two imaps are equal.
   */
  predicate {:opaque} equals<X(!new), Y>(m: imap<X, Y>, m': imap<X, Y>) {
    (forall x :: x in m <==> x in m') && (forall x :: x in m ==> m[x] == m'[x])
  }

  /**
   * Returns true if m.Keys is a subset of m'.Keys.
   */
  predicate {:opaque} subset<X(!new), Y>(m: imap<X, Y>, m': imap<X, Y>) {
    m.Keys <= m'.Keys && (forall x :: x in m ==> equals_on_key(m, m', x))
  }

  /**
   * Finds the union of two imaps. Does not require disjoint domains; on the 
   * intersection, values from the first imap are chosen.
   */
  function {:opaque} union_prefer_first<X, Y>(m: imap<X, Y>, m': imap<X, Y>): (m'': imap<X, Y>)
    ensures m''.Keys == m.Keys + m'.Keys
    ensures forall k :: k in m ==> m''[k] == m[k]
    ensures forall k :: k in m'.Keys - m.Keys ==> m''[k] == m'[k]
    ensures forall k :: k in m' && k !in m ==> m''[k] == m'[k]
  {
    imap x | x in m.Keys + m'.Keys :: if x in m then m[x] else m'[x]
  }

  /**
   * Finds the union of two imaps. Does not require disjoint domains; on the 
   * intersection, values from the second imap are chosen.
   */
  function {:opaque} union_prefer_second<X, Y>(m: imap<X, Y>, m': imap<X, Y>): (m'': imap<X, Y>)
    ensures m''.Keys == m.Keys + m'.Keys
    ensures forall k :: k in m' ==> m''[k] == m'[k]
    ensures forall k :: k in m.Keys - m'.Keys ==> m''[k] == m[k]
    ensures forall k :: k in m && k !in m' ==> m''[k] == m[k]
  {
    imap x | x in m.Keys + m'.Keys :: if x in m' then m'[x] else m[x]
  }

  /**
   * Finds the union of two imaps. Does not require disjoint domains; no
   * promises on which value is chosen on the intersection.
   */
  function {:opaque} union<X, Y>(m: imap<X, Y>, m': imap<X, Y>): (m'': imap<X, Y>)
		ensures m''.Keys == m.Keys + m'.Keys
		ensures forall k :: k in m.Keys - m'.Keys ==> m[k] == m''[k]
		ensures forall k :: k in m'.Keys - m.Keys ==> m'[k] == m''[k]
		ensures forall k :: k in m.Keys * m'.Keys ==>	m'[k] == m''[k] ||
                                                  m[k] == m''[k]
	{
		union_prefer_first(m, m')
	}

  /**
   * m'' is the union of imaps m and m'. Requires disjoint domains.
   */
  lemma lemma_is_union<X, Y>(m: imap<X, Y>, m': imap<X, Y>, m'': imap<X, Y>)
    requires m.Keys !! m'.Keys
    requires forall x :: x in m ==> x in m'' && m''[x] == m[x]
    requires forall x :: x in m' ==> x in m'' && m''[x] == m'[x]
    requires forall x :: x in m'' ==> x in m || x in m'
    ensures m'' == union(m, m')
	{
	}

  /**
   * Finds the union of two imaps. Requires disjoint domains.
   */
  function {:opaque} disjoint_union<X, Y>(m: imap<X, Y>, m': imap<X, Y>): (m'': imap<X, Y>)
		requires m.Keys !! m'.Keys
		ensures m''.Keys == m.Keys + m'.Keys
		ensures forall k :: k in m ==> m[k] == m''[k]
		ensures forall k :: k in m' ==> m'[k] == m''[k]
	{
		imap x | x in m.Keys + m'.Keys :: if x in m then m[x] else m'[x]
	}

  /**
   * Returns true if an imap is injective.
   */
  predicate {:opaque} injective<X(!new), Y>(m: imap<X, Y>) {
    forall x, x' | x != x' && x in m && x' in m :: m[x] != m[x']
  }

  /**
   * Swaps imap keys and values. Values are not required to be unique; no
   * promises on which key is chosen on the intersection.
   */
  function {:opaque} invert<X, Y(!new)>(m: imap<X, Y>): imap<Y, X> {
    imap y | y in m.Values :: var x :| x in m && m[x] == y; x
  }

  /**
   * Inverted imaps are injective.
   */
  lemma lemma_invert_is_injective<X, Y>(m: imap<X, Y>)
    ensures injective(invert(m))
  {
    reveal_injective();
    reveal_invert();
  }

  /**
   * Returns true if an imap contains all valid keys.
   */
  predicate {:opaque} total<X(!new), Y>(m: imap<X, Y>) {
    forall i :: i in m
  }

  /**
   * Returns true if an imap is monotonic.
   */
  predicate {:opaque} monotonic(m: imap<int, int>) {
    forall x, x' :: x in m && x' in m && x <= x' ==> m[x] <= m[x']
  }

  /**
   * Returns true if an imap is monotonic. Only considers keys greater than or
   * equal to start.
   */
  predicate {:opaque} monotonic_from(start: int, m: imap<int, int>) {
    forall x, x' :: x in m && x' in m && start <= x <= x' ==> m[x] <= m[x']
  }

  /**
   * Returns true if the composite mapping m' ∘ m is monotonic.
   */
  predicate {:opaque} monotonic_double_mapping<X>(m: imap<int, X>, m': imap<X, int>)
    requires total(m)
    requires total(m')
  {
    reveal_total();
    forall x, x' :: x <= x' ==> m'[m[x]] <= m'[m[x']]
  }

  /**
   * Suppose an imap contains (start, true), and for all indices i in the range
   * [start, end), if m[i] is true then m[i + 1] is true. Then the imap contains
   * (end, true).
   */
  lemma lemma_induction_range(start: int, end: int, m: imap<int, bool>)
    requires start <= end
    requires forall i :: start <= i <= end ==> i in m
    requires forall i :: start <= i < end && m[i] ==> m[i + 1]
    requires m[start]
    ensures m[end]
    decreases end - start
  {
    if start < end {
      lemma_induction_range(start + 1, end, m);
    }
  }

}
