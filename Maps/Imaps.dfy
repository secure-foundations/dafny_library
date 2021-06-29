// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Options.dfy"

module Imaps {
  import opened Options

  function method {:opaque} get<X, Y>(m: imap<X, Y>, x: X): Option<Y> {
	  if x in m then Some(m[x]) else None
	}

  function {:opaque} remove<X, Y>(m:imap<X, Y>, x: X): (m': imap<X, Y>)
    ensures m'.Keys == m.Keys - iset{x}
    ensures forall x' :: x' in m' ==> m'[x'] == m[x']
  {
    imap i | i in m && i != x :: m[i]
  }

  function {:opaque} remove_iset<X, Y>(m: imap<X, Y>, xs: iset<X>): (m': imap<X, Y>)
    ensures m'.Keys == m.Keys - xs
    ensures forall x :: x in m' ==> m'[x] == m[x]
  {
    imap x | x in m && x !in xs :: m[x]
  }

  predicate {:opaque} contains<X(!new), Y>(m: imap<X, Y>, x: X, y: Y) {
    x in m && m[x] == y
  }

  predicate {:opaque} equals<X(!new), Y>(m: imap<X, Y>, m': imap<X, Y>, x: X) {
    (x !in m && x !in m') || (x in m && x in m' && m[x] == m'[x])
  }

  predicate {:opaque} is_subset<X(!new), Y>(m: imap<X, Y>, m': imap<X, Y>) {
    m.Keys <= m'.Keys && (forall x :: x in m.Keys ==> equals(m, m', x))
  }

  function {:opaque} union_prefer_first<X, Y>(m: imap<X, Y>, m': imap<X, Y>): (m'': imap<X, Y>)
    ensures m''.Keys == m.Keys + m'.Keys
    ensures forall k :: k in m.Keys ==> m''[k] == m[k]
    ensures forall k :: k in m'.Keys - m.Keys ==> m''[k] == m'[k]
    ensures forall k :: k in m'.Keys && !(k in m.Keys) ==> m''[k] == m'[k]
  {
    imap x | (x in m.Keys + m'.Keys) :: if x in m then m[x] else m'[x]
  }

  function {:opaque} union_prefer_second<X, Y>(m: imap<X, Y>, m': imap<X, Y>): (m'': imap<X, Y>)
    ensures m''.Keys == m.Keys + m'.Keys
    ensures forall k :: k in m'.Keys ==> m''[k] == m'[k]
    ensures forall k :: k in m.Keys - m'.Keys ==> m''[k] == m[k]
    ensures forall k :: k in m.Keys && !(k in m'.Keys) ==> m''[k] == m[k]
  {
    imap x | (x in m.Keys + m'.Keys) :: if x in m' then m'[x] else m[x]
  }

  function {:opaque} union<X, Y>(m: imap<X, Y>, m': imap<X, Y>): (m'': imap<X, Y>)
		ensures m''.Keys == m.Keys + m'.Keys
		ensures forall k :: k in m.Keys - m'.Keys ==> m[k] == m''[k]
		ensures forall k :: k in m'.Keys - m.Keys ==> m'[k] == m''[k]
		ensures forall k :: k in m.Keys * m'.Keys ==>	m'[k] == m''[k] ||
                                                  m[k] == m''[k]
	{
		union_prefer_first(m, m')
	}

  function {:opaque} restrict<X, Y>(m: imap<X, Y>, xs: iset<X>): (m': imap<X, Y>) {
    imap x | x in xs && x in m :: m[x]
  }

  predicate {:opaque} injective<X(!new), Y>(m: imap<X, Y>) {
    forall x, x' | x != x' && x in m && x' in m :: m[x] != m[x']
  }

  function {:opaque} invert<X, Y(!new)>(m: imap<X, Y>): (m': imap<Y, X>) {
    imap y | y in m.Values :: var x :| x in m && m[x] == y; x
  }

  lemma lemma_invert_is_injective<X, Y>(m: imap<X, Y>)
    ensures injective(invert(m))
  {
    reveal_injective();
    reveal_invert();
  }

  predicate {:opaque} total<X(!new), Y>(m: imap<X, Y>) {
    forall i :: i in m
  }

  predicate {:opaque} monotonic(m: imap<int, int>) {
    forall x, x' :: x in m && x' in m && x <= x' ==> m[x] <= m[x']
  }

  predicate {:opaque} monotonic_from(start: int, m: imap<int, int>) {
    forall x, x' :: x in m && x' in m && start <= x <= x' ==> m[x] <= m[x']
  }

  predicate {:opaque} monotonic_behavior<X>(m: imap<int, X>, m': imap<X, int>)
    requires total(m)
    requires total(m')
  {
    reveal_total();
    forall x, x' :: x <= x' ==> m'[m[x]] <= m'[m[x']]
  }

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
