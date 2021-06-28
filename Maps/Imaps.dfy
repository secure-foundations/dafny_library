module Imaps {

  predicate total<X(!new), Y>(m: imap<X, Y>) {
    forall i :: i in m
  }

  predicate monotonic(m: imap<int, int>) {
    forall x, x' :: x in m && x' in m && x <= x' ==> m[x] <= m[x']
  }

  predicate monotonic_from(start: int, m: imap<int, int>) {
    forall x, x' :: x in m && x' in m && start <= x <= x' ==> m[x] <= m[x']
  }

  predicate monotonic_behavior<X>(m: imap<int, X>, m': imap<X, int>)
    requires total(m)
    requires total(m')
  {
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
