module Imaps {
  predicate total<S(!new), T>(m: imap<S, T>) {
    forall s :: s in m
  }

  predicate monotonic(m: imap<int, int>) {
    forall s, s' :: s in m && s' in m && s <= s' ==> m[s] <= m[s']
  }

  predicate monotonic_from(start: int, m: imap<int, int>) {
    forall s, s' :: s in m && s' in m && start <= s <= s' ==> m[s] <= m[s']
  }

  predicate monotonic_behavior<S>(x: imap<int, S>, y: imap<S, int>)
    requires total(x)
    requires total(y)
  {
    forall s, s' :: s <= s' ==> y[x[s]] <= y[x[s']]
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
