include "SeqLast.dfy"
include "Mathematics.dfy"

module SeqExtrema {

  import opened SeqLast
  import Math = Mathematics

  // returns the maximum integer value in the sequence
  function method {:opaque} max(s: seq<int>): int
    requires 0 < |s|
    ensures forall k :: k in s ==> max(s) >= k
    ensures max(s) in s
  {
    assert s == drop_last(s) + [last(s)];

    if |s| == 1 then s[0] else Math.max(max(drop_last(s)), last(s))
  }

  // function method max_of_concat(a: seq<int>, b: seq<int>): int
  //   requires 0 < |a| && 0 < |b|
  //   ensures max(a+b) >= max(a)
  //   ensures max(a+b) >= max(b)
  //   ensures forall i :: i in a+b ==> max(a+b) >= i
  // {
  //   reveal_max();
  //   if max(b) >= max(a) then max(b) else max(a)
  // }

  // returns the minimum integer value in the sequence
  function method {:opaque} min(s: seq<int>): int
    requires 0 < |s|
    ensures forall k :: k in s ==> min(s) <= k
    ensures min(s) in s
  {
    assert s == drop_last(s) + [last(s)];
    if |s| == 1 then s[0] else Math.min(min(drop_last(s)), last(s))
  }

  // necessary for lemma_subseq_max
  /* the maximum value in sequence 1 is greater than or equal to the maximum
  value of sequence 2 */
  lemma lemma_max_correspondence(s1:seq<int>, s2:seq<int>, wit: seq<nat>)
    requires 0 < |s1|
    requires 0 < |s2|
    requires |wit| == |s2|
    requires forall j:nat :: j < |wit| ==> wit[j] < |s1|
    requires forall i :: 0 <= i < |s2| ==> s2[i] <= s1[wit[i]]
    ensures max(s2) <= max(s1)
  {
    if max(s2) > max(s1) {
      var k :| 0 <= k < |s2| && s2[k] == max(s2);
      assert s1[wit[k]] in s1;
      assert false;
    }
  }

  /* the maximum element in any subsequence will not be 
  greater than the maximum element in the full sequence */
  lemma lemma_subseq_max(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures max(s[from .. to]) <= max(s)
  {
    var subseq := s[from .. to];
    lemma_max_correspondence(s, subseq, seq(|subseq|, i requires 0<=i<|subseq| => i + from));
  }

  lemma lemma_min_correspondence(s1:seq<int>, s2:seq<int>, wit: seq<nat>)
    requires 0 < |s1|
    requires 0 < |s2|
    requires |wit| == |s2|
    requires forall j:nat :: j < |wit| ==> wit[j] < |s1|
    requires forall i :: 0 <= i < |s2| ==> s2[i] >= s1[wit[i]]
    ensures min(s2) >= min(s1)
  {
    if min(s2) < min(s1) {
      var k :| 0 <= k < |s2| && s2[k] == min(s2);
      assert s1[wit[k]] in s1;
    }
  }

  lemma lemma_subseq_min(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures min(s[from..to]) >= min(s)
    {
      var subseq := s[from..to];
      lemma_min_correspondence(s, subseq, seq(|subseq|, i requires 0<=i<|subseq| => i + from));
    }
}