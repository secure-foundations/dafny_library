include "Mathematics.dfy"
include "Options.dfy"
include "SeqLast.dfy"
// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module Seq {
  import opened Options
  import Math = Mathematics
  import opened SeqLast

  /* a sequence that is sliced at the jth element concatenated with that same
  sequence sliced from the jth element is equal to the original, unsliced sequence */
  lemma lemma_split_act<T>(intseq: seq<T>, j: int)
  requires 0<=j<|intseq|;
  ensures intseq[..j] + intseq[j..] == intseq;
  {
  }

  /* explains sequence reduction */
  lemma lemma_sequence_reduction<T>(s: seq<T>, b: nat)
    requires 0<b<|s|;
    ensures s[0..b][0..b-1] == s[0..b-1];
  {
    var t := s[0..b];
    forall (i | 0 <= i < b-1)
      ensures s[0..b][0..b-1][i] == s[0..b-1][i];
    {
    }
  }
  
  // converts a sequence to a multiset
  function method to_set<T>(s: seq<T>): set<T> 
  {
    set x: T | x in multiset(s)
  }


  /* proves that the cardinality of a subsequence is always less than or equal to that
  of the full sequence */
  lemma lemma_cardinality_of_set<T>(s: seq<T>)
    ensures |to_set(s)| <= |s| // length of the subset is less than the length of the set
  {
    if |s| == 0 {
    } else {
      assert to_set(s) == to_set(drop_last(s)) + {last(s)};
      lemma_cardinality_of_set(drop_last(s));
    }
  }
  
  // the cardinality of a subsequence of an empty sequence is also 0
  lemma lemma_cardinality_of_empty_set_is_0<T>(s: seq<T>)
    ensures |to_set(s)| == 0 <==> |s| == 0
  {
    if |s| != 0 {
      assert s[0] in to_set(s);
    }
  }

  // returns true if there are no duplicate values in the sequence
  predicate {:opaque} has_no_duplicates<T>(a: seq<T>) 
  {
    (forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j])
  }

  /* if sequence a and b don't have duplicates AND they are disjoint, then the
  concatenated sequence of a + b will not contain duplicates either */
  lemma {:timeLimitMultiplier 3} lemma_no_duplicates_in_concat<T>(a: seq<T>, b: seq<T>)
    requires has_no_duplicates(a);
    requires has_no_duplicates(b);
    requires multiset(a) !! multiset(b);
    ensures has_no_duplicates(a + b);
  {
    reveal_has_no_duplicates();
    var c := a + b;
    if |c| > 1 {
      assert forall i, j :: i != j && 0 <= i < |a| && |a| <= j < |c| ==>
        c[i] in multiset(a) && c[j] in multiset(b) && c[i] != c[j]; 
    }
  }

  /* proves that the sequence the length of the multiset version of the sequence
  is the same as the sequence, given that there are no duplicates involved */
  lemma lemma_cardinality_of_set_no_duplicates<T>(a: seq<T>)
    requires has_no_duplicates(a)
    ensures |to_set(a)| == |a|
  {
    reveal_has_no_duplicates();
    if |a| == 0 {
    } else {
      lemma_cardinality_of_set_no_duplicates(drop_last(a));
      assert to_set(a) == to_set(drop_last(a)) + {last(a)};
    }
  }

  // proves that there are no duplicate values in the multiset
  lemma lemma_multiset_has_no_duplicates<T>(a: seq<T>)
    requires has_no_duplicates(a)
    ensures forall x | x in multiset(a):: multiset(a)[x] == 1
  {
    if |a| == 0 {
    } else {
      assert a == drop_last(a) + [ last(a) ];
      assert last(a) !in drop_last(a) by {
        reveal_has_no_duplicates();
      }
      assert has_no_duplicates(drop_last(a)) by {
        reveal_has_no_duplicates();
      }
      lemma_multiset_has_no_duplicates(drop_last(a));
    }
  }

  // returns the index of a certain element in the sequence
  function index_of<T>(s: seq<T>, e: T): int
    requires e in s;
    ensures 0 <= index_of(s,e) < |s|;
    ensures s[index_of(s,e)] == e;
  {
    var i :| 0 <= i < |s| && s[i] == e;
    i
  }

  /* finds the index of a certain value in the sequence, if it exists. Returns
  the index, or -1 if the value is not included in the sequence */
  function find_index_in_sequence<T>(s: seq<T>, v: T): Option<nat>
    ensures var idx := find_index_in_sequence(s, v);
            if idx.Some? then
              idx.value < |s| && s[idx.value] == v
            else
              v !in s
  {
    if v in s then
      Some(index_of(s, v))
    else
      None
  }

  // slices out a specific position's value from the sequence and returns the new sequence
  function method {:opaque} remove<A>(s: seq<A>, pos: int): seq<A>
  requires 0 <= pos < |s|
  ensures |remove(s, pos)| == |s| - 1
  ensures forall i | 0 <= i < pos :: remove(s, pos)[i] == s[i]
  ensures forall i | pos <= i < |s| - 1 :: remove(s, pos)[i] == s[i+1]
  {
    s[.. pos] + s[pos + 1 ..] 
  }

  // slices out a specific value from the sequence and returns the new sequence
  function {:opaque} remove_one_value<V>(s: seq<V>, v: V): (s': seq<V>)
    ensures has_no_duplicates(s) ==> has_no_duplicates(s') && to_set(s') == to_set(s) - {v}
  {
    reveal_has_no_duplicates();
    if v !in s then s else
    var i :| 0 <= i < |s| && s[i] == v;
    s[.. i] + s[i + 1 ..]
  }

  // inserts a certain value into a specified index of the sequence and returns the new sequence
  function method {:opaque} insert<A>(s: seq<A>, a: A, pos: int): seq<A>
  requires 0 <= pos <= |s|;
  ensures |insert(s,a,pos)| == |s| + 1;
  ensures forall i :: 0 <= i < pos ==> insert(s, a, pos)[i] == s[i];
  ensures forall i :: pos <= i < |s| ==> insert(s, a, pos)[i+1] == s[i];
  ensures insert(s, a, pos)[pos] == a;
  {
    s[..pos] + [a] + s[pos..]
  }

  // shows that the inserted element is now included in the multiset
  lemma lemma_insert_multiset<A>(s: seq<A>, a: A, pos: int)
    requires 0 <= pos <= |s|;
    ensures multiset(insert(s, a, pos)) == multiset(s) + multiset{a}
  {
    reveal_insert();
    assert s == s[..pos] + s[pos..];
  }

  // explains associative property of sequences in addition
  lemma lemma_seq_addition_is_associative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
  ensures a+(b+c) == (a+b)+c;
  {
  }

  /* explains the associative nature of adding sequences*/
  lemma lemma_seq_concatenation_associative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
      ensures (a+b)+c == a+(b+c);
  {
  }

  /* concatenating two sequences of sequences is equivalent to concatenating
  each sequence of sequences seperately, and then concatenating the two resulting 
  sequences together */
  lemma lemma_seq_concat_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
    ensures seq_concat(A + B) == seq_concat(A) + seq_concat(B)
  {
    if |A| == 0 {
      assert A+B == B;
    } else {
      calc == {
        seq_concat(A + B);
          { assert (A + B)[0] == A[0];  assert (A + B)[1..] == A[1..] + B; }
        A[0] + seq_concat(A[1..] + B);
        A[0] + seq_concat(A[1..]) + seq_concat(B);
        seq_concat(A) + seq_concat(B);
      }
    }
  }

  // proves sequence addition
  lemma lemma_concat_seq_addition<A>(a: seq<seq<A>>, b: seq<seq<A>>)
  ensures concat_seq(a + b) == concat_seq(a) + concat_seq(b)
  {
    if b == [] {
      calc {
        concat_seq(a + b);
        { assert a + b == a; }
        concat_seq(a);
        {
          reveal_concat_seq();
          assert concat_seq(b) == [];
        }
        concat_seq(a) + concat_seq(b);
      }
    } else {
      calc {
        concat_seq(a + b);
        { reveal_concat_seq(); }
        concat_seq(drop_last(a + b)) + last(a + b);
        {
          assert drop_last(a + b) == a + drop_last(b);
          assert last(a + b) == last(b);
        }
        concat_seq(a + drop_last(b)) + last(b);
        {
          lemma_concat_seq_addition(a, drop_last(b));
        }
        concat_seq(a) + concat_seq(drop_last(b)) + last(b);
        { reveal_concat_seq(); }
        concat_seq(a) + concat_seq(b);
      }
    }
  }

  /* concatenates the sequence of sequences into a single sequence. 
  works by adding elements from last to first */
  function method seq_concat_reverse<T>(seqs: seq<seq<T>>): seq<T>
  decreases |seqs|
  {
    if |seqs| == 0 then []
    else seq_concat_reverse(drop_last(seqs)) + last(seqs)
  }

  /* concatenating two reversed sequences of sequences is the same as reversing two 
  sequences of sequences and then adding the two resulting sequences together */
  lemma lemma_seq_concat_reverse_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
  ensures seq_concat_reverse(A + B) == seq_concat_reverse(A) + seq_concat_reverse(B)
  {
    if |B| == 0 {
      assert seq_concat_reverse(B) == [];
      assert A+B == A;
    } else {
      calc == {
        seq_concat_reverse(A + B);
          { assert last(A + B) == last(B);  assert drop_last(A + B) == A + drop_last(B); }
        seq_concat_reverse(A + drop_last(B)) + last(B);
        seq_concat_reverse(A) + seq_concat_reverse(drop_last(B)) + last(B);
        seq_concat_reverse(A) + seq_concat_reverse(B);
      }
    }
  }

  /* both methods of concatenating sequence (starting from front v. starting from back)
  result in the same sequence */
  lemma lemma_seq_concat_and_seq_concat_reverse_are_equivalent<T>(seqs: seq<seq<T>>)
    ensures seq_concat(seqs) == seq_concat_reverse(seqs)
  {
    if |seqs| == 0 {
    } else {
      calc == {
        seq_concat_reverse(seqs);
        seq_concat_reverse(drop_last(seqs)) + last(seqs);
          { lemma_seq_concat_and_seq_concat_reverse_are_equivalent(drop_last(seqs)); }
        seq_concat(drop_last(seqs)) + last(seqs);
        seq_concat(drop_last(seqs)) + seq_concat([last(seqs)]);
          { lemma_seq_concat_adds(drop_last(seqs), [last(seqs)]); 
        assert seqs == drop_last(seqs) + [last(seqs)]; }
        seq_concat(seqs);
      }
    }
  }

  /* the concatenated sequence's length is greater than or equal to 
  each individual inner sequence's length */
  lemma lemma_concat_seq_length_ge_single_element_length<A>(a: seq<seq<A>>, i: int)
  requires 0 <= i < |a|
  ensures |concat_seq(a)| >= |a[i]|
  {
    reveal_concat_seq();
    if i < |a| - 1 {
      lemma_concat_seq_length_ge_single_element_length(a[..|a|-1], i);
    }
  }

  /* the length of concatenating sequence in a sequence together will be no longer 
  than the length of the original sequence of sequences multiplied by the length of 
  the longest sequence */
  lemma lemma_concat_seq_length_le_mul<A>(a: seq<seq<A>>, t: int)
  requires forall i | 0 <= i < |a| :: |a[i]| <= t
  ensures |concat_seq(a)| <= |a| * t
  {
    reveal_concat_seq();
    if |a| == 0 {
    } else {
      lemma_concat_seq_length_le_mul(a[..|a|-1], t);
    }
  }
  
  predicate {:opaque} IsPrefix<A>(a: seq<A>, b: seq<A>)
  ensures IsPrefix(a, b) ==> |a| <= |b|
  {
    && |a| <= |b|
    && a == b[..|a|]
  }
  
  predicate {:opaque} IsSuffix<A>(a: seq<A>, b: seq<A>) {
    && |a| <= |b|
    && a == b[|b|-|a|..]
  }
  
  function method {:opaque} repeat<V>(v: V, length: nat): (res: seq<V>)
  ensures |res| == length
  ensures forall i: nat | i < |res| :: res[i] == v
  {
    if length == 0 then
      []
    else
      [v] + repeat(v, length - 1)
  }

  /* takes two sequences, a and b, and combines then to form one sequence in which
  each position contains an ordered pair from a and b */
  function method {:opaque} zip<A,B>(a: seq<A>, b: seq<B>): seq<(A,B)>
    requires |a| == |b|
    ensures |zip(a, b)| == |a|
    ensures forall i :: 0 <= i < |zip(a, b)| ==> zip(a, b)[i] == (a[i], b[i])
  {
    if |a| == 0 then []
    else zip(drop_last(a), drop_last(b)) + [(last(a), last(b))]
  }

  // unzips a sequence that contains ordered pairs into 2 seperate sequences
  function method {:opaque} unzip<A,B>(z: seq<(A, B)>): (seq<A>, seq<B>)
    ensures |unzip(z).0| == |unzip(z).1| == |z|
    ensures forall i :: 0 <= i < |z| ==> (unzip(z).0[i], unzip(z).1[i]) == z[i]
  {
    if |z| == 0 then ([], [])
    else
      var (a, b):= unzip(drop_last(z));
      (a + [last(z).0], b + [last(z).1])
  }

  // if a sequence is unzipped and then zipped, it forms the original sequence
  lemma lemma_zip_of_unzip<A,B>(s: seq<(A,B)>)
    ensures zip(unzip(s).0, unzip(s).1) == s
  {
  }
  
  // if a zipped sequence is unzipped, this results in two seperate sequences
  lemma lemma_unzip_of_zip<A,B>(sa: seq<A>, sb: seq<B>)
    requires |sa| == |sb|
    ensures unzip(zip(sa, sb)).0 == sa
    ensures unzip(zip(sa, sb)).1 == sb
  {
  }

  // returns the maximum integer value in the sequence
  function method {:opaque} seq_max(s: seq<int>): int
    requires 0 < |s|
    ensures forall k :: k in s ==> seq_max(s) >= k
    ensures seq_max(s) in s
  {
    assert s == drop_last(s) + [last(s)];

    if |s| == 1 then
      s[0]
    else
      Math.max(seq_max(drop_last(s)), last(s))
  }

  /* the maximum element in any subsequence will not be 
  greater than the maximum element in the full sequence */
  lemma lemma_subseq_max(s: seq<int>, from: nat, to: nat)
    requires 0 <= from < to <= |s|
    ensures seq_max(s[from .. to]) <= seq_max(s)
  {
    var subseq := s[from .. to];
    lemma_seq_max_correspondence(s, subseq, seq(|subseq|, i requires 0<=i<|subseq| => i + from));
  }

  // ensures that the element from a slice is included in the original sequence
  lemma lemma_element_from_seq_slice<T>(s: seq<T>, s':seq<T>, a:int, b:int, pos:int)
    requires 0 <= a <= b <= |s|;
    requires s' == s[a..b];
    requires a <= pos < b;
    ensures  0 <= pos - a < |s'|;
    ensures  s'[pos-a] == s[pos];
  {
  }

  // similar to lemma_seq_slice_slice
  lemma lemma_seq_slice_of_slice<T>(s: seq<T>, s1:int, e1:int, s2:int, e2:int)
    requires 0 <= s1 <= e1 <= |s|;
    requires 0 <= s2 <= e2 <= e1 - s1;
    ensures  s[s1..e1][s2..e2] == s[s1+s2..s1+e2];
  {
    var r1 := s[s1..e1];
    var r2 := r1[s2..e2];
    var r3 := s[s1+s2..s1+e2];
    assert |r2| == |r3|;
    forall i | 0 <= i < |r2| ensures r2[i] == r3[i];
    {
    }
  }

  /* shows the sequence equivalence of slices of slices */
  lemma lemma_seq_slice_slice<T>(s: seq<T>, i: int, j: int, k: int, l: int)
    requires 0 <= i <= j <= |s|
    requires 0 <= k <= l <= j - i
    ensures s[i..j][k..l] == s[i+k..i+l];
  {
    lemma_seq_extensionality(s[i..j][k..l], s[i+k..i+l]);
  }

  /* taking a slice of range i to j and then taking another slice that is within 
  the first range is equivalent to simply slicing the original array */
  lemma lemma_array_slice_slice<T>(ar: array<T>, i: int, j: int, k: int, l: int)
    requires 0 <= i <= j <= ar.Length
    requires 0 <= k <= l <= j - i
    ensures ar[i..j][k..l] == ar[i+k..i+l];
  {
    lemma_seq_slice_slice(ar[..], i, j, k, l);
  }
  
  // converts a map to a sequence
  function method {:opaque} convert_map_to_seq<T>(n:int, m:map<int, T>): seq<T>
    requires n >= 0;
    requires forall i {:trigger i in m} :: 0 <= i < n ==> i in m;
    ensures |convert_map_to_seq(n, m)| == n;
    ensures var s := convert_map_to_seq(n, m);
    forall i {:trigger s[i]} :: 0 <= i < n ==> s[i] == m[i];
  {
      if n == 0 then []
      else convert_map_to_seq(n-1, m) + [m[n-1]]
  }
}