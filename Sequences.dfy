include "SeqLast.dfy"
include "Options.dfy"

// add in copyright from all libraries?

module Seq {
  import opened SeqLast
  import opened Options

  // converts a sequence to a multiset
  // multiset() specifically converts a sequence to a multiset; no set() exists
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
  predicate {:opaque} has_no_duplicates<T>(s: seq<T>) 
  {
    (forall i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j])
  }

  /* if sequence a and b don't have duplicates, then the
  concatenated sequence of a + b will not contain duplicates either */
  lemma {:timeLimitMultiplier 3} lemma_no_duplicates_in_concat<T>(a: seq<T>, b: seq<T>)
    requires has_no_duplicates(a);
    requires has_no_duplicates(b);
    requires multiset(a) !! multiset(b);
    ensures has_no_duplicates(a+b);
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
  lemma lemma_cardinality_of_set_no_duplicates<T>(s: seq<T>)
    requires has_no_duplicates(s)
    ensures |to_set(s)| == |s|
  {
    reveal_has_no_duplicates();
    if |s| == 0 {
    } else {
      lemma_cardinality_of_set_no_duplicates(drop_last(s));
      assert to_set(s) == to_set(drop_last(s)) + {last(s)};
    }
  }

  // proves that there are no duplicate values in the multiset
  lemma lemma_multiset_has_no_duplicates<T>(s: seq<T>)
    requires has_no_duplicates(s)
    ensures forall x | x in multiset(s):: multiset(s)[x] == 1
  {
    if |s| == 0 {
    } else {
      assert s == drop_last(s) + [ last(s) ];
      assert last(s) !in drop_last(s) by {
        reveal_has_no_duplicates();
      }
      assert has_no_duplicates(drop_last(s)) by {
        reveal_has_no_duplicates();
      }
      lemma_multiset_has_no_duplicates(drop_last(s));
    }
  }

   // returns the index of a certain element in the sequence
  function index_of<T>(s: seq<T>, v: T): Option<nat>
    requires v in s;
    ensures var i:= index_of(s, v);
    if i.Some? then i.value < |s| && s[i.value] == v else v !in s;
  {
    if i :| 0 <= i < |s| && s[i] == v then Some(i) else None
  }

  // slices out a specific position's value from the sequence and returns the new sequence
  function method {:opaque} remove<T>(s: seq<T>, pos: nat): seq<T>
    requires pos < |s|
    ensures |remove(s, pos)| == |s| - 1
    ensures forall i | 0 <= i < pos :: remove(s, pos)[i] == s[i]
    ensures forall i | pos <= i < |s| - 1 :: remove(s, pos)[i] == s[i+1]
  {
    s[.. pos] + s[pos + 1 ..] 
  }

  // slices out a specific value from the sequence and returns the new sequence
  function {:opaque} remove_one_value<T>(s: seq<T>, v: T): (s': seq<T>)
    ensures has_no_duplicates(s) ==> has_no_duplicates(s') && to_set(s') == to_set(s) - {v}
  {
    reveal_has_no_duplicates();
    if v !in s then s else
    var i :| 0 <= i < |s| && s[i] == v;
    s[.. i] + s[i + 1 ..]
  }

  // inserts a certain value into a specified index of the sequence and returns the new sequence
  function method {:opaque} insert<T>(s: seq<T>, a: T, pos: int): seq<T>
    requires 0 <= pos <= |s|;
    ensures |insert(s,a,pos)| == |s| + 1;
    ensures forall i :: 0 <= i < pos ==> insert(s, a, pos)[i] == s[i];
    ensures forall i :: pos <= i < |s| ==> insert(s, a, pos)[i+1] == s[i];
    ensures insert(s, a, pos)[pos] == a;
  {
    s[..pos] + [a] + s[pos..]
  }

  // shows that the inserted element is now included in the multiset
  lemma lemma_insert_multiset<T>(s: seq<T>, a: T, pos: nat)
    requires pos <= |s|;
    ensures multiset(insert(s, a, pos)) == multiset(s) + multiset{a}
  {
    reveal_insert();
    assert s == s[..pos] + s[pos..];
  }

  predicate {:opaque} is_prefix<T>(a: seq<T>, b: seq<T>)
    ensures is_prefix(a, b) ==> |a| <= |b|
  {
    && |a| <= |b|
    && a == b[..|a|]    
  } 
  
  predicate {:opaque} is_suffix<T>(a: seq<T>, b: seq<T>) {
    && |a| <= |b|
    && a == b[|b|-|a|..]
  }

    
  function method {:opaque} repeat<T>(v: T, length: nat): (s: seq<T>)
    ensures |s| == length
    ensures forall i: nat | i < |s| :: s[i] == v
  {
    if length == 0 then
      []
    else
      [v] + repeat(v, length - 1)
  }

  // explains associative property of sequences in addition
  lemma lemma_addition_is_associative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
  ensures a+(b+c) == (a+b)+c;
  {
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

   lemma lemma_zip_of_unzip<A,B>(s: seq<(A,B)>)
  // if a sequence is unzipped and then zipped, it forms the original sequence
    ensures zip(unzip(s).0, unzip(s).1) == s
  {
  }

  // unzips a sequence that contains ordered pairs into 2 seperate sequences
  function method {:opaque} unzip<A,B>(s: seq<(A, B)>): (seq<A>, seq<B>)
    ensures |unzip(s).0| == |unzip(s).1| == |s|
    ensures forall i :: 0 <= i < |s| ==> (unzip(s).0[i], unzip(s).1[i]) == s[i]
  {
    if |s| == 0 then ([], [])
    else
      var (a, b):= unzip(drop_last(s));
      (a + [last(s).0], b + [last(s).1])
  }
  
  // if a zipped sequence is unzipped, this results in two seperate sequences
  lemma lemma_unzip_of_zip<A,B>(a: seq<A>, b: seq<B>)
    requires |a| == |b|
    ensures unzip(zip(a, b)).0 == a
    ensures unzip(zip(a, b)).1 == b
  {
  }

  /* a sequence that is sliced at the jth element concatenated with that same
  sequence sliced from the jth element is equal to the original, unsliced sequence */
  lemma lemma_split_act<T>(s: seq<T>, pos: nat)
    requires pos<|s|;
    ensures s[..pos] + s[pos..] == s;
  {
  }

  // ensures that the element from a slice is included in the original sequence
  lemma lemma_element_from_slice<T>(s: seq<T>, s':seq<T>, a:int, b:int, pos:nat)
    requires 0 <= a <= b <= |s|;
    requires s' == s[a..b];
    requires a <= pos < b;
    ensures  pos - a < |s'|;
    ensures  s'[pos-a] == s[pos];
  {
  }

  lemma lemma_slice_of_slice<T>(s: seq<T>, s1:int, e1:int, s2:int, e2:int)
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

}