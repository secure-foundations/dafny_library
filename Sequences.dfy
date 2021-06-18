include "Mathematics.dfy"
include "Options.dfy"

// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module Seq {
  import opened Options
  import Math = Mathematics

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

  // returns the last element in the sequence
  function method last<E>(run: seq<E>): E
    requires |run| > 0;
  {
    run[|run|-1]
  }

  // returns the sequence slice up to but not including the last element
  function method drop_last<E>(run: seq<E>): seq<E> 
  requires |run| > 0;
  {
    run[..|run|-1]
  }

  // concatenating everything but the last element + the last element results in the original seq 
  lemma lemma_last<T>(s: seq<T>)
    requires |s| > 0;
    ensures  drop_last(s) + [last(s)] == s;
  {

  }
  
  // converts a sequence to a multiset
  function method to_set<T>(run: seq<T>): set<T> 
  {
    set x: T | x in multiset(run)
  }


  /* proves that the cardinality of a subsequence is always less than or equal to that
  of the full sequence */
  lemma lemma_cardinality_of_set<T>(run: seq<T>)
    ensures |to_set(run)| <= |run| // length of the subset is less than the length of the set
  {
    if |run| == 0 {
    } else {
      assert to_set(run) == to_set(drop_last(run)) + {last(run)};
      lemma_cardinality_of_set(drop_last(run));
    }
  }
  
  // the cardinality of a subsequence of an empty sequence is also 0
  lemma lemma_cardinality_of_empty_set_is_0<T>(run: seq<T>)
    ensures |to_set(run)| == 0 <==> |run| == 0
  {
    if |run| != 0 {
      assert run[0] in to_set(run);
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

  // applies a transformation function on the sequence
  function method {:opaque} Map<E,R>(f: (E ~> R), run: seq<E>): (result: seq<R>)
    requires forall i :: 0 <= i < |run| ==> f.requires(run[i])
    ensures |result| == |run|
    ensures forall i :: 0 <= i < |run| ==> result[i] == f(run[i]);
    reads set i, o | 0 <= i < |run| && o in f.reads(run[i]):: o
  {
    if |run| == 0 then []
    else  [f(run[0])] + Map(f, run[1..])
  }

  // uses a selection function to select elements from the sequence
  function method filter<E>(f : (E ~> bool), run: seq<E>): (result: seq<E>)
    requires forall i :: 0 <= i < |run| ==> f.requires(run[i])
    ensures |result| <= |run|
    ensures forall i: nat :: i < |result| && f.requires(result[i]) ==> f(result[i])
    reads f.reads
  {
    if |run| == 0 then []
    else ((if f(run[0]) then [run[0]] else []) + filter(f, run[1..]))
  }
  
  function method fold_left<A,E>(f: (A, E) -> A, init: A, run: seq<E>): A
  {
    if |run| == 0 then init
    else fold_left(f, f(init, run[0]), run[1..])
  }

  function method fold_right<A,E>(f: (A, E) -> A, init: A, run: seq<E>): A
  {
    if |run| == 0 then init
    else f(fold_right(f, init, run[1..]), run[0])
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

  /* concatenates a sequence of sequences into a single sequence. 
  Works by adding elements in order from first to last */
  function method seq_concat<T>(seqs: seq<seq<T>>): seq<T>
  decreases |seqs|
  {
    if |seqs| == 0 then []
    else seqs[0] + seq_concat(seqs[1..])
  }

  // turns a sequence of sequences into a single sequence and returns the result
  function method {:opaque} concat_seq<A>(a: seq<seq<A>>): seq<A>
  {
    if |a| == 0 then [] else concat_seq(drop_last(a)) + last(a)
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

  // This is a workaround since Dafny right now doesn't support
  // s[i := t] when i is a native type integer.
  //already a function method
  function method {:opaque} SeqIndexUpdate<T>(s: seq<T>, i: int, t: T): seq<T>
  requires i as int + 1 < 0x1_0000_0000_0000_0000
  requires 0 <= i as int < |s|
  ensures SeqIndexUpdate(s, i, t) == s[i as int := t]
  {
    s[..i] + [t] + s[i+1..]
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
  
  /* receives a sequence of sequences. Returns a sequence in which the ith element corresponds 
  to the length of the sequence at the ith position*/
  function method {:opaque} flatten_shape<A>(seqs: seq<seq<A>>): (shape: seq<nat>)
    ensures |shape| == |seqs|
    ensures forall i :: 0 <= i < |shape| ==> shape[i] == |seqs[i]|
  {
    if |seqs| == 0 then []
    else flatten_shape(drop_last(seqs)) + [|last(seqs)|]
  }

  /* concatenating two sequences and then flattening their shape retults in the same
  result as flattenning each sequence first and then concatenating */
  lemma lemma_flatten_shape_addition<A>(seqs1: seq<seq<A>>, seqs2: seq<seq<A>>)
    ensures flatten_shape(seqs1 + seqs2) == flatten_shape(seqs1) + flatten_shape(seqs2)
  {
  }
  
  /* returns a number that results from adding up each all 
  of the elements in the sequence's shape */
  function method {:opaque} flatten_length(shape: seq<nat>): nat
    ensures |shape| == 0 ==> flatten_length(shape) == 0
  {
    if |shape| == 0 then 0
    else flatten_length(drop_last(shape)) + last(shape)
  }

  /* concatenating two "shape" sequences together and then flattening their length is 
  the same as flattening each shape's length and then adding the resulting numbers */
  lemma {:induction true} lemma_flatten_length_addition(shape1: seq<nat>, shape2: seq<nat>)
    ensures flatten_length(shape1 + shape2) == flatten_length(shape1) + flatten_length(shape2)
  {
    if |shape2| == 0 {
      assert shape1 + shape2 == shape1;
    } else {
      reveal_flatten_length();
      assert shape1 + shape2 == (shape1 + drop_last(shape2)) + [last(shape2)];
    }
  }
  
  /* the flattened length of any subsequence of the shape is less than 
  the flattened length of the whole shape */
  lemma lemma_flatten_length_subseq(shape: seq<nat>, from: nat, to: nat)
    requires from <= to <= |shape|
    ensures flatten_length(shape[from..to]) <= flatten_length(shape)
  {
    assert shape == shape[..from] + shape[from..to] + shape[to..];
    lemma_flatten_length_addition(shape[..from] + shape[from..to], shape[to..]);
    lemma_flatten_length_addition(shape[..from], shape[from..to]);
  }

  /* the flattened sequence's length will be equal to flattenening the shape 
  and then flattening the length; returns a sequence that combines all sequences of 
  the sequence */
  function method {:opaque} flatten<A>(seqs: seq<seq<A>>): seq<A>
    ensures |flatten(seqs)| == flatten_length(flatten_shape(seqs))
    ensures |seqs| == 0 ==> |flatten(seqs)| == 0
  {
    reveal_flatten_shape();
    reveal_flatten_length();
    if |seqs| == 0 then []
    else flatten(drop_last(seqs)) + last(seqs)
  }

  // flattening a singleton of sequences will simply result in the original sequence
  lemma lemma_flatten_singleton<A>(s: seq<A>)
    ensures flatten([ s ]) == s
  {
    reveal_flatten();
  }
  
  /* concatenating two sequences and then flattening them has the same result 
  as flattening each sequence seperately and then concatenating afterwards */
  lemma lemma_flatten_addition<A>(seqs1: seq<seq<A>>, seqs2: seq<seq<A>>)
    ensures flatten(seqs1 + seqs2) == flatten(seqs1) + flatten(seqs2)
    decreases |seqs2|
  {
    if |seqs2| == 0 {
      assert seqs1 + seqs2 == seqs1;
    } else if |seqs2| == 1 {
      reveal_flatten();
    } else {
      calc {
        flatten(seqs1 + seqs2);
        { assert seqs1 + seqs2 == seqs1 + drop_last(seqs2) + [ last(seqs2) ]; }
        flatten(seqs1 + drop_last(seqs2) + [ last(seqs2) ]);
        { lemma_flatten_addition(seqs1 + drop_last(seqs2), [ last(seqs2) ]); }
        flatten(seqs1 + drop_last(seqs2)) + flatten([ last(seqs2) ]);
        { lemma_flatten_addition(seqs1, drop_last(seqs2)); }
        flatten(seqs1) + flatten(drop_last(seqs2)) + flatten([ last(seqs2) ]);
        { lemma_flatten_addition(drop_last(seqs2), [ last(seqs2) ]); }
        flatten(seqs1) + flatten(drop_last(seqs2) + [ last(seqs2) ]);
        { assert seqs2 == drop_last(seqs2) + [ last(seqs2) ]; }
        flatten(seqs1) + flatten(seqs2);
      }
    }
  }
  
  /* returns the index of the flattened sequence  */
  function method flatten_index(shape: seq<nat>, i: nat, j: nat): nat
    requires i < |shape|
    requires j < shape[i]
  {
    flatten_length(shape[..i]) + j
  }

  /* returns the index of the unflattened sequence */
  function method unflatten_index(shape: seq<nat>, i: nat): (nat, nat)
    requires i < flatten_length(shape)
  {
    reveal_flatten_length();
    if i < flatten_length(drop_last(shape)) then unflatten_index(drop_last(shape), i)
    else (|shape|-1, i - flatten_length(drop_last(shape)))
  }

  /* the index in a flattened sequence is less than the flattened length
  of the entire sequence */
  lemma lemma_flatten_index_in_bounds(shape: seq<nat>, i: nat, j: nat)
    requires i < |shape|
    requires j < shape[i]
    ensures flatten_index(shape, i, j) < flatten_length(shape)
  {
    reveal_flatten_length();
    if i == |shape|-1 {
    } else {
      lemma_flatten_index_in_bounds(drop_last(shape), i, j);
      assert drop_last(shape)[..i] == shape[..i];
    }
  }
  
  /* the unflattened index is in the bounds if the index is less than the sequence's flattened length  */
  lemma {:induction true} lemma_unflatten_index_in_bounds(shape: seq<nat>, i: nat)
    requires i < flatten_length(shape)
    ensures unflatten_index(shape, i).0 < |shape|
    ensures unflatten_index(shape, i).1 < shape[unflatten_index(shape, i).0]
  {
    var shapeidx := unflatten_index(shape, i).0;
  }

  /* flattening and then unflattening the sequence results in the original sequence */
  lemma {:induction true} lemma_flatten_unflatten_indentity(shape: seq<nat>, i: nat)
    requires i < flatten_length(shape)
    ensures unflatten_index(shape, i).0 < |shape|
    ensures unflatten_index(shape, i).1 < shape[unflatten_index(shape, i).0]
    ensures i == flatten_index(shape, unflatten_index(shape, i).0, unflatten_index(shape, i).1)
  {
    lemma_unflatten_index_in_bounds(shape, i);
    var (shapeidx, shapeoff):= unflatten_index(shape, i);
    if shapeidx == |shape|-1 {
    } else {
      lemma_flatten_unflatten_indentity(drop_last(shape), i);
      assert drop_last(shape)[..shapeidx] == shape[..shapeidx];
    }
  }
  
  /* unflattening and then flattening the sequence results in the original sequence */
  lemma lemma_unflatten_flatten_identity(shape: seq<nat>, i: nat, j: nat)
    requires i < |shape|
    requires j < shape[i]
    ensures flatten_index(shape, i, j) < flatten_length(shape)
    ensures (i, j) == unflatten_index(shape, flatten_index(shape, i, j))
  {
    lemma_flatten_index_in_bounds(shape, i, j);
    if i == |shape| - 1 {
    } else {
      lemma_unflatten_flatten_identity(drop_last(shape), i, j);
      assert drop_last(shape)[..i] == shape[..i];
    }
  }
  
  // the ordering of flattened indicies is also an indicator of placement in the unflattened sequence
  lemma {:induction true} lemma_unflatten_index_ordering(shape: seq<nat>, i: nat, j: nat)
    requires i < j < flatten_length(shape)
    ensures unflatten_index(shape, i).0 <= unflatten_index(shape, j).0
    ensures unflatten_index(shape, i).0 == unflatten_index(shape, j).0 ==> unflatten_index(shape, i).1 < unflatten_index(shape, j).1
  {
    lemma_flatten_unflatten_indentity(shape, i);
  }

  // the flattened index is correct
  lemma lemma_flatten_index_is_correct<A>(seqs: seq<seq<A>>, i: nat, j: nat)
    requires i < |seqs|
    requires j < |seqs[i]|
    ensures flatten_index(flatten_shape(seqs), i, j) < |flatten(seqs)|
    ensures flatten(seqs)[flatten_index(flatten_shape(seqs), i, j)] == seqs[i][j]
  {
    reveal_flatten();
    lemma_flatten_index_in_bounds(flatten_shape(seqs), i, j);
    if i == |seqs|-1 {
    } else {
      lemma_flatten_index_is_correct(drop_last(seqs), i, j);
      assert drop_last(flatten_shape(seqs))[..i] == flatten_shape(seqs)[..i];
    }
  }

  // proves that the unflattened index is correct
  lemma {:induction true} {:timeLimitMultiplier 3} lemma_unflatten_index_is_correct<A>(seqs: seq<seq<A>>, i: nat)
    requires i < flatten_length(flatten_shape(seqs))
    ensures unflatten_index(flatten_shape(seqs), i).0 < |seqs|
    ensures unflatten_index(flatten_shape(seqs), i).1 < |seqs[unflatten_index(flatten_shape(seqs), i).0]|
    ensures flatten(seqs)[i] == seqs[unflatten_index(flatten_shape(seqs), i).0][unflatten_index(flatten_shape(seqs), i).1]
  {
    var shape := flatten_shape(seqs);
    lemma_unflatten_index_in_bounds(shape, i);
    reveal_flatten();
  }

  /* proves that the cardinality of the set is the same as the cardinality 
  of the sequence, given that the set is the same size as the sequence*/
  lemma lemma_cardinality_of_set_and_sequence<T>(q:seq<T>, t:set<int>)
    requires t == set i | 0 <= i < |q|
    ensures |t| == |q|
  {
    if |q| > 0 {
      var sq := q[..|q|-1];
      var st := set i | 0 <= i < |sq|;
      calc {
        |q|;
        |sq| + 1;
          { lemma_cardinality_of_set_and_sequence(sq, st); }
        |st| + 1;
          { assert t == st + {|sq|}; }
        |t|;
      }
    }
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

  /* the maximum value in sequence 1 is greater than or equal to the maximum
  value of sequence 2 */
  lemma lemma_seq_max_correspondence(s1:seq<int>, s2:seq<int>, wit: seq<nat>)
    requires 0 < |s1|
    requires 0 < |s2|
    requires |wit| == |s2|
    requires forall j:nat :: j < |wit| ==> wit[j] < |s1|
    requires forall i :: 0 <= i < |s2| ==> s2[i] <= s1[wit[i]]
    ensures seq_max(s2) <= seq_max(s1)
  {
    if seq_max(s2) > seq_max(s1) {
      var idx :| 0 <= idx < |s2| && s2[idx] == seq_max(s2);
      assert s1[wit[idx]] in s1;  // trigger
      assert false;
    }
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

  /* proves that if a sequence is sliced from i until the end and then sliced a seconds time, 
  the resulting sequence is the same as the original sequence shifted by i */ 
  lemma lemma_seq_suffix_slice<T>(s: seq<T>, i: int, j: int, k: int)
    requires 0 <= i <= |s|
    requires 0 <= j <= k <= |s| - i
    ensures s[i..][j..k] == s[i+j..i+k];
  {
  }

  // the given element is included in the sequence's sliced portion
  lemma lemma_element_from_seq_suffix<T>(s: seq<T>, s':seq<T>, a:int, pos:int)
    requires 0 <= a <= |s|;
    requires s' == s[a..];
    requires a <= pos < |s|;
    ensures  s'[pos-a] == s[pos];
  {
  }

  /* if a sequence is sliced after the a certain length, the new sequence's
  elements' values are shifted down by that length*/
  lemma lemma_seq_suffix<T>(s: seq<T>, prefix_length: int, index: int)
    requires 0 <= prefix_length <= index < |s|;
    ensures s[index] == s[prefix_length..][index - prefix_length];
  {
  }

  /* if a sequence is sliced in a certain interval and then sliced again
  from k until the end, then this is the same as slicing the initial
  sequence from the first + the second slice */
  lemma lemma_seq_slice_suffix<T>(s: seq<T>, i: int, j: int, k: int)
    requires 0 <= i <= j <= |s|
    requires 0 <= k <= j - i
    ensures s[i..j][k..] == s[i+k..j];
  { 
  }

  /* proves that if an array is sliced from i until the end and then sliced a seconds time, 
  the resulting array is the same as the original array shifted by i */ 
  lemma lemma_array_suffix_slice<T>(ar: array<T>, i: int, j: int, k: int)
    requires 0 <= i <= ar.Length
    requires 0 <= j <= k <= ar.Length - i
    ensures ar[i..][j..k] == ar[i+j..i+k];
  {
  }

  /* if a sequence is sliced after the first element, the new sequence's
  elements' values are shifted down by 1 */
  lemma lemma_seq_shift_after_slicing<T>(sequence:seq<T>, j:int)
    requires 0<=j<|sequence|-1;
    ensures sequence[1..][j] == sequence[j+1];
  {
  }

  // increments all of the elements of the sequence of ints by a specified amount
  function method increment_seq(s: seq<int>, amount:int): seq<int>
    ensures var s' := increment_seq(s, amount);
      |s| == |s'| && forall i :: 0 <= i < |s'| ==> s'[i] == s[i] + amount;
  {
    if s == [] then [] else [s[0] + amount] + increment_seq(s[1..], amount)
  }

  // proves that sequence a and b are equal
  lemma lemma_seq_equal<E>(a: seq<E>, b: seq<E>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> a[i] == b[i]
    ensures a == b
  {
  }

  /* if sequence a and sequence b are of equall lengths and all of their
  elements are equal, a and b are equal sequences */ 
  lemma lemma_seq_equality<T>(a:seq<T>, b:seq<T>, len:int)
    requires |a| == |b| == len;
    requires forall i {:trigger a[i]}{:trigger b[i]} :: 0 <= i < len ==> a[i] == b[i];
    ensures a == b;
  {
    assert forall i :: 0 <= i < len ==> a[i] == b[i];
  }

  /* if the length two sequences are equal and each element is equal, then the two
  sequences are equal */
  lemma lemma_seq_extensionality<T>(s: seq<T>, t: seq<T>)
    requires |s| == |t|
    requires forall i | 0 <= i < |s| :: s[i] == t[i]
    ensures s == t
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

  /* if two sequences have the same elements in a certain interval
  the subsequences over that interval are equal */
  lemma lemma_seq_extensionality_slice<T>(s: seq<T>, t: seq<T>, a: int, b: int)
    requires 0 <= a <= b <= |s|
    requires b <= |t|
    requires forall i | a <= i < b :: s[i] == t[i]
    ensures s[a..b] == t[a..b]
  {
  }

  // fills the sequence with n identical elements
  function method {:opaque} fill<T>(n: int, t: T): (res: seq<T>)
    requires n >= 0
    ensures |res| == n
    ensures forall i | 0 <= i < n :: res[i] == t
  {
    if n == 0 then [] else fill(n-1, t) + [t]
  }

  /* concatenating two sequences and then taking a slice starting from an index 
  that is greater than the first sequence is the same as taking a slice from the 
  second sequence */
  lemma sum_slice_second<T>(a: seq<T>, b: seq<T>, i: int, j: int)
    requires |a| <= i <= j <= |a| + |b|
    ensures (a+b)[i..j] == b[i-|a| .. j-|a|]
  {
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