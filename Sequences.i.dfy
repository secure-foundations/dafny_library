// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//include "SequencesLite.s.dfy"
//include "Option.s.dfy"
//include "../Lang/NativeTypes.s.dfy"
//include "mathematics.i.dfy"

module Sequences {
  //import opened SequencesLite
  //import opened Options
  //import opened NativeTypes
  //import Math = Mathematics

  lemma lemma_seq_equality<E>(a: seq<E>, b: seq<E>)
  // proves that sequence a and b are equal
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> a[i] == b[i]
    ensures a == b
  {
  }
  
  function last<E>(run: seq<E>) : E
  // returns the last element in the sequence
    requires |run| > 0;
  {
    run[|run|-1]
  }

  function FirstOpt<E>(run: seq<E>) : Option<E>
  // ???
  {
    if |run| == 0 then None else Some(run[0])
  }

  function drop_last<E>(run: seq<E>) : seq<E> // same as all_but_last in 'Seqs.i.dfy'
  // returns the sequence slice up to but not including the last element
    requires |run| > 0;
  {
    run[..|run|-1]
  }

  function Set<T>(run: seq<T>) : set<T> 
  // converts a sequence to a multiset
  {
    set x: T | x in multiset(run)
  }

  lemma lemma_cardinality_of_set<T>(run: seq<T>)
  /* proves that the cardinality of a subsequence is always less than or equal to that
  of the full sequence */
    ensures |Set(run)| <= |run| // length of the subset is less than the length of the set
  {
    if |run| == 0 {
    } else {
      assert Set(run) == Set(drop_last(run)) + {last(run)};
      lemma_cardinality_of_set(drop_last(run));
    }
  }
  
  lemma lemma_cardinality_of_empty_set_is_0<T>(run: seq<T>)
  // the cardinality of a subsequence of an empty sequence is also 0
    ensures |Set(run)| == 0 <==> |run| == 0
  {
    if |run| != 0 {
      assert run[0] in Set(run);
    }
  }
  
  function ISet<T>(run: seq<T>) : iset<T> 
  // initializing a possibly infinite set that is included in the original sequence...???
  {
    iset x : T | x in multiset(run)
  }
  
  predicate {:opaque} no_duplicates<T>(a: seq<T>) // function body is hidden
  // returns true if there are no duplicate values in the sequence
  {
    (forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j])
  }

  lemma {:timeLimitMultiplier 3} lemma_no_duplicates_in_disjoint_concat<T>(a: seq<T>, b: seq<T>)
  /* if sequence a and b don't have duplicates AND they are disjoint, then the
  concatenated sequence of a + b will not contain duplicates either */
    requires no_duplicates(a);
    requires no_duplicates(b);
    requires multiset(a) !! multiset(b);
    ensures no_duplicates(a + b);
  {
    reveal_no_duplicates(); // necessary because no_duplicates is :opaque
    var c := a + b;
    if |c| > 1 {
      assert forall i, j :: i != j && 0 <= i < |a| && |a| <= j < |c| ==>
        c[i] in multiset(a) && c[j] in multiset(b) && c[i] != c[j]; 
    }
  }

  lemma lemma_cardinality_of_set_no_duplicates<T>(a: seq<T>)
  /* proves that the sequence the length of the multiset version of the sequence
  is the same as the sequence, given that there are no duplicates involved */
    requires no_duplicates(a)
    ensures |Set(a)| == |a|
  {
    reveal_no_duplicates();
    if |a| == 0 {
    } else {
      lemma_cardinality_of_set_no_duplicates(drop_last(a));
      assert Set(a) == Set(drop_last(a)) + {last(a)};
    }
  }

  lemma lemma_multiset_has_no_duplicates<T>(a: seq<T>)
  // proves that there are no duplicate values in the multiset
    requires no_duplicates(a)
    ensures forall x | x in multiset(a) :: multiset(a)[x] == 1
  {
    if |a| == 0 {
    } else {
      assert a == drop_last(a) + [ last(a) ];
      assert last(a) !in drop_last(a) by {
        reveal_no_duplicates();
      }
      assert no_duplicates(drop_last(a)) by {
        reveal_no_duplicates();
      }
      lemma_multiset_has_no_duplicates(drop_last(a));
    }
  }
  
  function index_of<T>(s: seq<T>, e: T) : int
  // returns the index of a certain element in the sequence
    requires e in s;
    ensures 0 <= index_of(s,e) < |s|;
    ensures s[index_of(s,e)] == e;
  {
    var i :| 0 <= i < |s| && s[i] == e;
    i
  }

  function {:opaque} range(n: int) : seq<int>
  /* returns a sequence of n integers in which the integer is the
  same number as the index */ 
    requires n >= 0
    ensures |range(n)| == n
    ensures forall i | 0 <= i < n :: range(n)[i] == i
  {
    if n == 0 then [] else range(n-1) + [n-1]
  }
  
  function apply<E,R>(f: (E ~> R), run: seq<E>) : (result: seq<R>)
  // applies a transformation function on the sequence
    requires forall i :: 0 <= i < |run| ==> f.requires(run[i])
    ensures |result| == |run|
    ensures forall i :: 0 <= i < |run| ==> result[i] == f(run[i]);
    reads set i, o | 0 <= i < |run| && o in f.reads(run[i]) :: o
  {
    if |run| == 0 then []
    else  [f(run[0])] + apply(f, run[1..])
  }

  // TODO: can we replace Apply with this?
  function {:opaque} apply_opaque<E,R>(f: (E ~> R), run: seq<E>) : (result: seq<R>)
    requires forall i :: 0 <= i < |run| ==> f.requires(run[i])
    ensures |result| == |run|
    ensures forall i :: 0 <= i < |run| ==> result[i] == f(run[i]);
    reads set i, o | 0 <= i < |run| && o in f.reads(run[i]) :: o
  {
    apply(f, run)
  }

  function Filter<E>(f : (E ~> bool), run: seq<E>) : (result: seq<E>)
  // ???
    requires forall i :: 0 <= i < |run| ==> f.requires(run[i])
    ensures |result| <= |run|
    ensures forall i: nat :: i < |result| && f.requires(result[i]) ==> f(result[i])
    reads f.reads
  {
    if |run| == 0 then []
    else ((if f(run[0]) then [run[0]] else []) + Filter(f, run[1..]))
  }
  
  function fold_left<A,E>(f: (A, E) -> A, init: A, run: seq<E>) : A
  {
    if |run| == 0 then init
    else fold_left(f, f(init, run[0]), run[1..])
  }

  function fold_right<A,E>(f: (A, E) -> A, init: A, run: seq<E>) : A
  {
    if |run| == 0 then init
    else f(fold_right(f, init, run[1..]), run[0])
  }

  function fold_from_right<A,E>(f: (A, E) -> A, init: A, run: seq<E>) : A
  {
    if |run| == 0 then init
    else f(fold_from_right(f, init, drop_last(run)), last(run))
  }

  function {:opaque} remove<A>(s: seq<A>, pos: int) : seq<A>
  // slices out a specific position's value from the sequence and returns teh new sequence
  requires 0 <= pos < |s|
  ensures |remove(s, pos)| == |s| - 1
  ensures forall i | 0 <= i < pos :: remove(s, pos)[i] == s[i]
  ensures forall i | pos <= i < |s| - 1 :: remove(s, pos)[i] == s[i+1]
  {
    s[.. pos] + s[pos + 1 ..]
  }

  function {:opaque} remove_one_value<V>(s: seq<V>, v: V) : (s': seq<V>)
  // slices out a specific value from the sequence and returns the new sequence
    ensures no_duplicates(s) ==> no_duplicates(s') && Set(s') == Set(s) - {v}
  {
    reveal_no_duplicates();
    if v !in s then s else
    var i :| 0 <= i < |s| && s[i] == v;
    s[.. i] + s[i + 1 ..]
  }

  function {:opaque} insert<A>(s: seq<A>, a: A, pos: int) : seq<A>
  // inserts a certain value into a specified index of the sequence and returns the new sequence
  requires 0 <= pos <= |s|;
  ensures |insert(s,a,pos)| == |s| + 1;
  ensures forall i :: 0 <= i < pos ==> insert(s, a, pos)[i] == s[i];
  ensures forall i :: pos <= i < |s| ==> insert(s, a, pos)[i+1] == s[i];
  ensures insert(s, a, pos)[pos] == a;
  {
    s[..pos] + [a] + s[pos..]
  }

  method Insert<A>(s: seq<A>, a: A, pos: uint64) returns (res: seq<A>)
  // inserts a value into a specified index of the sequence and returns the new sequence
  requires 0 <= pos as int <= |s|;
  ensures res == insert(s, a, pos as int); //calls the function
  {
    return s[..pos] + [a] + s[pos..];
  }

  lemma InsertMultiset<A>(s: seq<A>, a: A, pos: int)
  // shows that the inserted element is now included in the multiset
    requires 0 <= pos <= |s|;
    ensures multiset(insert(s, a, pos)) == multiset(s) + multiset{a}
  {
    reveal_insert();
    assert s == s[..pos] + s[pos..];
  }
  
  function {:opaque} replace_1_with_2<A>(s: seq<A>, a: A, b: A, pos: int) : seq<A>
  /* inserts 2 values into the sequence at a specified position and replaces the 
  value that was previously in that position. Returns the resulting sequence */
  requires 0 <= pos < |s|;
  ensures |replace_1_with_2(s,a,b,pos)| == |s| + 1;
  ensures forall i :: 0 <= i < pos ==> replace_1_with_2(s, a, b, pos)[i] == s[i];
  ensures forall i :: pos < i < |s| ==> replace_1_with_2(s, a, b, pos)[i+1] == s[i];
  ensures replace_1_with_2(s, a, b, pos)[pos] == a;
  ensures replace_1_with_2(s, a, b, pos)[pos + 1] == b;
  {
    s[..pos] + [a, b] + s[pos+1..]
  }

  method Replace_1_with_2<A>(s: seq<A>, a: A, b: A, pos: uint64) returns (res:seq<A>)
  // replaces value at a specified index with 2 values
  requires 0 <= pos as int < |s|;
  requires pos < 0xffff_ffff_ffff_ffff
  ensures res == replace_1_with_2(s, a, b, pos as int)
  {
    return s[..pos] + [a, b] + s[pos+1..];
  }

  function {:opaque} replace_2_with_1<A>(s: seq<A>, a: A, pos: int) : seq<A>
  // replaces 2 values with one value at that position
  requires 0 <= pos < |s| - 1;
  ensures |replace_2_with_1(s,a,pos)| == |s| - 1;
  ensures forall i :: 0 <= i < pos ==> replace_2_with_1(s, a, pos)[i] == s[i];
  ensures forall i :: pos < i < |s| - 1 ==> replace_2_with_1(s, a, pos)[i] == s[i+1];
  ensures replace_2_with_1(s, a, pos)[pos] == a;
  {
    s[..pos] + [a] + s[pos+2..]
  }

  function {:opaque} concat<A>(a: seq<A>, b: seq<A>) : seq<A>
  // concatenates two sequences
  ensures |concat(a,b)| == |a| + |b|
  ensures forall i :: 0 <= i < |a| ==> a[i] == concat(a,b)[i];
  ensures forall i :: 0 <= i < |b| ==> b[i] == concat(a,b)[|a| + i];
  {
    a + b
  }

  function {:opaque} concat3<A>(a: seq<A>, b: A, c: seq<A>) : seq<A>
  // concatenates 2 sequences with one value in between 
  ensures |concat3(a,b,c)| == |a| + |c| + 1
  ensures forall i :: 0 <= i < |a| ==> a[i] == concat3(a,b,c)[i];
  ensures concat3(a,b,c)[|a|] == b;
  ensures forall i :: 0 <= i < |c| ==> c[i] == concat3(a,b,c)[|a| + 1 + i];
  {
    a + [b] + c
  }

  function {:opaque} concatSeq<A>(a: seq<seq<A>>) : seq<A>
  // turns a sequence of sequences into a single sequence and returns the result
  {
    if |a| == 0 then [] else concatSeq(drop_last(a)) + last(a)
  }

  lemma concatSeqAdditive<A>(a: seq<seq<A>>, b: seq<seq<A>>)
  // proves sequence addition
  ensures concatSeq(a + b) == concatSeq(a) + concatSeq(b)
  {
    if b == [] {
      calc {
        concatSeq(a + b);
        { assert a + b == a; }
        concatSeq(a);
        {
          reveal_concatSeq();
          assert concatSeq(b) == [];
        }
        concatSeq(a) + concatSeq(b);
      }
    } else {
      calc {
        concatSeq(a + b);
        { reveal_concatSeq(); }
        concatSeq(drop_last(a + b)) + last(a + b);
        {
          assert drop_last(a + b) == a + drop_last(b);
          assert last(a + b) == last(b);
        }
        concatSeq(a + drop_last(b)) + last(b);
        {
          concatSeqAdditive(a, drop_last(b));
        }
        concatSeq(a) + concatSeq(drop_last(b)) + last(b);
        { reveal_concatSeq(); }
        concatSeq(a) + concatSeq(b);
      }
    }
  }

  lemma lemma_concatSeqLen_ge_elemLen<A>(a: seq<seq<A>>, i: int)
  /* the concatenated sequence's length is greater than or equal to 
  each individual inner sequence's length */
  requires 0 <= i < |a|
  ensures |concatSeq(a)| >= |a[i]|
  {
    reveal_concatSeq();
    if i < |a| - 1 {
      lemma_concatSeqLen_ge_elemLen(a[..|a|-1], i);
    }
  }

  lemma lemma_concatSeqLen_le_mul<A>(a: seq<seq<A>>, t: int)
  /* the length of concatenating sequence in a sequence together will be no longer 
  than the length of the original sequence of sequences multiplied by the length of 
  the longest sequence */
  requires forall i | 0 <= i < |a| :: |a[i]| <= t
  ensures |concatSeq(a)| <= |a| * t
  {
    reveal_concatSeq();
    if |a| == 0 {
    } else {
      lemma_concatSeqLen_le_mul(a[..|a|-1], t);
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

  function {:opaque} SeqIndexIterate<A>(run: seq<A>, needle: A, i: int) : (res : Option<int>)
  requires 0 <= i <= |run|
  ensures res.Some? ==> 0 <= res.value < |run| && run[res.value] == needle
  ensures res.None? ==> forall j | i <= j < |run| :: run[j] != needle
  decreases |run| - i
  {
    if i == |run| then None
    else if run[i] == needle then Some(i)
    else SeqIndexIterate(run, needle, i+1)
  }

  function {:opaque} SeqIndex<A>(run: seq<A>, needle: A) : (res : Option<int>)
  ensures res.Some? ==> 0 <= res.value < |run| && run[res.value] == needle
  ensures res.None? ==> forall i | 0 <= i < |run| :: run[i] != needle
  {
    SeqIndexIterate(run, needle, 0)
  }

  function {:opaque} SeqOfLength<V>(length: nat, v: V) : (res: seq<V>)
  ensures |res| == length
  ensures forall i: nat | i < |res| :: res[i] == v
  {
    if length == 0 then
      []
    else
      [v] + SeqOfLength(length - 1, v)
  }

  // This is a workaround since Dafny right now doesn't support
  // s[i := t] when i is a native type integer.
  function method {:opaque} SeqIndexUpdate<T>(s: seq<T>, i: uint64, t: T) : seq<T>
  requires i as int + 1 < 0x1_0000_0000_0000_0000
  requires 0 <= i as int < |s|
  ensures SeqIndexUpdate(s, i, t) == s[i as int := t]
  {
    s[..i] + [t] + s[i+1..]
  }

  function {:opaque} Zip<A,B>(a: seq<A>, b: seq<B>) : seq<(A,B)>
  /* takes two sequences, a and b, and combines then to form one sequence in which
  each position contains an ordered pair from a and b */

    requires |a| == |b|
    ensures |Zip(a, b)| == |a|
    ensures forall i :: 0 <= i < |Zip(a, b)| ==> Zip(a, b)[i] == (a[i], b[i])
  {
    if |a| == 0 then []
    else Zip(drop_last(a), drop_last(b)) + [(last(a), last(b))]
  }

  function {:opaque} Unzip<A,B>(z: seq<(A, B)>) : (seq<A>, seq<B>)
  // unzips a sequence that contains ordered pairs into 2 seperate sequences
    ensures |Unzip(z).0| == |Unzip(z).1| == |z|
    ensures forall i :: 0 <= i < |z| ==> (Unzip(z).0[i], Unzip(z).1[i]) == z[i]
  {
    if |z| == 0 then ([], [])
    else
      var (a, b) := Unzip(drop_last(z));
      (a + [last(z).0], b + [last(z).1])
  }

  lemma ZipOfUnzip<A,B>(s: seq<(A,B)>)
  // if a sequence is unzipped and then zipped, it forms the original sequence
    ensures Zip(Unzip(s).0, Unzip(s).1) == s
  {
  }
  
  lemma UnzipOfZip<A,B>(sa: seq<A>, sb: seq<B>)
  // if a zipped sequence is unzipped, this results in two seperate sequences
    requires |sa| == |sb|
    ensures Unzip(Zip(sa, sb)).0 == sa
    ensures Unzip(Zip(sa, sb)).1 == sb
  {
  }
  
  function {:opaque} FlattenShape<A>(seqs: seq<seq<A>>) : (shape: seq<nat>)
  /* receives a sequence of sequences. Returns a sequence in which the ith element corresponds 
  to the length of the sequence at the ith position*/
    ensures |shape| == |seqs|
    ensures forall i :: 0 <= i < |shape| ==> shape[i] == |seqs[i]|
  {
    if |seqs| == 0 then []
    else FlattenShape(drop_last(seqs)) + [|last(seqs)|]
  }

  lemma FlattenShapeAdditive<A>(seqs1: seq<seq<A>>, seqs2: seq<seq<A>>)
  /* concatenating two sequences and then flattening their shape retults in the same
  result as flattenning each sequence first and then concatenating */
    ensures FlattenShape(seqs1 + seqs2) == FlattenShape(seqs1) + FlattenShape(seqs2)
  {
  }
  
  function {:opaque} FlattenLength(shape: seq<nat>) : nat
  /* returns a number that results from adding up each all 
  of the elements in the sequence's shape */
    ensures |shape| == 0 ==> FlattenLength(shape) == 0
  {
    if |shape| == 0 then 0
    else FlattenLength(drop_last(shape)) + last(shape)
  }


  lemma {:induction true} FlattenLengthAdditive(shape1: seq<nat>, shape2: seq<nat>)
  /* concatenating two "shape" sequences together and then flattening their length is 
  the same as flattening each shape's length and then adding the resulting numbers */
    ensures FlattenLength(shape1 + shape2) == FlattenLength(shape1) + FlattenLength(shape2)
  {
    if |shape2| == 0 {
      assert shape1 + shape2 == shape1;
    } else {
      reveal_FlattenLength();
      assert shape1 + shape2 == (shape1 + drop_last(shape2)) + [last(shape2)];
    }
  }
  
  lemma FlattenLengthSubSeq(shape: seq<nat>, from: nat, to: nat)
  /* the flattened length of any subsequence of the shape is less than 
  the flattened length of the whole shape */
    requires from <= to <= |shape|
    ensures FlattenLength(shape[from..to]) <= FlattenLength(shape)
  {
    assert shape == shape[..from] + shape[from..to] + shape[to..];
    FlattenLengthAdditive(shape[..from] + shape[from..to], shape[to..]);
    FlattenLengthAdditive(shape[..from], shape[from..to]);
  }

  function {:opaque} Flatten<A>(seqs: seq<seq<A>>) : seq<A>
  /* the flattened sequence's length will be equal to flattenening the shape 
  and then flattening the length; returns a sequence that combines all sequences of 
  the sequence */
    ensures |Flatten(seqs)| == FlattenLength(FlattenShape(seqs))
    ensures |seqs| == 0 ==> |Flatten(seqs)| == 0
  {
    reveal_FlattenShape();
    reveal_FlattenLength();
    if |seqs| == 0 then []
    else Flatten(drop_last(seqs)) + last(seqs)
  }

  lemma FlattenSingleton<A>(s: seq<A>)
  // flattening a singleton of sequences will simply result in the original sequence
    ensures Flatten([ s ]) == s
  {
    reveal_Flatten();
  }
  
  lemma FlattenAdditive<A>(seqs1: seq<seq<A>>, seqs2: seq<seq<A>>)
  /* concatenating two sequences and then flattening them has the same result 
  as flattening each sequence seperately and then concatenating afterwards */
    ensures Flatten(seqs1 + seqs2) == Flatten(seqs1) + Flatten(seqs2)
    decreases |seqs2|
  {
    if |seqs2| == 0 {
      assert seqs1 + seqs2 == seqs1;
    } else if |seqs2| == 1 {
      reveal_Flatten();
    } else {
      calc {
        Flatten(seqs1 + seqs2);
        { assert seqs1 + seqs2 == seqs1 + drop_last(seqs2) + [ last(seqs2) ]; }
        Flatten(seqs1 + drop_last(seqs2) + [ last(seqs2) ]);
        { FlattenAdditive(seqs1 + drop_last(seqs2), [ last(seqs2) ]); }
        Flatten(seqs1 + drop_last(seqs2)) + Flatten([ last(seqs2) ]);
        { FlattenAdditive(seqs1, drop_last(seqs2)); }
        Flatten(seqs1) + Flatten(drop_last(seqs2)) + Flatten([ last(seqs2) ]);
        { FlattenAdditive(drop_last(seqs2), [ last(seqs2) ]); }
        Flatten(seqs1) + Flatten(drop_last(seqs2) + [ last(seqs2) ]);
        { assert seqs2 == drop_last(seqs2) + [ last(seqs2) ]; }
        Flatten(seqs1) + Flatten(seqs2);
      }
    }
  }
  
  function FlattenIndex(shape: seq<nat>, i: nat, j: nat) : nat
  /* returns the summation of the flattened length of a subsequence
  plus ___j???  */
    requires i < |shape|
    requires j < shape[i]
  {
    FlattenLength(shape[..i]) + j
  }

  function UnflattenIndex(shape: seq<nat>, i: nat) : (nat, nat)
  /* ??? */
    requires i < FlattenLength(shape)
  {
    reveal_FlattenLength();
    if i < FlattenLength(drop_last(shape)) then UnflattenIndex(drop_last(shape), i)
    else (|shape|-1, i - FlattenLength(drop_last(shape)))
  }

  lemma FlattenIndexInBounds(shape: seq<nat>, i: nat, j: nat)
    requires i < |shape|
    requires j < shape[i]
    ensures FlattenIndex(shape, i, j) < FlattenLength(shape)
  {
    reveal_FlattenLength();
    if i == |shape|-1 {
    } else {
      FlattenIndexInBounds(drop_last(shape), i, j);
      assert drop_last(shape)[..i] == shape[..i];
    }
  }
  
  lemma {:induction true} UnflattenIndexInBounds(shape: seq<nat>, i: nat)
    requires i < FlattenLength(shape)
    ensures UnflattenIndex(shape, i).0 < |shape|
    ensures UnflattenIndex(shape, i).1 < shape[UnflattenIndex(shape, i).0]
  {
    var shapeidx := UnflattenIndex(shape, i).0;
  }

  lemma {:induction true} FlattenUnflattenIdentity(shape: seq<nat>, i: nat)
    requires i < FlattenLength(shape)
    ensures UnflattenIndex(shape, i).0 < |shape|
    ensures UnflattenIndex(shape, i).1 < shape[UnflattenIndex(shape, i).0]
    ensures i == FlattenIndex(shape, UnflattenIndex(shape, i).0, UnflattenIndex(shape, i).1)
  {
    UnflattenIndexInBounds(shape, i);
    var (shapeidx, shapeoff) := UnflattenIndex(shape, i);
    if shapeidx == |shape|-1 {
    } else {
      FlattenUnflattenIdentity(drop_last(shape), i);
      assert drop_last(shape)[..shapeidx] == shape[..shapeidx];
    }
  }
  
  lemma UnflattenFlattenIdentity(shape: seq<nat>, i: nat, j: nat)
    requires i < |shape|
    requires j < shape[i]
    ensures FlattenIndex(shape, i, j) < FlattenLength(shape)
    ensures (i, j) == UnflattenIndex(shape, FlattenIndex(shape, i, j))
  {
    FlattenIndexInBounds(shape, i, j);
    if i == |shape| - 1 {
    } else {
      UnflattenFlattenIdentity(drop_last(shape), i, j);
      assert drop_last(shape)[..i] == shape[..i];
    }
  }
  
  lemma {:induction true} UnflattenIndexOrdering(shape: seq<nat>, i: nat, j: nat)
    requires i < j < FlattenLength(shape)
    ensures UnflattenIndex(shape, i).0 <= UnflattenIndex(shape, j).0
    ensures UnflattenIndex(shape, i).0 == UnflattenIndex(shape, j).0 ==> UnflattenIndex(shape, i).1 < UnflattenIndex(shape, j).1
  {
    FlattenUnflattenIdentity(shape, i);
  }

  lemma FlattenIndexIsCorrect<A>(seqs: seq<seq<A>>, i: nat, j: nat)
    requires i < |seqs|
    requires j < |seqs[i]|
    ensures FlattenIndex(FlattenShape(seqs), i, j) < |Flatten(seqs)|
    ensures Flatten(seqs)[FlattenIndex(FlattenShape(seqs), i, j)] == seqs[i][j]
  {
    reveal_Flatten();
    FlattenIndexInBounds(FlattenShape(seqs), i, j);
    if i == |seqs|-1 {
    } else {
      FlattenIndexIsCorrect(drop_last(seqs), i, j);
      assert drop_last(FlattenShape(seqs))[..i] == FlattenShape(seqs)[..i];
    }
  }

  lemma {:induction true} {:timeLimitMultiplier 3} UnflattenIndexIsCorrect<A>(seqs: seq<seq<A>>, i: nat)
    requires i < FlattenLength(FlattenShape(seqs))
    ensures UnflattenIndex(FlattenShape(seqs), i).0 < |seqs|
    ensures UnflattenIndex(FlattenShape(seqs), i).1 < |seqs[UnflattenIndex(FlattenShape(seqs), i).0]|
    ensures Flatten(seqs)[i] == seqs[UnflattenIndex(FlattenShape(seqs), i).0][UnflattenIndex(FlattenShape(seqs), i).1]
  {
    var shape := FlattenShape(seqs);
    UnflattenIndexInBounds(shape, i);
    reveal_Flatten();
  }

  lemma CardinalityOfSetsOfSequenceIndices<T>(q:seq<T>, t:set<int>)
  /* proves that the cardinality of the set is the same as the cardinality 
  of the set, given that the set is the same size as the sequence*/
    requires t == set i | 0 <= i < |q|
    ensures |t| == |q|
  {
    if |q|>0 {
      var sq := q[..|q|-1];
      var st := set i | 0 <= i < |sq|;
      calc {
        |q|;
        |sq| + 1;
          { CardinalityOfSetsOfSequenceIndices(sq, st); }
        |st| + 1;
          { assert t == st + {|sq|}; }
        |t|;
      }
    }
  }

  function {:opaque} seqMax(s: seq<int>): int
  // returns the maximum integer value in the sequence
    requires 0 < |s|
    ensures forall k :: k in s ==> seqMax(s) >= k
    ensures seqMax(s) in s
  {
    assert s == drop_last(s) + [last(s)];
    if |s| == 1
    then s[0]
    else Math.max(seqMax(drop_last(s)), last(s))
  }

  lemma SeqMaxCorrespondence(s1:seq<int>, s2:seq<int>, wit: seq<nat>)
  /* ??? */
    requires 0 < |s1|
    requires 0 < |s2|
    requires |wit| == |s2|
    requires forall j:nat :: j < |wit| ==> wit[j] < |s1|
    requires forall i :: 0 <= i < |s2| ==> s2[i] <= s1[wit[i]]
    ensures seqMax(s2) <= seqMax(s1)
  {
    if seqMax(s2) > seqMax(s1) {
      var idx :| 0 <= idx < |s2| && s2[idx] == seqMax(s2);
      assert s1[wit[idx]] in s1;  // trigger
      assert false;
    }
  }

  lemma SubseqMax(s: seq<int>, from: nat, to: nat)
  /* the maximum element in any subsequence will not be 
  greater than the maximum element in the full sequence */
    requires 0 <= from < to <= |s|
    ensures seqMax(s[from .. to]) <= seqMax(s)
  {
    var subseq := s[from .. to];
    SeqMaxCorrespondence(s, subseq, seq(|subseq|, i requires 0<=i<|subseq| => i + from));
  }

  lemma lemma_seq_suffix_slice<T>(s: seq<T>, i: int, j: int, k: int)
  /* proves that if a sequence is sliced from i until the end and then sliced a seconds time, 
  the resulting sequence is the same as the original sequence shifted by i */ 
  requires 0 <= i <= |s|
  requires 0 <= j <= k <= |s| - i
  ensures s[i..][j..k] == s[i+j..i+k];
  {
  }

  lemma lemma_seq_slice_suffix<T>(s: seq<T>, i: int, j: int, k: int)
  /* if a sequence is sliced in a certain interval and then sliced again
  from k until the end, then this is the same as slicing the initial
  sequence from the first + the second slice */
  requires 0 <= i <= j <= |s|
  requires 0 <= k <= j - i
  ensures s[i..j][k..] == s[i+k..j];
  {
  }

  lemma lemma_array_suffix_slice<T>(ar: array<T>, i: int, j: int, k: int)
  
  /* proves that if an array is sliced from i until the end and then sliced a seconds time, 
  the resulting array is the same as the original array shifted by i */ 
  requires 0 <= i <= ar.Length
  requires 0 <= j <= k <= ar.Length - i
  ensures ar[i..][j..k] == ar[i+j..i+k];
  {
  }

  lemma lemma_seq_extensionality<T>(s: seq<T>, t: seq<T>)
  /* if the length two sequences are equal and each element is equal, then the two
  sequences are equal */
  requires |s| == |t|
  requires forall i | 0 <= i < |s| :: s[i] == t[i]
  ensures s == t
  {
  }

  lemma lemma_seq_slice_slice<T>(s: seq<T>, i: int, j: int, k: int, l: int)
  /* shows the sequence equivalence of slices of slices */
  requires 0 <= i <= j <= |s|
  requires 0 <= k <= l <= j - i
  ensures s[i..j][k..l] == s[i+k..i+l];
  {
    lemma_seq_extensionality(s[i..j][k..l], s[i+k..i+l]);
  }

  lemma lemma_array_slice_slice<T>(ar: array<T>, i: int, j: int, k: int, l: int)
  /* taking a slice of range i to j and then taking another slice that is within 
  the first range is equivalent to simply slicing the original array */
  requires 0 <= i <= j <= ar.Length
  requires 0 <= k <= l <= j - i
  ensures ar[i..j][k..l] == ar[i+k..i+l];
  {
    lemma_seq_slice_slice(ar[..], i, j, k, l);
  }

  lemma lemma_seq_extensionality_slice<T>(s: seq<T>, t: seq<T>, a: int, b: int)
  /* if two sequences have the same elements in a certain interval
  the subsequences over that interval are equal */
  requires 0 <= a <= b <= |s|
  requires b <= |t|
  requires forall i | a <= i < b :: s[i] == t[i]
  ensures s[a..b] == t[a..b]
  {
  }

  function {:opaque} fill<T>(n: int, t: T) : (res: seq<T>)
  // fills the sequence with n identical elements
  requires n >= 0
  ensures |res| == n
  ensures forall i | 0 <= i < n :: res[i] == t
  {
    if n == 0 then [] else fill(n-1, t) + [t]
  }

  lemma sum_slice_second<T>(a: seq<T>, b: seq<T>, i: int, j: int)
  /* concatenating two sequences and then taking a slice starting from an index 
  that is greater than the first sequence is the same as taking a slice from the 
  second sequence */
  requires |a| <= i <= j <= |a| + |b|
  ensures (a+b)[i..j] == b[i-|a| .. j-|a|]
  {
  }
}
