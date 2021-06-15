// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module Mathematics {

	function method min(a: int, b: int) : int
	{
		if a < b
			then a
		else
			b
	}

	function method max(a: int, b: int) : int
	{
		if a < b
			then b
		else
			a
	}

  lemma PosMulPosIsPos(x: int, y: int)
    requires 0 < x
    requires 0 < y
    ensures 0 < x * y
  {
  }
  
  lemma DivCeilLT(x: int, d: int)
    requires 1 < d
    requires 1 < x
    ensures (x + d - 1) / d < x
  {
    PosMulPosIsPos(d-1, x-1);
    calc <= {
      0; <
      (d-1) * (x-1);
    }
  }

  lemma PosMulPreservesOrder(x: nat, y: nat, m: nat)
    requires x <= y
    ensures x * m <= y * m
  {
  }
}
module {:extern} Options {
  datatype Option<V> = None | Some(value:V)

  function MapOption<V0, V1>(opt: Option<V0>, f: V0 ~> V1) : (result: Option<V1>)
  requires opt.Some? ==> f.requires(opt.value)
  ensures opt.Some? <==> result.Some?
  ensures result.Some? ==> result.value == f(opt.value)
  reads if opt.Some? then f.reads(opt.value) else {}
  {
    match opt {
      case Some(v) => Some(f(v))
      case None => None
    }
  }

  function FlatMapOption<V0, V1>(opt: Option<V0>, f: V0 ~> Option<V1>) : (result: Option<V1>)
  requires opt.Some? ==> f.requires(opt.value)
  ensures opt.Some? && f(opt.value).Some? ==> result.Some?
  ensures opt.Some? && f(opt.value).Some? ==> result.value == f(opt.value).value
  reads if opt.Some? then f.reads(opt.value) else {}
  {
    match opt {
      case Some(v) => f(v)
      case None => None
    }
  }
} // module
module Sequences {
  import opened Options
  import Math = Mathematics

  lemma lemma_seq_slice_concatenation_is_original<T>(intseq:seq<T>, j:int)
  // from seqs_simple.i
  /* a sequence that is sliced at the jth element concatenated with that same
  sequence sliced from the jth element is equal to the original, unsliced sequence */
  requires 0<=j<|intseq|;
  ensures intseq[..j] + intseq[j..] == intseq;
  {
  }

  lemma lemma_seq_equality<E>(a: seq<E>, b: seq<E>)
  // proves that sequence a and b are equal
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> a[i] == b[i]
    ensures a == b
  {
  }

  lemma lemma_identical_seq_singletons_have_itentical_elements<T>(x:T, y:T)
  // from Seqs.i
  // two identical sequences of length 1 have the same elements
  requires [x] == [y]
  ensures  x == y
  {
    calc == {
      x;
      [x][0];
      [y][0];
      y;
    }
  }

  lemma lemma_sequence_reduction<T>(s:seq<T>, b:nat)
  // from seqs_simple.i -- not sure where to place
  /* explains sequence reduction */
    requires 0<b<|s|;
    ensures s[0..b][0..b-1] == s[0..b-1];
  {
    var t := s[0..b];
    forall (i | 0<=i<b-1)
        ensures s[0..b][0..b-1][i] == s[0..b-1][i];
    {
    }
  }

  lemma lemma_seq_slice_start<T>(intseq:seq<T>, j:int)
  // from seqs_simple.i
  /* a sequence sliced from the first element to the jth element is
  the same as that sequence sliced until the jth element*/
    requires 0<=j<|intseq|;
    ensures intseq[0..j]==intseq[..j];
  {
  }

  lemma lemma_seq_slice_full_length<T>(intseq:seq<T>)
  // from seqs_simple.i
  /* a sequence is the same as that sequence sliced until the end 
  of that sequence's length */
    ensures intseq==intseq[..|intseq|];
  {
  }

  function method last<E>(run: seq<E>) : E
  // returns the last element in the sequence
    requires |run| > 0;
  {
    run[|run|-1]
  }
  
  function method FirstOpt<E>(run: seq<E>) : Option<E>
  {
    if |run| == 0 then None else Some(run[0])
  }

  function method drop_last<E>(run: seq<E>) : seq<E> // same as all_but_last in 'Seqs.i.dfy'
  // returns the sequence slice up to but not including the last element
    requires |run| > 0;
  {
    run[..|run|-1]
  }

  function method all_but_last<T>(s:seq<T>):seq<T> 
  // from Seqs.i; same idea as drop_last
  /* returns a slice of the sequence that includes all elements of the 
  original sequence except for the last element */
  requires |s| > 0
  ensures  |all_but_last(s)| == |s| - 1
  {
    s[..|s|-1]
  }

  function method Set<T>(run: seq<T>) : set<T> 
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
  
  function method ISet<T>(run: seq<T>) : iset<T> 
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

  predicate item_at_position_in_sequence<T>(s:seq<T>, v:T, idx:int)
  // from Seqs.i
  // defines if the element is at a specific position in the sequence
  {
    0 <= idx < |s| && s[idx] == v
  }

  lemma lemma_item_at_position_in_sequence<T>(s:seq<T>, v:T)
  // from Seqs.i
  // if there is an element at a certain index, then that index exists
    requires v in s
    ensures exists idx :: item_at_position_in_sequence(s, v, idx)
  { 
    var idx :| 0 <= idx < |s| && s[idx] == v;
    assert item_at_position_in_sequence(s, v, idx);
  }

  function method find_index_in_sequence<T>(s:seq<T>, v:T):int
  // from Seqs.i; similar to index_of
  /* finds the index of a certain value in the sequence, if it exists. Returns
  the index, or -1 if the value is not included in the sequence */
    ensures var idx := find_index_in_sequence(s, v);
            if idx >= 0 then
              idx < |s| && s[idx] == v
            else
              v !in s
  {
    if v in s then
      lemma_item_at_position_in_sequence(s, v);
      var idx :| item_at_position_in_sequence(s, v, idx);
      idx
    else
      -1
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

  // another "range" function in Seqs_from_Vale_repository.i.dfy
  function method {:opaque} range(n: int) : seq<int>
  /* returns a sequence of n integers in which the integer is the
  same number as the index */ 
    requires n >= 0
    ensures |range(n)| == n
    ensures forall i | 0 <= i < n :: range(n)[i] == i
  {
    if n == 0 then [] else range(n-1) + [n-1]
  }
  
  
  function method apply<E,R>(f: (E ~> R), run: seq<E>) : (result: seq<R>)
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
  function method {:opaque} apply_opaque<E,R>(f: (E ~> R), run: seq<E>) : (result: seq<R>)
    requires forall i :: 0 <= i < |run| ==> f.requires(run[i])
    ensures |result| == |run|
    ensures forall i :: 0 <= i < |run| ==> result[i] == f(run[i]);
    reads set i, o | 0 <= i < |run| && o in f.reads(run[i]) :: o
  {
    apply(f, run)
  }

  function method filter<E>(f : (E ~> bool), run: seq<E>) : (result: seq<E>)
  // uses a selection function to select elements from the sequence
    requires forall i :: 0 <= i < |run| ==> f.requires(run[i])
    ensures |result| <= |run|
    ensures forall i: nat :: i < |result| && f.requires(result[i]) ==> f(result[i])
    reads f.reads
  {
    if |run| == 0 then []
    else ((if f(run[0]) then [run[0]] else []) + filter(f, run[1..]))
  }
  
  function method fold_left<A,E>(f: (A, E) -> A, init: A, run: seq<E>) : A
  {
    if |run| == 0 then init
    else fold_left(f, f(init, run[0]), run[1..])
  }

  function method fold_right<A,E>(f: (A, E) -> A, init: A, run: seq<E>) : A
  {
    if |run| == 0 then init
    else f(fold_right(f, init, run[1..]), run[0])
  }

  function method fold_from_right<A,E>(f: (A, E) -> A, init: A, run: seq<E>) : A
  {
    if |run| == 0 then init
    else f(fold_from_right(f, init, drop_last(run)), last(run))
  }

  function method {:opaque} remove<A>(s: seq<A>, pos: int) : seq<A>
  // slices out a specific position's value from the sequence and returns the new sequence
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

  function method {:opaque} insert<A>(s: seq<A>, a: A, pos: int) : seq<A>
  // inserts a certain value into a specified index of the sequence and returns the new sequence
  requires 0 <= pos <= |s|;
  ensures |insert(s,a,pos)| == |s| + 1;
  ensures forall i :: 0 <= i < pos ==> insert(s, a, pos)[i] == s[i];
  ensures forall i :: pos <= i < |s| ==> insert(s, a, pos)[i+1] == s[i];
  ensures insert(s, a, pos)[pos] == a;
  {
    s[..pos] + [a] + s[pos..]
  }

  method Insert<A>(s: seq<A>, a: A, pos: int) returns (res: seq<A>)
  // inserts a value into a specified index of the sequence and returns the new sequence
  requires 0 <= pos as int <= |s|;
  ensures res == insert(s, a, pos as int); //calls the function
  {
    return s[..pos] + [a] + s[pos..];
  }

  lemma lemma_insert_multiset<A>(s: seq<A>, a: A, pos: int)
  // shows that the inserted element is now included in the multiset
    requires 0 <= pos <= |s|;
    ensures multiset(insert(s, a, pos)) == multiset(s) + multiset{a}
  {
    reveal_insert();
    assert s == s[..pos] + s[pos..];
  }
  
  function method {:opaque} replace_1_with_2<A>(s: seq<A>, a: A, b: A, pos: int) : seq<A>
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

  method Replace_1_with_2<A>(s: seq<A>, a: A, b: A, pos: int) returns (res:seq<A>)
  // replaces value at a specified index with 2 values
  requires 0 <= pos as int < |s|;
  requires pos < 0xffff_ffff_ffff_ffff
  ensures res == replace_1_with_2(s, a, b, pos as int)
  {
    return s[..pos] + [a, b] + s[pos+1..];
  }

  function method {:opaque} replace_2_with_1<A>(s: seq<A>, a: A, pos: int) : seq<A>
  // replaces 2 values with one value at that position
  requires 0 <= pos < |s| - 1;
  ensures |replace_2_with_1(s,a,pos)| == |s| - 1;
  ensures forall i :: 0 <= i < pos ==> replace_2_with_1(s, a, pos)[i] == s[i];
  ensures forall i :: pos < i < |s| - 1 ==> replace_2_with_1(s, a, pos)[i] == s[i+1];
  ensures replace_2_with_1(s, a, pos)[pos] == a;
  {
    s[..pos] + [a] + s[pos+2..]
  }

  function method {:opaque} concat<A>(a: seq<A>, b: seq<A>) : seq<A>
  // concatenates two sequences
  ensures |concat(a,b)| == |a| + |b|
  ensures forall i :: 0 <= i < |a| ==> a[i] == concat(a,b)[i];
  ensures forall i :: 0 <= i < |b| ==> b[i] == concat(a,b)[|a| + i];
  {
    a + b
  }

  function method {:opaque} concat_3<A>(a: seq<A>, b: A, c: seq<A>) : seq<A>
  // concatenates 2 sequences with one value in between 
  // should I make b into a sequence, and the user can choose for it be be used as a singleton???
  ensures |concat_3(a,b,c)| == |a| + |c| + 1
  ensures forall i :: 0 <= i < |a| ==> a[i] == concat_3(a,b,c)[i];
  ensures concat_3(a,b,c)[|a|] == b;
  ensures forall i :: 0 <= i < |c| ==> c[i] == concat_3(a,b,c)[|a| + 1 + i];
  {
    a + [b] + c
  }

  lemma lemma_subseq_concatenation<T>(s: seq<T>, left: int, middle: int, right: int)
  // from seqs_simple.i
  /* a subsequence is the same as concatenating two subsequences: one from the leftmost
  element until some element in the middle, and one from the middle element to the 
  rightmost element */
  requires 0 <= left <= middle <= right <= |s|;
  ensures s[left..right] == s[left..middle] + s[middle..right];
  {
  }

  function method seq_concat<T>(seqs:seq<seq<T>>) : seq<T>
  // from Seqs.i; similar to concat_seq
  /* concatenates a sequence of sequences into a single sequence. 
  Works by adding elements in order from first to last */
  decreases |seqs|
  {
    if |seqs| == 0 then []
    else seqs[0] + seq_concat(seqs[1..])
  }

  function method {:opaque} concat_seq<A>(a: seq<seq<A>>) : seq<A>
  // turns a sequence of sequences into a single sequence and returns the result
  // was already a function method
  {
    if |a| == 0 then [] else concat_seq(drop_last(a)) + last(a)
  }

  lemma lemma_seq_addition_is_associative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
  // from Seqs.i
  // explains associative property of sequences in addition
  ensures a+(b+c) == (a+b)+c;
  {
  }

  lemma lemma_seq_concatenation_associative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
  // from seqs_simple.i; similar to lemma_seq_addition_is_associative and lemma_seq_concat_adds
  /* explains the associative nature of adding sequences*/
      ensures (a+b)+c == a+(b+c);
  {
  }

  lemma lemma_seq_concat_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
  // from Seqs.i; similar to lemma_concat_seqs_addition
  /* concatenating two sequences of sequences is equivalent to concatenating
  each sequence of sequences seperately, and then concatenating the two resulting 
  sequences together */
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

  lemma lemma_concat_seq_addition<A>(a: seq<seq<A>>, b: seq<seq<A>>)
  // proves sequence addition
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

  function method seq_concat_reverse<T>(seqs:seq<seq<T>>) : seq<T>
  // from Seqs.i
  /* concatenates the sequence of sequences into a single sequence. 
  works by adding elements from last to first */
  decreases |seqs|
  {
    if |seqs| == 0 then []
    else seq_concat_reverse(all_but_last(seqs)) + last(seqs)
  }

  lemma lemma_seq_concat_reverse_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
  // from Seqs.i
  /* concatenating two reversed sequences of sequences is the same as reversing two 
  sequences of sequences and then adding the two resulting sequences together */
  ensures seq_concat_reverse(A + B) == seq_concat_reverse(A) + seq_concat_reverse(B)
  {
    if |B| == 0 {
      assert seq_concat_reverse(B) == [];
      assert A+B == A;
    } else {
      calc == {
        seq_concat_reverse(A + B);
          { assert last(A + B) == last(B);  assert all_but_last(A + B) == A + all_but_last(B); }
        seq_concat_reverse(A + all_but_last(B)) + last(B);
        seq_concat_reverse(A) + seq_concat_reverse(all_but_last(B)) + last(B);
        seq_concat_reverse(A) + seq_concat_reverse(B);
      }
    }
  }

  lemma lemma_seq_concat_and_seq_concat_reverse_are_equivalent<T>(seqs:seq<seq<T>>)
  // from Seqs.i
  /* both methods of concatenating sequence (starting from front v. starting from back)
  result in the same sequence */
    ensures seq_concat(seqs) == seq_concat_reverse(seqs)
  {
    if |seqs| == 0 {
    } else {
      calc == {
        seq_concat_reverse(seqs);
        seq_concat_reverse(all_but_last(seqs)) + last(seqs);
          { lemma_seq_concat_and_seq_concat_reverse_are_equivalent(all_but_last(seqs)); }
        seq_concat(all_but_last(seqs)) + last(seqs);
        seq_concat(all_but_last(seqs)) + seq_concat([last(seqs)]);
          { lemma_seq_concat_adds(all_but_last(seqs), [last(seqs)]); 
        assert seqs == all_but_last(seqs) + [last(seqs)]; }
        seq_concat(seqs);
      }
    }
  }

  lemma lemma_concat_seq_length_ge_single_element_length<A>(a: seq<seq<A>>, i: int)
  /* the concatenated sequence's length is greater than or equal to 
  each individual inner sequence's length */
  requires 0 <= i < |a|
  ensures |concat_seq(a)| >= |a[i]|
  {
    reveal_concat_seq();
    if i < |a| - 1 {
      lemma_concat_seq_length_ge_single_element_length(a[..|a|-1], i);
    }
  }

  lemma lemma_concat_seq_length_le_mul<A>(a: seq<seq<A>>, t: int)
  /* the length of concatenating sequence in a sequence together will be no longer 
  than the length of the original sequence of sequences multiplied by the length of 
  the longest sequence */
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
  
  function method {:opaque} SeqIndexIterate<A(==)>(run: seq<A>, needle: A, i: int) : (res : Option<int>)
  requires 0 <= i <= |run|
  ensures res.Some? ==> 0 <= res.value < |run| && run[res.value] == needle
  ensures res.None? ==> forall j | i <= j < |run| :: run[j] != needle
  decreases |run| - i
  {
    if i == |run| then None
    else if run[i] == needle then Some(i)
    else SeqIndexIterate(run, needle, i+1)
  }

  // function method {:opaque} SeqIndex<A>(run: seq<A>, needle: A) : (res : Option<int>)
  // ensures res.Some? ==> 0 <= res.value < |run| && run[res.value] == needle
  // ensures res.None? ==> forall i | 0 <= i < |run| :: run[i] != needle
  // {
  //   SeqIndexIterate(run, needle, 0)
  // } 
  
  function method {:opaque} SeqOfLength<V>(length: nat, v: V) : (res: seq<V>)
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
  //already a function method
  function method {:opaque} SeqIndexUpdate<T>(s: seq<T>, i: int, t: T) : seq<T>
  requires i as int + 1 < 0x1_0000_0000_0000_0000
  requires 0 <= i as int < |s|
  ensures SeqIndexUpdate(s, i, t) == s[i as int := t]
  {
    s[..i] + [t] + s[i+1..]
  }

  function method {:opaque} zip<A,B>(a: seq<A>, b: seq<B>) : seq<(A,B)>
  /* takes two sequences, a and b, and combines then to form one sequence in which
  each position contains an ordered pair from a and b */

    requires |a| == |b|
    ensures |zip(a, b)| == |a|
    ensures forall i :: 0 <= i < |zip(a, b)| ==> zip(a, b)[i] == (a[i], b[i])
  {
    if |a| == 0 then []
    else zip(drop_last(a), drop_last(b)) + [(last(a), last(b))]
  }

  function method {:opaque} unzip<A,B>(z: seq<(A, B)>) : (seq<A>, seq<B>)
  // unzips a sequence that contains ordered pairs into 2 seperate sequences
    ensures |unzip(z).0| == |unzip(z).1| == |z|
    ensures forall i :: 0 <= i < |z| ==> (unzip(z).0[i], unzip(z).1[i]) == z[i]
  {
    if |z| == 0 then ([], [])
    else
      var (a, b) := unzip(drop_last(z));
      (a + [last(z).0], b + [last(z).1])
  }

  lemma lemma_zip_of_unzip<A,B>(s: seq<(A,B)>)
  // if a sequence is unzipped and then zipped, it forms the original sequence
    ensures zip(unzip(s).0, unzip(s).1) == s
  {
  }
  
  lemma lemma_unzip_of_zip<A,B>(sa: seq<A>, sb: seq<B>)
  // if a zipped sequence is unzipped, this results in two seperate sequences
    requires |sa| == |sb|
    ensures unzip(zip(sa, sb)).0 == sa
    ensures unzip(zip(sa, sb)).1 == sb
  {
  }
  
  function method {:opaque} flatten_shape<A>(seqs: seq<seq<A>>) : (shape: seq<nat>)
  /* receives a sequence of sequences. Returns a sequence in which the ith element corresponds 
  to the length of the sequence at the ith position*/
    ensures |shape| == |seqs|
    ensures forall i :: 0 <= i < |shape| ==> shape[i] == |seqs[i]|
  {
    if |seqs| == 0 then []
    else flatten_shape(drop_last(seqs)) + [|last(seqs)|]
  }

  lemma lemma_flatten_shape_addition<A>(seqs1: seq<seq<A>>, seqs2: seq<seq<A>>)
  /* concatenating two sequences and then flattening their shape retults in the same
  result as flattenning each sequence first and then concatenating */
    ensures flatten_shape(seqs1 + seqs2) == flatten_shape(seqs1) + flatten_shape(seqs2)
  {
  }
  
  function method {:opaque} flatten_length(shape: seq<nat>) : nat
  /* returns a number that results from adding up each all 
  of the elements in the sequence's shape */
    ensures |shape| == 0 ==> flatten_length(shape) == 0
  {
    if |shape| == 0 then 0
    else flatten_length(drop_last(shape)) + last(shape)
  }

  lemma {:induction true} lemma_flatten_length_addition(shape1: seq<nat>, shape2: seq<nat>)
  /* concatenating two "shape" sequences together and then flattening their length is 
  the same as flattening each shape's length and then adding the resulting numbers */
    ensures flatten_length(shape1 + shape2) == flatten_length(shape1) + flatten_length(shape2)
  {
    if |shape2| == 0 {
      assert shape1 + shape2 == shape1;
    } else {
      reveal_flatten_length();
      assert shape1 + shape2 == (shape1 + drop_last(shape2)) + [last(shape2)];
    }
  }
  
  lemma lemma_flatten_length_subseq(shape: seq<nat>, from: nat, to: nat)
  /* the flattened length of any subsequence of the shape is less than 
  the flattened length of the whole shape */
    requires from <= to <= |shape|
    ensures flatten_length(shape[from..to]) <= flatten_length(shape)
  {
    assert shape == shape[..from] + shape[from..to] + shape[to..];
    lemma_flatten_length_addition(shape[..from] + shape[from..to], shape[to..]);
    lemma_flatten_length_addition(shape[..from], shape[from..to]);
  }

  function method {:opaque} flatten<A>(seqs: seq<seq<A>>) : seq<A>
  /* the flattened sequence's length will be equal to flattenening the shape 
  and then flattening the length; returns a sequence that combines all sequences of 
  the sequence */
    ensures |flatten(seqs)| == flatten_length(flatten_shape(seqs))
    ensures |seqs| == 0 ==> |flatten(seqs)| == 0
  {
    reveal_flatten_shape();
    reveal_flatten_length();
    if |seqs| == 0 then []
    else flatten(drop_last(seqs)) + last(seqs)
  }

  lemma lemma_flatten_singleton<A>(s: seq<A>)
  // flattening a singleton of sequences will simply result in the original sequence
    ensures flatten([ s ]) == s
  {
    reveal_flatten();
  }
  
  lemma lemma_flatten_addition<A>(seqs1: seq<seq<A>>, seqs2: seq<seq<A>>)
  /* concatenating two sequences and then flattening them has the same result 
  as flattening each sequence seperately and then concatenating afterwards */
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
  
  function method flatten_index(shape: seq<nat>, i: nat, j: nat) : nat
  /* returns the index of the flattened sequence  */
    requires i < |shape|
    requires j < shape[i]
  {
    flatten_length(shape[..i]) + j
  }

  function method unflatten_index(shape: seq<nat>, i: nat) : (nat, nat)
  /* returns the index of the unflattened sequence */
    requires i < flatten_length(shape)
  {
    reveal_flatten_length();
    if i < flatten_length(drop_last(shape)) then unflatten_index(drop_last(shape), i)
    else (|shape|-1, i - flatten_length(drop_last(shape)))
  }

  lemma lemma_flatten_index_in_bounds(shape: seq<nat>, i: nat, j: nat)
  /* the index in a flattened sequence is less than the flattened length
  of the entire sequence */
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
  
  lemma {:induction true} lemma_unflatten_index_in_bounds(shape: seq<nat>, i: nat)
  /* the unflattened index is in the bounds if the index is less than the sequence's flattened length  */
    requires i < flatten_length(shape)
    ensures unflatten_index(shape, i).0 < |shape|
    ensures unflatten_index(shape, i).1 < shape[unflatten_index(shape, i).0]
  {
    var shapeidx := unflatten_index(shape, i).0;
  }

  lemma {:induction true} lemma_flatten_unflatten_indentity(shape: seq<nat>, i: nat)
  /* flattening and then unflattening the sequence results in the original sequence */
    requires i < flatten_length(shape)
    ensures unflatten_index(shape, i).0 < |shape|
    ensures unflatten_index(shape, i).1 < shape[unflatten_index(shape, i).0]
    ensures i == flatten_index(shape, unflatten_index(shape, i).0, unflatten_index(shape, i).1)
  {
    lemma_unflatten_index_in_bounds(shape, i);
    var (shapeidx, shapeoff) := unflatten_index(shape, i);
    if shapeidx == |shape|-1 {
    } else {
      lemma_flatten_unflatten_indentity(drop_last(shape), i);
      assert drop_last(shape)[..shapeidx] == shape[..shapeidx];
    }
  }
  
  lemma lemma_unflatten_flatten_identity(shape: seq<nat>, i: nat, j: nat)
  /* unflattening and then flattening the sequence results in the original sequence */
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
  
  lemma {:induction true} lemma_unflatten_index_ordering(shape: seq<nat>, i: nat, j: nat)
  // the ordering of flattened indicies is also an indicator of placement in the unflattened sequence
    requires i < j < flatten_length(shape)
    ensures unflatten_index(shape, i).0 <= unflatten_index(shape, j).0
    ensures unflatten_index(shape, i).0 == unflatten_index(shape, j).0 ==> unflatten_index(shape, i).1 < unflatten_index(shape, j).1
  {
    lemma_flatten_unflatten_indentity(shape, i);
  }

  lemma lemma_flatten_index_is_correct<A>(seqs: seq<seq<A>>, i: nat, j: nat)
  // the flattened index is correct
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

  lemma {:induction true} {:timeLimitMultiplier 3} lemma_unflatten_index_is_correct<A>(seqs: seq<seq<A>>, i: nat)
  // proves that the unflattened index is correct
    requires i < flatten_length(flatten_shape(seqs))
    ensures unflatten_index(flatten_shape(seqs), i).0 < |seqs|
    ensures unflatten_index(flatten_shape(seqs), i).1 < |seqs[unflatten_index(flatten_shape(seqs), i).0]|
    ensures flatten(seqs)[i] == seqs[unflatten_index(flatten_shape(seqs), i).0][unflatten_index(flatten_shape(seqs), i).1]
  {
    var shape := flatten_shape(seqs);
    lemma_unflatten_index_in_bounds(shape, i);
    reveal_flatten();
  }

  lemma lemma_cardinality_of_set_and_sequence<T>(q:seq<T>, t:set<int>)
  /* proves that the cardinality of the set is the same as the cardinality 
  of the sequence, given that the set is the same size as the sequence*/
    requires t == set i | 0 <= i < |q|
    ensures |t| == |q|
  {
    if |q|>0 {
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

  function method {:opaque} seq_max(s: seq<int>): int
  // returns the maximum integer value in the sequence
    requires 0 < |s|
    ensures forall k :: k in s ==> seq_max(s) >= k
    ensures seq_max(s) in s
  {
    assert s == drop_last(s) + [last(s)];
    if |s| == 1
    then s[0]
    else Math.max(seq_max(drop_last(s)), last(s))
  }

  lemma lemma_seq_max_correspondence(s1:seq<int>, s2:seq<int>, wit: seq<nat>)
  /* the maximum value in sequence 1 is greater than or equal to the maximum
  value of sequence 2 */
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

  lemma lemma_subseq_max(s: seq<int>, from: nat, to: nat)
  /* the maximum element in any subsequence will not be 
  greater than the maximum element in the full sequence */
    requires 0 <= from < to <= |s|
    ensures seq_max(s[from .. to]) <= seq_max(s)
  {
    var subseq := s[from .. to];
    lemma_seq_max_correspondence(s, subseq, seq(|subseq|, i requires 0<=i<|subseq| => i + from));
  }

  lemma lemma_seq_suffix_slice<T>(s: seq<T>, i: int, j: int, k: int)
  /* proves that if a sequence is sliced from i until the end and then sliced a seconds time, 
  the resulting sequence is the same as the original sequence shifted by i */ 
  requires 0 <= i <= |s|
  requires 0 <= j <= k <= |s| - i
  ensures s[i..][j..k] == s[i+j..i+k];
  {
  }

  lemma lemma_seq_suffix<T>(s: seq<T>, prefix_length: int, index: int)
  // from seqs_simple.i; similar to lemma_seq_suffix_slice
  /* if a sequence is sliced after the a certain length, the new sequence's
  elements' values are shifted down by that length*/
    requires 0 <= prefix_length <= index < |s|;
    ensures s[index] == s[prefix_length..][index - prefix_length];
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
  
  lemma lemma_seq_shift_after_slicing<T>(sequence:seq<T>, j:int)
  // from seqs_simple.i
  /* if a sequence is sliced after the first element, the new sequence's
  elements' values are shifted down by 1 */
    requires 0<=j<|sequence|-1;
    ensures sequence[1..][j] == sequence[j+1];
  {
  }

  lemma lemma_seq_equality<T>(a:seq<T>, b:seq<T>, len:int)
  // from seqs_simple.i; similar to lemma_seq_extensionality
  /* if sequence a and sequence b are of equall lengths and all of their
  elements are equal, a and b are equal sequences */ 
  requires |a| == |b| == len;
  requires forall i {:trigger a[i]}{:trigger b[i]} :: 0 <= i < len ==> a[i] == b[i];
  ensures a == b;
  {
    assert forall i :: 0 <= i < len ==> a[i] == b[i];
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

  function method {:opaque} fill<T>(n: int, t: T) : (res: seq<T>)
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
