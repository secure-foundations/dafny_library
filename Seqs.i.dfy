module Collections__Seqs_i {

lemma lemma_seq_addition_is_associative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
// explains associative property of sequences in addition
  ensures a+(b+c) == (a+b)+c;
{
}

predicate item_at_position_in_sequence<T>(s:seq<T>, v:T, idx:int)
// defines if the element is at a specific position in the sequence
{
  0 <= idx < |s| && s[idx] == v
}

lemma lemma_item_at_position_in_sequence<T>(s:seq<T>, v:T)
// if there is an element at a certain index, then that index exists
  requires v in s
  ensures exists idx :: item_at_position_in_sequence(s, v, idx)
{
  var idx :| 0 <= idx < |s| && s[idx] == v;
  assert item_at_position_in_sequence(s, v, idx);
}

function find_index_in_sequence<T>(s:seq<T>, v:T):int
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

lemma lemma_identical_seq_singletons_have_itentical_elements<T>(x:T, y:T)
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

function last<T>(s:seq<T>):T
// returns the value of the last element in the sequence
  requires |s| > 0
{
  s[|s|-1]
}

function all_but_last<T>(s:seq<T>):seq<T>
/* returns a slice of the sequence that includes all elements of the 
original sequence except for the last element */
  requires |s| > 0
  ensures  |all_but_last(s)| == |s| - 1
{
  s[..|s|-1]
}

//////////////////////////////////////////////////////////
//  Combining sequences of sequences
//////////////////////////////////////////////////////////
function seq_concat<T>(seqs:seq<seq<T>>) : seq<T>
/* concatenates a sequence of sequences into a single sequence. 
Works by adding elements in order from first to last */
  decreases |seqs|
{
  if |seqs| == 0 then []
  else seqs[0] + seq_concat(seqs[1..])
}

function seq_concat_reverse<T>(seqs:seq<seq<T>>) : seq<T>
/* concatenates the sequence of sequences into a single sequence. 
works by adding elements from last to first */
  decreases |seqs|
{
  if |seqs| == 0 then []
  else seq_concat_reverse(all_but_last(seqs)) + last(seqs)
}

lemma lemma_seq_concat_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
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

lemma lemma_seq_concat_reverse_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
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

}