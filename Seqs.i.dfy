module Collections__Seqs_i {

lemma SeqAdditionIsAssociative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
// explains associative property of sequences in addition
  ensures a+(b+c) == (a+b)+c;
{
}

predicate ItemAtPositionInSeq<T>(s:seq<T>, v:T, idx:int)
// defines if the element is at a specific position in the sequence
{
  0 <= idx < |s| && s[idx] == v
}

lemma Lemma_ItemInSeqAtASomePosition<T>(s:seq<T>, v:T)
// if there is an element at a certain index, then that index exists
  requires v in s
  ensures exists idx :: ItemAtPositionInSeq(s, v, idx)
{
  var idx :| 0 <= idx < |s| && s[idx] == v;
  assert ItemAtPositionInSeq(s, v, idx);
}

function FindIndexInSeq<T>(s:seq<T>, v:T):int
/* finds the index of a certain value in the sequence, if it exists. Returns
the index, or -1 if the value is not included in the sequence */
  ensures var idx := FindIndexInSeq(s, v);
          if idx >= 0 then
            idx < |s| && s[idx] == v
          else
            v !in s
{
  if v in s then
    Lemma_ItemInSeqAtASomePosition(s, v);
    var idx :| ItemAtPositionInSeq(s, v, idx);
    idx
  else
    -1
}

lemma Lemma_IdenticalSingletonSequencesHaveIdenticalElement<T>(x:T, y:T)
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
function SeqCat<T>(seqs:seq<seq<T>>) : seq<T>
// concatenates a sequence of sequences into a single sequence
  decreases |seqs|
{
  if |seqs| == 0 then []
  else seqs[0] + SeqCat(seqs[1..])
}

function SeqCatRev<T>(seqs:seq<seq<T>>) : seq<T>
// concatenates the sequence in reverse and returns the resulting sequence  
  decreases |seqs|
{
  if |seqs| == 0 then []
  else SeqCatRev(all_but_last(seqs)) + last(seqs)
}

lemma lemma_SeqCat_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
/* concatenating two sequences of sequences is equivalent to concatenating
each sequence of sequences seperately, and then concatenating the two resulting 
sequences together */
  ensures SeqCat(A + B) == SeqCat(A) + SeqCat(B)
{
  if |A| == 0 {
    assert A+B == B;
  } else {
    calc == {
      SeqCat(A + B);
        { assert (A + B)[0] == A[0];  assert (A + B)[1..] == A[1..] + B; }
      A[0] + SeqCat(A[1..] + B);
      A[0] + SeqCat(A[1..]) + SeqCat(B);
      SeqCat(A) + SeqCat(B);
    }
  }
}

lemma lemma_SeqCatRev_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
/* concatenating two reversed sequences of sequences is the same as reversing two 
sequences of sequences and then adding the two resulting sequences together */
  ensures SeqCatRev(A + B) == SeqCatRev(A) + SeqCatRev(B)
{
  if |B| == 0 {
    assert SeqCatRev(B) == [];
    assert A+B == A;
  } else {
    calc == {
      SeqCatRev(A + B);
        { assert last(A + B) == last(B);  assert all_but_last(A + B) == A + all_but_last(B); }
      SeqCatRev(A + all_but_last(B)) + last(B);
      SeqCatRev(A) + SeqCatRev(all_but_last(B)) + last(B);
      SeqCatRev(A) + SeqCatRev(B);
    }
  }
}

lemma lemma_SeqCat_equivalent<T>(seqs:seq<seq<T>>)
// 
  ensures SeqCat(seqs) == SeqCatRev(seqs)
{
  if |seqs| == 0 {
  } else {
    calc == {
      SeqCatRev(seqs);
      SeqCatRev(all_but_last(seqs)) + last(seqs);
        { lemma_SeqCat_equivalent(all_but_last(seqs)); }
      SeqCat(all_but_last(seqs)) + last(seqs);
      SeqCat(all_but_last(seqs)) + SeqCat([last(seqs)]);
        { lemma_SeqCat_adds(all_but_last(seqs), [last(seqs)]); 
      assert seqs == all_but_last(seqs) + [last(seqs)]; }
      SeqCat(seqs);
    }
  }
}

}