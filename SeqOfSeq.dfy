include "SeqLast.dfy"

module SeqOfSeq {

  import opened SeqLast

  /*concatenates a sequence of sequences into a single sequence. 
  Works by adding elements in order from first to last */
  function method concat<T>(s: seq<seq<T>>): seq<T>
  decreases |s|
  {
    if |s| == 0 then []
    else s[0] + concat(s[1..])
  }

    /* concatenating two sequences of sequences is equivalent to concatenating
  each sequence of sequences seperately, and then concatenating the two resulting 
  sequences together */
  lemma lemma_concat_adds<T>(a: seq<seq<T>>, b: seq<seq<T>>)
    ensures concat(a + b) == concat(a) + concat(b)
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc == {
        concat(a + b);
          { assert (a + b)[0] == a[0];  assert (a + b)[1..] == a[1..] + b; }
        a[0] + concat(a[1..] + b);
        a[0] + concat(a[1..]) + concat(b);
        concat(a) + concat(b);
      }
    }
  }

  /* concatenates the sequence of sequences into a single sequence. 
  works by adding elements from last to first */
  function method concat_reverse<T>(s: seq<seq<T>>): seq<T>
  decreases |s|
  {
    if |s| == 0 then []
    else concat_reverse(drop_last(s)) + last(s)
  }

  /* concatenating two reversed sequences of sequences is the same as reversing two 
  sequences of sequences and then adding the two resulting sequences together */
  lemma lemma_concat_reverse_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
  ensures concat_reverse(A + B) == concat_reverse(A) + concat_reverse(B)
  {
    if |B| == 0 {
      assert concat_reverse(B) == [];
      assert A+B == A;
    } else {
      calc == {
        concat_reverse(A + B);
          { assert last(A + B) == last(B);  assert drop_last(A + B) == A + drop_last(B); }
        concat_reverse(A + drop_last(B)) + last(B);
        concat_reverse(A) + concat_reverse(drop_last(B)) + last(B);
        concat_reverse(A) + concat_reverse(B);
      }
    }
  }

  /* both methods of concatenating sequence (starting from front v. starting from back)
  result in the same sequence */
  lemma lemma_concat_and_concat_reverse_are_equivalent<T>(s: seq<seq<T>>)
    ensures concat(s) == concat_reverse(s)
  {
    if |s| == 0 {
    } else {
      calc == {
        concat_reverse(s);
        concat_reverse(drop_last(s)) + last(s);
          { lemma_concat_and_concat_reverse_are_equivalent(drop_last(s)); }
        concat(drop_last(s)) + last(s);
        concat(drop_last(s)) + concat([last(s)]);
          { lemma_concat_adds(drop_last(s), [last(s)]); 
        assert s == drop_last(s) + [last(s)]; }
        concat(s);
      }
    }
  }

  /* the concatenated sequence's length is greater than or equal to 
  each individual inner sequence's length */
  lemma lemma_concat_length_ge_single_element_length<T>(s: seq<seq<T>>, i: int)
  requires 0 <= i < |s|
  ensures |concat_reverse(s)| >= |s[i]|
  {
    if i < |s| - 1 {
      lemma_concat_length_ge_single_element_length(s[..|s|-1], i);
    }
  }

  /* the length of concatenating sequence in a sequence together will be no longer 
  than the length of the original sequence of sequences multiplied by the length of 
  the longest sequence */
  lemma lemma_concat_length_le_mul<T>(s: seq<seq<T>>, j: int)
  requires forall i | 0 <= i < |s| :: |s[i]| <= j
  ensures |concat_reverse(s)| <= |s| * j
  {
    if |s| == 0 {
    } else {
      lemma_concat_length_le_mul(s[..|s|-1], j);
    }
  }

}