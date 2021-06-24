include "SeqLast.dfy"

module SeqOfSeq {

  import opened SeqLast

  /*concatenates a sequence of sequences into a single sequence. Works by adding 
  elements in order from first to last */
  function method flatten<T>(s: seq<seq<T>>): seq<T>
  decreases |s|
  {
    if |s| == 0 then []
    else s[0] + flatten(s[1..])
  }

  /* concatenating two sequences of sequences is equivalent to concatenating 
  each sequence of sequences seperately, and then concatenating the two resulting 
  sequences together */
  lemma lemma_flatten_concat<T>(a: seq<seq<T>>, b: seq<seq<T>>)
    ensures flatten(a + b) == flatten(a) + flatten(b)
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc == {
        flatten(a + b);
          { assert (a + b)[0] == a[0];  assert (a + b)[1..] == a[1..] + b; }
        a[0] + flatten(a[1..] + b);
        a[0] + flatten(a[1..]) + flatten(b);
        flatten(a) + flatten(b);
      }
    }
  }

  /* concatenates the sequence of sequences into a single sequence. Works by concatenating 
  elements from last to first */
  function method flatten_reverse<T>(s: seq<seq<T>>): seq<T>
  decreases |s|
  {
    if |s| == 0 then []
    else flatten_reverse(drop_last(s)) + last(s)
  }

  /* concatenating two reversed sequences of sequences is the same as reversing two 
  sequences of sequences and then concattenating the two resulting sequences together */
  lemma lemma_flatten_reverse_concat<T>(A:seq<seq<T>>, B:seq<seq<T>>)
  ensures flatten_reverse(A + B) == flatten_reverse(A) + flatten_reverse(B)
  {
    if |B| == 0 {
      assert flatten_reverse(B) == [];
      assert A+B == A;
    } else {
      calc == {
        flatten_reverse(A + B);
          { assert last(A + B) == last(B);  assert drop_last(A + B) == A + drop_last(B); }
        flatten_reverse(A + drop_last(B)) + last(B);
        flatten_reverse(A) + flatten_reverse(drop_last(B)) + last(B);
        flatten_reverse(A) + flatten_reverse(B);
      }
    }
  }

  /* both methods of concatenating sequence (starting from front v. starting from back)
  result in the same sequence */
  lemma lemma_flatten_and_flatten_reverse_are_equivalent<T>(s: seq<seq<T>>)
    ensures flatten(s) == flatten_reverse(s)
  {
    if |s| == 0 {
    } else {
      calc == {
        flatten_reverse(s);
        flatten_reverse(drop_last(s)) + last(s);
          { lemma_flatten_and_flatten_reverse_are_equivalent(drop_last(s)); }
        flatten(drop_last(s)) + last(s);
        flatten(drop_last(s)) + flatten([last(s)]);
          { lemma_flatten_concat(drop_last(s), [last(s)]); 
        assert s == drop_last(s) + [last(s)]; }
        flatten(s);
      }
    }
  }

  /* the concatenated sequence's length is greater than or equal to each individual
  inner sequence's length */
  lemma lemma_flatten_length_ge_single_element_length<T>(s: seq<seq<T>>, i: int)
    requires 0 <= i < |s|
    ensures |flatten_reverse(s)| >= |s[i]|
  {
    if i < |s| - 1 {
      lemma_flatten_length_ge_single_element_length(s[..|s|-1], i);
    }
  }

  /* the length of concatenating sequence in a sequence together will be no longer 
  than the length of the original sequence of sequences multiplied by the length of 
  the longest sequence */
  lemma lemma_flatten_length_le_mul<T>(s: seq<seq<T>>, j: int)
    requires forall i | 0 <= i < |s| :: |s[i]| <= j
    ensures |flatten_reverse(s)| <= |s| * j
  {
    if |s| == 0 {
    } else {
      lemma_flatten_length_le_mul(s[..|s|-1], j);
    }
  }

}