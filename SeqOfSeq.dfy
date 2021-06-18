include "SeqLast.dfy"

module SeqOfSeq {

  import opened SeqLast

  /*concatenates a sequence of sequences into a single sequence. 
  Works by adding elements in order from first to last */
  function method seq_concat<T>(s: seq<seq<T>>): seq<T>
  decreases |s|
  {
    if |s| == 0 then []
    else s[0] + seq_concat(s[1..])
  }

  // turns a sequence of sequences into a single sequence and returns the result
  function method {:opaque} concat_seq<T>(s: seq<seq<T>>): seq<T>
  {
    if |s| == 0 then [] else concat_seq(drop_last(s)) + last(s)
  }

    /* concatenating two sequences of sequences is equivalent to concatenating
  each sequence of sequences seperately, and then concatenating the two resulting 
  sequences together */
  lemma lemma_seq_concat_adds<T>(a: seq<seq<T>>, b: seq<seq<T>>)
    ensures seq_concat(a + b) == seq_concat(a) + seq_concat(b)
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc == {
        seq_concat(a + b);
          { assert (a + b)[0] == a[0];  assert (a + b)[1..] == a[1..] + b; }
        a[0] + seq_concat(a[1..] + b);
        a[0] + seq_concat(a[1..]) + seq_concat(b);
        seq_concat(a) + seq_concat(b);
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
  function method seq_concat_reverse<T>(s: seq<seq<T>>): seq<T>
  decreases |s|
  {
    if |s| == 0 then []
    else seq_concat_reverse(drop_last(s)) + last(s)
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
  lemma lemma_seq_concat_and_seq_concat_reverse_are_equivalent<T>(s: seq<seq<T>>)
    ensures seq_concat(s) == seq_concat_reverse(s)
  {
    if |s| == 0 {
    } else {
      calc == {
        seq_concat_reverse(s);
        seq_concat_reverse(drop_last(s)) + last(s);
          { lemma_seq_concat_and_seq_concat_reverse_are_equivalent(drop_last(s)); }
        seq_concat(drop_last(s)) + last(s);
        seq_concat(drop_last(s)) + seq_concat([last(s)]);
          { lemma_seq_concat_adds(drop_last(s), [last(s)]); 
        assert s == drop_last(s) + [last(s)]; }
        seq_concat(s);
      }
    }
  }

  /* the concatenated sequence's length is greater than or equal to 
  each individual inner sequence's length */
  lemma lemma_concat_seq_length_ge_single_element_length<T>(s: seq<seq<T>>, i: int)
  requires 0 <= i < |s|
  ensures |concat_seq(s)| >= |s[i]|
  {
    reveal_concat_seq();
    if i < |s| - 1 {
      lemma_concat_seq_length_ge_single_element_length(s[..|s|-1], i);
    }
  }

  /* the length of concatenating sequence in a sequence together will be no longer 
  than the length of the original sequence of sequences multiplied by the length of 
  the longest sequence */
  lemma lemma_concat_seq_length_le_mul<T>(s: seq<seq<T>>, j: int)
  requires forall i | 0 <= i < |s| :: |s[i]| <= j
  ensures |concat_seq(s)| <= |s| * j
  {
    reveal_concat_seq();
    if |s| == 0 {
    } else {
      lemma_concat_seq_length_le_mul(s[..|s|-1], j);
    }
  }

}