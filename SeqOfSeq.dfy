include "SeqLast.dfy"

module SeqOfSeq {

  import opened SeqLast

  /*concatenates a sequence of sequences into a single sequence. 
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

}