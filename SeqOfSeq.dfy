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

}