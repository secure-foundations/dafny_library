module SeqLast {

  // returns the last element in the sequence
  function method last<E>(s: seq<E>): E
    requires |s| > 0;
  {
    s[|s|-1]
  }

  // returns the sequence slice up to but not including the last element
  function method drop_last<E>(s: seq<E>): seq<E> 
  requires |s| > 0;
  {
    s[..|s|-1]
  }

  // concatenating everything but the last element + the last element results in the original seq 
  lemma lemma_last<T>(s: seq<T>)
    requires |s| > 0;
    ensures  drop_last(s) + [last(s)] == s;
  {
  }
}