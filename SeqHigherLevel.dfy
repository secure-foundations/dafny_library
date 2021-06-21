module SeqHigherLevel { 
  // applies a transformation function on the sequence
  function method {:opaque} Map<T,R>(f: (T ~> R), s: seq<T>): (result: seq<R>)
    requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> result[i] == f(s[i]);
    reads set i, o | 0 <= i < |s| && o in f.reads(s[i]):: o
  {
    if |s| == 0 then []
    else  [f(s[0])] + Map(f, s[1..])
  }

  // uses a selection function to select elements from the sequence
  function method {:opaque} filter<T>(f : (T ~> bool), s: seq<T>): (result: seq<T>)
    requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
    ensures |result| <= |s|
    ensures forall i: nat :: i < |result| && f.requires(result[i]) ==> f(result[i])
    reads f.reads
  {
    if |s| == 0 then []
    else ((if f(s[0]) then [s[0]] else []) + filter(f, s[1..]))
  }
  
  function method {:opaque} fold_left<A,T>(f: (A, T) -> A, init: A, s: seq<T>): A
  {
    if |s| == 0 then init
    else fold_left(f, f(init, s[0]), s[1..])
  }

  function method {:opaque} fold_right<A,T>(f: (A, T) -> A, init: A, s: seq<T>): A
  {
    if |s| == 0 then init
    else f(fold_right(f, init, s[1..]), s[0])
  }
}