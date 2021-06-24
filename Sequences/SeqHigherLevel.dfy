include "../Mathematics.dfy"
include "../Options.dfy"

module SeqHigherLevel { 

  import Math = Mathematics
  import opened Options

  /* applies a transformation function on the sequence; this acts as "map" in other languages */
  function method {:opaque} apply<T,R>(f: (T ~> R), s: seq<T>): (result: seq<R>)
    requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> result[i] == f(s[i]);
    reads set i, o | 0 <= i < |s| && o in f.reads(s[i]):: o
  {
    if |s| == 0 then []
    else  [f(s[0])] + apply(f, s[1..])
  }

  /* Apply an injective function to each element of a sequence. */
  function method {:opaque} apply_to_set<X(!new), Y>(s: seq<X>, f: X-->Y): set<Y>
    reads f.reads
    requires forall x :: f.requires(x)
    requires Math.injective(f)
    ensures forall x :: x in s <==> f(x) in apply_to_set(s, f)
  {
    if |s| == 0 then {} else apply_to_set(s[1..], f) + {f(s[0])}
  }

  lemma {:opaque} lemma_apply_concat<T,R>(f: (T ~> R), a: seq<T>, b: seq<T>)
    requires forall i :: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j :: 0 <= j < |b| ==> f.requires(b[j])
    ensures apply(f, a + b) == apply(f, a) + apply(f, b)
  {
    reveal_apply();
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc {
        apply(f, a + b);
          { assert (a + b)[0] == a[0]; assert (a + b)[1..] == a[1..] + b; }
        apply(f, [a[0]]) + apply(f, a[1..] + b);
        apply(f, [a[0]]) + apply(f, a[1..]) + apply(f, b);
          {assert [(a + b)[0]] + a[1..] + b == a + b;}
        apply(f, a) + apply(f, b);
      }
    }
  }

  /* uses a selection function to select elements from the sequence */
  function method {:opaque} filter<T>(f: (T ~> bool), s: seq<T>): (result: seq<T>)
    requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
    ensures |result| <= |s|
    ensures forall i: nat :: i < |result| && f.requires(result[i]) ==> f(result[i])
    reads f.reads
  {
    if |s| == 0 then []
    else ((if f(s[0]) then [s[0]] else []) + filter(f, s[1..]))
  }

  lemma {:opaque} lemma_filter_concat<T>(f: (T ~> bool), a: seq<T>, b: seq<T>)
    requires forall i :: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j :: 0 <= j < |b| ==> f.requires(b[j])
    ensures filter(f, a + b) == filter(f, a) + filter(f, b)
  {
    reveal_filter();
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc {
        filter(f, a + b);
          { assert (a + b)[0] == a[0]; assert (a + b)[1..] == a[1..] + b; }
        filter(f, [a[0]]) + filter(f, a[1..] + b);
        filter(f, [a[0]]) + filter(f, a[1..]) + filter(f, b);
          {assert [(a + b)[0]] + a[1..] + b == a + b;}
        filter(f, a) + filter(f, b);
      }
    }
  }
  
  function method {:opaque} fold_left<A,T>(f: (A, T) -> A, init: A, s: seq<T>): A
  {
    if |s| == 0 then init
    else fold_left(f, f(init, s[0]), s[1..])
  }

  lemma {:opaque} lemma_fold_left_concat<A,T>(f: (A, T) -> A, init: A, a: seq<T>, b: seq<T>)
    // ensures fold_left(f, f(init, (a+b)[0]), a + b) == fold_left(f, f(init, (a)[0]), a) 
    //         + fold_left(f, f(init, (b)[0]), b)
  {

  }

  function method {:opaque} fold_right<A,T>(f: (A, T) -> A, init: A, s: seq<T>): A
  {
    if |s| == 0 then init
    else f(fold_right(f, init, s[1..]), s[0])
  }

  lemma {:opaque} lemma_fold_right_concat<A,T>(f: (A, T) -> A, init: A, a: seq<T>, b: seq<T>)
    //ensures fold_right(f, init, a + b) == fold_right(f, init, a) + fold_right(f, init, b)
  {
  }

  lemma {:opaque} lemma_apply_then_fold_right_same_as_fold_right_then_apply<A, T, R>
                  (f1: (A, T) -> A, f2: (T ~> R), init: A, s: seq<T>)
  //   ensures apply(f2, [fold_right(f1, init, s)]) == fold_right(f1, init, apply(f2, s))
  // {
  //   reveal_fold_right();
  // }

}