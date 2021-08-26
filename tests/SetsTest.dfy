// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../src/Collections/Sets/Sets.dfy"

module SetsTest {

  import opened Sets

  method {:test} TestMap() {
    var input := {1, 2, 3, 4, 5};
    var output := Map(input, x => x * 2);
    expect output == {2, 4, 6, 8, 10};
  }

  method {:test} TestFilter() {
    var input := {1, 2, 3, 4, 5};
    var output := Filter(input, x => x % 2 == 0);
    expect output == {2, 4};
  }

  method {:test} TestSetRange() {
    var output := SetRange(1, 6);
    expect output == {1, 2, 3, 4, 5};
  }

  method {:test} TestSetRangeZeroBound() {
    var output := SetRangeZeroBound(6);
    expect output == {0, 1, 2, 3, 4, 5};
  }

}
