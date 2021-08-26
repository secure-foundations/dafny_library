// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../src/Math.dfy"

module MathTest {

  import opened Math

  method {:test} TestMin() {
    expect Min(2, 3) == 2;
  }

  method {:test} TestMax() {
    expect Max(2, 3) == 3;
  }

}
