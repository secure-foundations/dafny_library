// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../src/NonlinearArithmetic/Internals/DivInternals.dfy"
include "../src/NonlinearArithmetic/Internals/ModInternals.dfy"
include "../src/NonlinearArithmetic/Internals/MulInternals.dfy"
include "../src/NonlinearArithmetic/Power.dfy"
include "../src/NonlinearArithmetic/Power2.dfy"

module NonlinearArithmeticTest {

  import opened DivInternals
  import opened ModInternals
  import opened MulInternals
  import opened Power
  import opened Power2

  method {:test} TestDivPos() {
    expect DivPos(8, 2) == 4;
  }

  method {:test} TestDivRecursive() {
    expect DivRecursive(-8, 2) == -4;
  }

  method {:test} TestModRecursive() {
    expect ModRecursive(9, 2) == 1;
  }

  method {:test} TestMulPos() {
    expect MulPos(2, 4) == 8;
  }

  method {:test} TestMulRecursive() {
    expect MulRecursive(-2, 4) == -8;
  }

  method {:test} TestPow() {
    expect Pow(2, 3) == 8;
  }

  method {:test} TestPow2() {
    expect Pow2(3) == 8;
  }

}
