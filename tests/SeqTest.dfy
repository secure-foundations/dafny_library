// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../src/OptionAndResult.dfy"
include "../src/Collections/Sequences/Seq.dfy"

module SeqTest {

  import opened OptionAndResult
  import opened Seq

  method {:test} TestFirst() {
    var input := [1, 2, 3, 4, 5];
    var output := First(input);
    expect output == 1;
  }

  method {:test} TestDropFirst() {
    var input := [1, 2, 3, 4, 5];
    var output := DropFirst(input);
    expect output == [2, 3, 4, 5];
  }

  method {:test} TestLast() {
    var input := [1, 2, 3, 4, 5];
    var output := Last(input);
    expect output == 5;
  }

  method {:test} TestDropLast() {
    var input := [1, 2, 3, 4, 5];
    var output := DropLast(input);
    expect output == [1, 2, 3, 4];
  }

  method {:test} TestToSet() {
    var input := [1, 2, 3, 4, 5];
    var output := ToSet(input);
    expect output == {1, 2, 3, 4, 5};
  }

  method {:test} TestIndexOf() {
    var input := [1, 2, 3, 4, 3, 5];
    var output := IndexOf(input, 3);
    expect output == 2;
  }

  method {:test} TestIndexOfOption() {
    var input := [1, 2, 3, 4, 3, 5];
    var output := IndexOfOption(input, 3);
    expect output == Some(2);
  }

  method {:test} TestLastIndexOf() {
    var input := [1, 2, 3, 4, 3, 5];
    var output := LastIndexOf(input, 3);
    expect output == 4;
  }

  method {:test} TestLastIndexOfOption() {
    var input := [1, 2, 3, 4, 3, 5];
    var output := LastIndexOfOption(input, 3);
    expect output == Some(4);
  }

  method {:test} TestRemove() {
    var input := [1, 2, 3, 4, 5];
    var output := Remove(input, 2);
    expect output == [1, 2, 4, 5];
  }

  method {:test} TestRemoveValue() {
    var input := [1, 2, 3, 4, 5];
    var output := RemoveValue(input, 3);
    expect output == [1, 2, 4, 5];
  }

  method {:test} TestInsert() {
    var input := [1, 2, 3, 4, 5];
    var output := Insert(input, 6, 5);
    expect output == [1, 2, 3, 4, 5, 6];
  }

  method {:test} TestReverse() {
    var input := [1, 2, 3, 4, 5];
    var output := Reverse(input);
    expect output == [5, 4, 3, 2, 1];
  }

  method {:test} TestRepeat() {
    var output := Repeat(1, 5);
    expect output == [1, 1, 1, 1, 1];
  }

  method {:test} TestUnzip() {
    var input := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)];
    var output := Unzip(input);
    expect output == ([0, 1, 2, 3, 4], [1, 2, 3, 4, 5]);
  }

  method {:test} TestZip() {
    var inputA, inputB := [0, 1, 2, 3, 4], [1, 2, 3, 4, 5];
    var output := Zip(inputA, inputB);
    expect output == [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)];
  }

  method {:test} TestMax() {
    var input := [1, 2, 3, 4, 5];
    var output := Max(input);
    expect output == 5;
  }

  method {:test} TestMin() {
    var input := [1, 2, 3, 4, 5];
    var output := Min(input);
    expect output == 1;
  }

  method {:test} TestFlatten() {
    var input := [[1], [2, 3, 4, 5], [6, 7]];
    var output := Flatten(input);
    expect output == [1, 2, 3, 4, 5, 6, 7];
  }

  method {:test} TestFlattenReverse() {
    var input := [[1], [2, 3, 4, 5], [6, 7]];
    var output := FlattenReverse(input);
    expect output == [1, 2, 3, 4, 5, 6, 7];
  }

  method {:test} TestMap() {
    var input := [1, 2, 3, 4, 5];
    var output := Map(x => x * 2, input);
    expect output == [2, 4, 6, 8, 10];
  }

  method {:test} TestFilter() {
    var input := [1, 2, 3, 4, 5];
    var output := Filter(x => x % 2 == 0, input);
    expect output == [2, 4];
  }

  method {:test} TestFoldLeft() {
    var input := [1, 2, 3, 4, 5];
    var output := FoldLeft((x, y) => x - y, 0, input);
    expect output == -15;
  }

  method {:test} TestFoldRight() {
    var input := [1, 2, 3, 4, 5];
    var output := FoldRight((x, y) => x - y, input, 0);
    expect output == 3;
  }

}
