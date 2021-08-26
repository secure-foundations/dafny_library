// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../src/OptionAndResult.dfy"
include "../src/Collections/Maps/Maps.dfy"
include "../src/Collections/Maps/Imaps.dfy"

module MapsTest {

  import opened OptionAndResult
  import opened Maps
  import Imaps

  method {:test} TestGet() {
    var input := map[1 := 1, 2 := 2, 3 := 3];
    var output := Get(input, 2);
    expect output == Some(2);
  }

  method {:test} TestImapsGet() {
    var input := imap[1 := 1, 2 := 2, 3 := 3];
    var output := Imaps.Get(input, 2);
    expect output == Some(2);
  }

  method {:test} TestToImap() {
    var input := map[1 := 1, 2 := 2, 3 := 3];
    var output := ToImap(input);
    expect output == imap[1 := 1, 2 := 2, 3 := 3];
  }

  method {:test} TestRemoveKeys() {
    var input := map[1 := 1, 2 := 2, 3 := 3];
    var output := RemoveKeys(input, {1, 2});
    expect output == map[3 := 3];
  }

  method {:test} TestRemove() {
    var input := map[1 := 1, 2 := 2, 3 := 3];
    var output := Remove(input, 2);
    expect output == map[1 := 1, 3 := 3];
  }

  method {:test} TestRestrict() {
    var input := map[1 := 1, 2 := 2, 3 := 3];
    var output := Restrict(input, {1, 3});
    expect output == map[1 := 1, 3 := 3];
  }

  method {:test} TestUnion() {
    var inputA := map[1 := 1, 2 := 2, 3 := 3];
    var inputB := map[3 := 3, 4 := 4];
    var output := Union(inputA, inputB);
    expect output == map[1 := 1, 2 := 2, 3 := 3, 4 := 4];
  }

}
