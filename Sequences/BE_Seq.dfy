/* BE/LE refers to the endianness of the transformation. There's no inherent
endianness in a sequence until it's interpreted. */

include "DataSizes.dfy"
include "../Nonlinear_Arithmetic/Power2.dfy"

module BE_Seq {

  import opened DataSizes
  import opened Power2

  //////////////////////////////////////////////////////////////////////////////
  //
  // Sequence Types
  //
  //////////////////////////////////////////////////////////////////////////////

  predicate is_digit_seq(place_value: int, digits: seq<int>)
  {
    forall i {:trigger digits[i]} :: 0 <= i < |digits| ==>
                                     0 <= digits[i] < place_value
  }

  predicate is_bit_seq(s: seq<int>)
  {
    is_digit_seq(power2(1), s)
  }

  predicate is_byte_seq(s: seq<int>)
  {
    is_digit_seq(power2(8), s)
  }

  predicate is_word_seq(s: seq<int>)
  {
    is_digit_seq(power2(32), s)
  }

  predicate is_bit_seq_of_len(s: seq<int>, len: int)
  {
    is_bit_seq(s) && |s| == len
  }

  predicate is_byte_seq_of_len(s: seq<int>, len: int)
  {
    is_byte_seq(s) && |s| == len
  }

  predicate is_word_seq_of_len(s: seq<int>, len: int)
  {
    is_word_seq(s) && |s| == len
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Relationships among sequences of different digit sizes
  // (bit, byte, word, int)
  //
  //////////////////////////////////////////////////////////////////////////////


  function method {:opaque} be_digit_to_seq_private(place_value: int,
                                                    digits: seq<int>): int
  {
    if digits == [] then 0
    else be_digit_to_seq_private(place_value, digits[0 .. |digits|-1])
       * place_value + digits[|digits|-1]
  }

  function method be_digit_to_seq(place_value: int, digits: seq<int>): int
    requires is_digit_seq(place_value, digits)
  {
    be_digit_to_seq_private(place_value, digits)
  }

  function method {:autoReq} be_bit_seq_to_int(bits: seq<int>): int
  {
    be_digit_to_seq(power2(1), bits)
  }

  function method {:autoReq} be_byte_seq_to_int(bytes: seq<int>): int
  {
    be_digit_to_seq(power2(8), bytes)
  }

  function method {:autoReq} be_word_seq_to_int(words: seq<int>): int
  {
    be_digit_to_seq(power2(32), words)
  }

  function method {:opaque} be_int_to_digit_seq_private(place_value: int,
                                                        min_places: int,
                                                        v: int): seq<int>
    decreases if v > min_places then v else min_places
  {
    if place_value > 1 && (v > 0 || min_places > 0) then
      div_properties_dafny_cannot_see(v, place_value);
      be_int_to_digit_seq_private(place_value, min_places - 1, v / place_value)
        + [v % place_value]
    else []
  }

  // Move to DivMod
  lemma {:axiom} div_properties_dafny_cannot_see(n: int, d: int)
    requires d > 1;
    ensures n > 0 ==> n / d < n;
    ensures n <= 0 ==> n / d <= 0;

  function method be_int_to_digit_seq(place_value: int,
                                      min_places: int,
                                      v: int): seq<int>
  {
    be_int_to_digit_seq_private(place_value, min_places, v)
  }

  predicate be_digit_seq_eq_int(place_value: int, digits: seq<int>, v: int)
  {
    && is_digit_seq(place_value, digits)
    && be_digit_to_seq(place_value, digits) == v
  }

  predicate be_bit_seq_eq_int(bitseq: seq<int>, v: int)
  {
    be_digit_seq_eq_int(2, bitseq, v)
  }

  predicate be_bit_seq_eq_byte(bitseq: seq<int>, byte: int)
  {
    is_byte(byte) && be_bit_seq_eq_int(bitseq, byte)
  }

  predicate be_bit_seq_eq_word(bitseq: seq<int>, word: int)
  {
    is_word(word) && be_bit_seq_eq_int(bitseq, word)
  }

  predicate be_byte_seq_eq_int(byteseq: seq<int>, v: int)
  {
    be_digit_seq_eq_int(256, byteseq, v)
  }

  predicate be_byte_seq_eq_word(byteseq: seq<int>, word: int)
  {
    is_word(word) && be_byte_seq_eq_int(byteseq, word)
  }

  predicate be_word_seq_eq_int(byteseq: seq<int>, v: int)
  {
    be_digit_seq_eq_int(power2(32), byteseq, v)
  }

  predicate be_bit_seq_eq_byte_seq(bitseq: seq<int>, byteseq: seq<int>)
  {
    exists v: int ::
      be_bit_seq_eq_int(bitseq, v) && be_byte_seq_eq_int(byteseq, v)
  }

  predicate be_bit_seq_eq_word_seq(bitseq: seq<int>, wordseq: seq<int>)
  {
    exists v: int ::
      be_bit_seq_eq_int(bitseq, v) && be_word_seq_eq_int(wordseq, v)
  }

  predicate be_byte_seq_eq_word_seq(byteseq: seq<int>, wordseq: seq<int>)
  {
    exists v: int ::
      be_byte_seq_eq_int(byteseq, v) && be_word_seq_eq_int(wordseq, v)
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Generator functions (as opposed to recognizer predicates)
  //
  /////////////////////////////////////////////////////////////////////////////

  function method be_int_to_byte_seq(x: int): seq<int>
  {
    be_int_to_digit_seq(power2(8), 0, x)
  }

  function method be_word_to_4_bytes(x: int): seq<int>
    requires word_32(x);
  {
    be_int_to_digit_seq(power2(8), 4, x)
  }

  function method be_word_to_bit_seq(x: int): seq<int>
  {
    be_int_to_digit_seq(power2(1), 32, x)
  }

  function method {:autoReq} be_word_seq_to_bit_seq(wordseq: seq<int>): seq<int>
  {
    be_int_to_digit_seq(power2(1), |wordseq| * 32, be_digit_to_seq(power2(32), wordseq))
  }

  function method {:autoReq} be_byte_seq_to_bit_seq(byteseq: seq<int>): seq<int>
  {
    be_int_to_digit_seq(power2(1), |byteseq| * 8, be_digit_to_seq(power2(8), byteseq))
  }

  function method {:autoReq} be_word_seq_to_byte_seq(wordseq: seq<int>): seq<int>
  {
    be_int_to_digit_seq(power2(8), |wordseq| * 4, be_digit_to_seq(power2(32), wordseq))
  }

  function method repeat_digit(digit: int, count: int): seq<int>
    decreases count
  {
    if count <= 0 then [] else repeat_digit(digit, count - 1) + [digit]
  }

  // Move to Seq
  function method {:opaque} reverse(s: seq<int>): seq<int>
  {
    if s == [] then [] else [s[|s|-1]] + reverse(s[0 .. |s|-1])
  }

}
