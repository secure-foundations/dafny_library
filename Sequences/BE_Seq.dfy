/* BE/LE refers to the endianness of the transformation. There's no inherent
endianness in a sequence until it's interpreted. */

include "DataSizes.dfy"
include "../Nonlinear_Arithmetic/Power2.dfy"

module BE_Seq {

  import opened DataSizes
  import opened Power2

  //////////////////////////////////////////////////////////////////////////////
  //
  // Sequence types (bit, byte, word)
  //
  //////////////////////////////////////////////////////////////////////////////

  /* True iff each element of s is between 0 and data_size. */
  predicate is_digit_seq(data_size: int, s: seq<int>)
  {
    forall i {:trigger s[i]} :: 0 <= i < |s| ==> 0 <= s[i] < data_size
  }

  predicate is_bit_seq(s: seq<int>)
  {
    is_digit_seq(BIT, s)
  }

  predicate is_byte_seq(s: seq<int>)
  {
    is_digit_seq(BYTE, s)
  }

  predicate is_word_16_seq(s: seq<int>)
  {
    is_digit_seq(WORD_16, s)
  }

  predicate is_word_32_seq(s: seq<int>)
  {
    is_digit_seq(WORD_32, s)
  }

  predicate is_word_64_seq(s: seq<int>)
  {
    is_digit_seq(WORD_64, s)
  }

  predicate is_bit_seq_of_len(s: seq<int>, len: int)
  {
    is_bit_seq(s) && |s| == len
  }

  predicate is_byte_seq_of_len(s: seq<int>, len: int)
  {
    is_byte_seq(s) && |s| == len
  }

  predicate is_word_16_seq_of_len(s: seq<int>, len: int)
  {
    is_word_16_seq(s) && |s| == len
  }

  predicate is_word_32_seq_of_len(s: seq<int>, len: int)
  {
    is_word_32_seq(s) && |s| == len
  }

  predicate is_word_64_seq_of_len(s: seq<int>, len: int)
  {
    is_word_64_seq(s) && |s| == len
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Utility functions
  //
  //////////////////////////////////////////////////////////////////////////////

  function method {:opaque} be_extend_seq(s: seq<int>, len: int): seq<int>
    requires |s| <= len
    ensures |be_extend_seq(s, len)| == len
    decreases len - |s|
  {
    if |s| == len then s else be_extend_seq([0] + s, len)
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Conversions from sequences to ints
  //
  /////////////////////////////////////////////////////////////////////////////

  /* Tranforms a sequence of digits into an int. */
  function method {:opaque} be_digit_seq_to_int_private(data_size: int,
                                                        s: seq<int>): int
  {
    if s == [] then 0
    else be_digit_seq_to_int_private(data_size, s[0 .. |s|-1])
       * data_size + s[|s|-1]
  }

  function method be_digit_seq_to_int(data_size: int, s: seq<int>): int
    requires is_digit_seq(data_size, s)
  {
    be_digit_seq_to_int_private(data_size, s)
  }

  function method {:autoReq} be_bit_seq_to_int(s: seq<int>): int
  {
    be_digit_seq_to_int(BIT, s)
  }

  function method {:autoReq} be_byte_seq_to_int(s: seq<int>): int
  {
    be_digit_seq_to_int(BYTE, s)
  }

  function method {:autoReq} be_word_16_seq_to_int(s: seq<int>): int
  {
    be_digit_seq_to_int(WORD_16, s)
  }

  function method {:autoReq} be_word_32_seq_to_int(s: seq<int>): int
  {
    be_digit_seq_to_int(WORD_32, s)
  }

  function method {:autoReq} be_word_64_seq_to_int(s: seq<int>): int
  {
    be_digit_seq_to_int(WORD_64, s)
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Conversions from ints to sequences
  //
  //////////////////////////////////////////////////////////////////////////////

  // Move to DivMod
  lemma {:axiom} div_properties_dafny_cannot_see(n: int, d: int)
    requires d > 1;
    ensures n > 0 ==> n / d < n;
    ensures n <= 0 ==> n / d <= 0;

  /* Tranforms a single value into a sequence of digits. */
  function method {:opaque} be_int_to_digit_seq_private(data_size: int,
                                                        min_length: int,
                                                        x: int): seq<int>
    decreases if x > min_length then x else min_length
  {
    if data_size > 1 && (x > 0 || min_length > 0) then
      div_properties_dafny_cannot_see(x, data_size);
      be_int_to_digit_seq_private(data_size, min_length - 1, x / data_size)
        + [x % data_size]
    else []
  }

  function method be_int_to_digit_seq(data_size: int,
                                      min_length: int,
                                      x: int): seq<int>
  {
    be_int_to_digit_seq_private(data_size, min_length, x)
  }

  function method be_int_to_bit_seq(x: int): seq<int>
  {
    be_int_to_digit_seq(BIT, 0, x)
  }

  function method be_int_to_byte_seq(x: int): seq<int>
  {
    be_int_to_digit_seq(BYTE, 0, x)
  }

  function method be_int_to_word_16_seq(x: int): seq<int>
  {
    be_int_to_digit_seq(WORD_16, 0, x)
  }

  function method be_int_to_word_32_seq(x: int): seq<int>
  {
    be_int_to_digit_seq(WORD_32, 0, x)
  }

  function method be_int_to_word_64_seq(x: int): seq<int>
  {
    be_int_to_digit_seq(WORD_64, 0, x)
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Equality between sequences and values
  //
  //////////////////////////////////////////////////////////////////////////////

  predicate be_digit_seq_eq_int(data_size: int, s: seq<int>, x: int)
  {
    is_digit_seq(data_size, s) && be_digit_seq_to_int(data_size, s) == x
  }

  predicate be_bit_seq_eq_int(s: seq<int>, x: int)
  {
    be_digit_seq_eq_int(BIT, s, x)
  }

  predicate be_byte_seq_eq_int(s: seq<int>, x: int)
  {
    be_digit_seq_eq_int(BYTE, s, x)
  }

  predicate be_word_16_seq_eq_int(s: seq<int>, x: int)
  {
    be_digit_seq_eq_int(WORD_16, s, x)
  }

  predicate be_word_32_seq_eq_int(s: seq<int>, x: int)
  {
    be_digit_seq_eq_int(WORD_32, s, x)
  }

  predicate be_word_64_seq_eq_int(s: seq<int>, x: int)
  {
    be_digit_seq_eq_int(WORD_64, s, x)
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Equality among sequences
  //
  //////////////////////////////////////////////////////////////////////////////

  predicate be_bit_seq_eq_byte_seq(bits: seq<int>, bytes: seq<int>)
  {
    exists x :: be_bit_seq_eq_int(bits, x) && be_byte_seq_eq_int(bytes, x)
  }

  predicate be_bit_seq_eq_word_16_seq(bits: seq<int>, words: seq<int>)
  {
    exists x :: be_bit_seq_eq_int(bits, x) && be_word_16_seq_eq_int(words, x)
  }

  predicate be_bit_seq_eq_word_32_seq(bits: seq<int>, words: seq<int>)
  {
    exists x :: be_bit_seq_eq_int(bits, x) && be_word_32_seq_eq_int(words, x)
  }

  predicate be_bit_seq_eq_word_64_seq(bits: seq<int>, words: seq<int>)
  {
    exists x :: be_bit_seq_eq_int(bits, x) && be_word_64_seq_eq_int(words, x)
  }

  predicate be_byte_seq_eq_word_16_seq(bytes: seq<int>, words: seq<int>)
  {
    exists x :: be_byte_seq_eq_int(bytes, x) && be_word_16_seq_eq_int(words, x)
  }

  predicate be_byte_seq_eq_word_32_seq(bytes: seq<int>, words: seq<int>)
  {
    exists x :: be_byte_seq_eq_int(bytes, x) && be_word_32_seq_eq_int(words, x)
  }

  predicate be_byte_seq_eq_word_64_seq(bytes: seq<int>, words: seq<int>)
  {
    exists x :: be_byte_seq_eq_int(bytes, x) && be_word_64_seq_eq_int(words, x)
  }

  predicate be_word_16_seq_eq_word_32_seq(bytes: seq<int>, words: seq<int>)
  {
    exists x :: be_word_16_seq_eq_int(bytes, x)
             && be_word_32_seq_eq_int(words, x)
  }

  predicate be_word_16_seq_eq_word_64_seq(bytes: seq<int>, words: seq<int>)
  {
    exists x :: be_word_16_seq_eq_int(bytes, x)
             && be_word_64_seq_eq_int(words, x)
  }

  predicate be_word_32_seq_eq_word_64_seq(bytes: seq<int>, words: seq<int>)
  {
    exists x :: be_word_32_seq_eq_int(bytes, x)
             && be_word_64_seq_eq_int(words, x)
  }

}
