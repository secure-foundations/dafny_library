include "../Nonlinear_Arithmetic/Power2.dfy"

module DataSizes {

  import opened Power2

  predicate is_bit(b: int)  { 0 <= b < 2 }
  predicate is_byte(b: int) { 0 <= b < 256 }
  predicate word_16(x: int) { 0 <= x < 0x10000 }
  predicate word_32(x: int) { 0 <= x < power2(32) }
  predicate is_word(w: int) { word_32(w) }

}
