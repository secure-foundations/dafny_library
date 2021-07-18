include "../Nonlinear_Arithmetic/Power2.dfy"

module DataSizes {

  import opened Power2

  const BIT:      int := power2(1)
  const BYTE:     int := power2(8)
  const WORD_16:  int := power2(16)
  const WORD_32:  int := power2(32)
  const WORD_64:  int := power2(64)

  predicate is_bit(x: int)      { 0 <= x < BIT }
  predicate is_byte(x: int)     { 0 <= x < BYTE }
  predicate is_word_16(x: int)  { 0 <= x < WORD_16 }
  predicate is_word_32(x: int)  { 0 <= x < WORD_32 }
  predicate is_word_64(x: int)  { 0 <= x < WORD_64 }

}
