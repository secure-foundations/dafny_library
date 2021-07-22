include "../Nonlinear_Arithmetic/DivMod.dfy"
include "../Nonlinear_Arithmetic/Mul.dfy"
include "../NativeTypes.dfy"
include "../Nonlinear_Arithmetic/Power.dfy"
include "Seq.dfy"

module SeqConversions {

  import opened DivMod
  import opened Mul
  import opened NativeTypes
  import opened Power
  import opened Seq

  //////////////////////////////////////////////////////////////////////////////
  //
  // nat to sequences
  //
  //////////////////////////////////////////////////////////////////////////////

  function method {:opaque} nat_to_bytes(n: nat): seq<uint8>
  {
    if n == 0 then []
    else
      lemma_div_basics_auto();
      nat_to_bytes(n / BASE_8) + [(n % BASE_8) as uint8] 
  }

  function method {:opaque} nat_to_uint16(n: nat): seq<uint16>
  {
    if n == 0 then []
    else
      lemma_div_basics_auto();
      nat_to_uint16(n / BASE_16) + [(n % BASE_16) as uint16] 
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Sequences to nat
  //
  //////////////////////////////////////////////////////////////////////////////

  function method {:opaque} bytes_to_nat(xs: seq<uint8>): nat
  {
    if |xs| == 0 then 0
    else
      lemma_power_positive_auto();
      lemma_mul_nonnegative_auto();
      bytes_to_nat(drop_last(xs)) + last(xs) as nat * power(BASE_8, |xs| - 1)
  }

  function method {:opaque} uint16_to_nat(xs: seq<uint16>): nat
  {
    if |xs| == 0 then 0
    else
      lemma_power_positive_auto();
      lemma_mul_nonnegative_auto();
      uint16_to_nat(drop_last(xs)) + last(xs) as nat * power(BASE_16, |xs| - 1)
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Sequence conversions
  //
  //////////////////////////////////////////////////////////////////////////////

  function method {:opaque} uint16_to_bytes(xs: seq<uint16>): seq<uint8>
  {
    if |xs| == 0 then []
    else [(xs[0] % BASE_8 as uint16) as uint8,
          (xs[0] / BASE_8 as uint16) as uint8] + uint16_to_bytes(xs[1..])
  }

  function method {:opaque} uint32_to_bytes(xs: seq<uint32>): seq<uint8>
  {
    if |xs| == 0 then []
    else [(xs[0] % BASE_8 as uint32) as uint8,
          (xs[0] / BASE_8 as uint32 % BASE_8 as uint32) as uint8,
          (xs[0] / BASE_16 as uint32 % BASE_8 as uint32) as uint8,
          (xs[0] / BASE_24 as uint32) as uint8] + uint32_to_bytes(xs[1..])
  }

  function method {:opaque} bytes_to_uint16_helper(xs: seq<uint8>): seq<uint16>
    requires |xs| % 2 == 0
  {
    if |xs| == 0 then []
    else [xs[0] as uint16 + xs[1] as uint16 * BASE_8 as uint16] +
      bytes_to_uint16_helper(xs[2..])
  }

  function method {:opaque} bytes_to_uint32_helper(xs: seq<uint8>): seq<uint32>
    requires |xs| % 4 == 0
  {
    if |xs| == 0 then []
    else
      [xs[0] as uint32 +
       xs[1] as uint32 * BASE_8 as uint32 +
       xs[2] as uint32 * BASE_16 as uint32 +
       xs[3] as uint32 * BASE_24 as uint32] +
      bytes_to_uint32_helper(xs[4..])
  }

  function method {:opaque} bytes_to_uint64_helper(xs: seq<uint8>): seq<uint64>
    requires |xs| % 8 == 0
  {
    if |xs| == 0 then []
    else [xs[0] as uint64
        + xs[1] as uint64 * BASE_8 as uint64
        + xs[2] as uint64 * BASE_16 as uint64
        + xs[3] as uint64 * BASE_24 as uint64
        + xs[4] as uint64 * BASE_32 as uint64
        + xs[5] as uint64 * BASE_40 as uint64
        + xs[6] as uint64 * BASE_48 as uint64
        + xs[7] as uint64 * BASE_56 as uint64]
        + bytes_to_uint64_helper(xs[8..])
  }

  function method {:opaque} bytes_to_uint16(xs: seq<uint8>): seq<uint16>
    decreases |xs| % 2 != 0, 2 - |xs| % 2
  {
    if |xs| % 2 == 0 then bytes_to_uint16_helper(xs)
    else bytes_to_uint16(xs + [0])
  }

  function method {:opaque} bytes_to_uint32(xs: seq<uint8>): seq<uint32>
    decreases |xs| % 4 != 0, 4 - |xs| % 4
  {
    if |xs| % 4 == 0 then bytes_to_uint32_helper(xs)
    else bytes_to_uint32(xs + [0])
  }

  function method {:opaque} bytes_to_uint64(xs: seq<uint8>): seq<uint64>
    decreases |xs| % 8 != 0, 8 - |xs| % 8
  {
    if |xs| % 8 == 0 then bytes_to_uint64_helper(xs)
    else bytes_to_uint64(xs + [0])
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Uniqueness and sequence conversion lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Prove that if we start with a nat, convert it to a byte sequence,
  and convert it back, we get the same nat we started with. */
  lemma lemma_nat_bytes_nat(n: nat)
    requires bytes_to_nat(nat_to_bytes(n)) == n
  {
    assume false;
  }

  lemma lemma_bytes_to_uint16(xs: seq<uint8>, ys: seq<uint8>)
    requires bytes_to_uint16(xs) == bytes_to_uint16(ys)
    ensures xs == ys
  {
    assume false;
  }

  lemma lemma_bytes_uint16_to_nat(xs: seq<uint8>)
    ensures bytes_to_nat(xs) == uint16_to_nat(bytes_to_uint16(xs))
  {
    assume false;
  }

}
