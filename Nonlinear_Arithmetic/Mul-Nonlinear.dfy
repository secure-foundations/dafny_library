/* - <NuBuild AddDafnyFlag /proverOpt:O:smt.arith.nl=true/>
- WARNING: In general, you shouldn't need to call these directly.*/

module MulNonlinear {

  /* WARNING: Think three times before adding to this file, as nonlinear verification
  is highly unstable! */

  /* multiplying two positive integers will result in a positive integer */
  lemma lemma_mul_strictly_positive_helper(x:int, y:int)
  ensures (0 < x && 0 < y) ==> (0 < x*y)
  {}

  /* multiplying two nonzero numbers will never result in 0 as the poduct */
  lemma lemma_mul_nonzero_helper(x:int, y:int)
  ensures x*y != 0 <==> x != 0 && y != 0
  {}

  /* multiplication is associative */
  lemma lemma_mul_is_associative_helper(x:int, y:int, z:int)
  ensures x * (y * z) == (x * y) * z
  {}

  /* multiplication is distributive */
  lemma lemma_mul_is_distributive_add_helper(x:int, y:int, z:int)
  ensures x*(y + z) == x*y + x*z
  {}

  /* the product of two integers is greater than the value of each individual integer */
  lemma lemma_mul_ordering_helper(x:int, y:int)
  requires 0 < x
  requires 0 < y
  requires 0 <= x*y
  ensures x <= x*y && y <= x*y
  { }

  /* multiplying by a positive integer preserves inequality */
  lemma lemma_mul_strict_inequality_helper(x:int, y:int, z:int)
  requires x < y
  requires z > 0
  ensures  x*z < y*z
  {}

  /* the product of any integer and zero is zero */
  lemma lemma_mul_by_zero_is_zero_helper(x:int)
  ensures 0*x == 0
  ensures x*0 == 0
  { }

} 