include "Mul-Nonlinear.dfy"
include "Mul-Internals.dfy"

module Mul {

  import opened Mul-Nonlinear
  import opened Mul-Internals

  /* calculates the product of two integers */
  function method mul(x:int, y:int) : int { x*y }

  /*****************************************************
  * Recursive definitions that can be handy for proving 
  * properties we can't or don't want to rely on nonlinear for
  *****************************************************/
 
  /* performs multiplication for positive integers using recursive addition */
  function method {:opaque} mul_pos(x:int, y:int) : int
    requires x >= 0
  {
    if x == 0 then 0
    else y + mul_pos(x - 1, y)
  }

  /* performs multiplication for both positive and negative integers */ 
  function method mul_recursive(x:int, y:int) : int
  {
    if x >= 0 then mul_pos(x, y)
    else -1*mul_pos(-1*x, y)
  }

  /* the common syntax of multiplication results in the same product as multiplication 
  through recursive addition */
  lemma lemma_mul_is_mul_recursive(x:int, y:int)
    ensures x * y == mul_recursive(x, y)
  {
    if (x >= 0) { lemma_mul_is_mul_pos(x, y); }
    if (x <= 0) { lemma_mul_is_mul_pos(-x, y); }
    lemma_mul_auto();
  }
  
  lemma lemma_mul_is_mul_recursive_auto()
    ensures forall x:int, y:int :: x * y == mul_recursive(x, y)
  {
    forall x:int, y:int
      ensures x * y == mul_recursive(x, y)
    {
      lemma_mul_is_mul_recursive(x, y);
    }
  }

  /* the common syntax of multiplying two positive integers results in the same product as 
  mul_pos, which is achieved by recursive addition */ 
  lemma lemma_mul_is_mul_pos(x:int, y:int)
    requires x >= 0
    ensures x * y == mul_pos(x, y)
  {
    reveal_mul_pos();
    lemma_mul_auto_induction(x, u => u >= 0 ==> u * y == mul_pos(u, y));
  }

  //-////////////////////////////////////////////////////////////////////////////
  //-
  //- Core lemmas, with named arguments.
  //-
  //-////////////////////////////////////////////////////////////////////////////

  /* ensures that the basic properties of multiplication, including the identity and zero properties */
  lemma lemma_mul_basics(x:int)
    ensures 0*x == 0
    ensures x*0 == 0
    ensures 1*x == x
    ensures x*1 == x
  {
  }

  lemma lemma_mul_basics_auto()
    ensures forall x:int {:trigger 0*x} :: 0*x == 0
    ensures forall x:int {:trigger x*0} :: x*0 == 0
    ensures forall x:int {:trigger 1*x} :: 1*x == x
    ensures forall x:int {:trigger x*1} :: x*1 == x
  {
  }

  /* multiplying any two nonzero integers will never result in 0 as the poduct */
  lemma lemma_mul_nonzero_auto()
    ensures forall x:int, y:int {:trigger x*y} :: x*y != 0 <==> x != 0 && y != 0
  {
    forall (x:int, y:int)
      ensures x*y != 0 <==> x != 0 && y != 0;
    {
      lemma_mul_nonzero(x,y);
    }
  }
  
  /* any integer multiplied by 0 results in a product of 0 */
  lemma lemma_mul_by_zero_is_zero_auto()
    ensures forall x: int {:trigger 0*x} {:trigger x*0} :: x*0 == 0*x == 0
  {
    forall x:int {:trigger 0*x} {:trigger x*0}
      ensures x*0 == 0*x == 0
    {
      lemma_mul_by_zero_is_zero(x);
    }
  }
  
  /* multiplication is always associative for all integers*/
  lemma lemma_mul_is_associative_auto()
    ensures forall x:int, y:int, z:int {:trigger x * (y * z)}{:trigger (x * y) * z} :: x * (y * z) == (x * y) * z
  {
    forall (x:int, y:int, z:int)
      ensures x * (y * z) == (x * y) * z
    {
      lemma_mul_is_associative(x,y,z);
    }
  }

  /* multiplcation is commutative */
  lemma lemma_mul_is_commutative(x:int, y:int)
    ensures x*y == y*x
  {
  }

  /* multiplication is always commutative for all integers */
  lemma lemma_mul_is_commutative_auto()
    ensures forall x:int, y:int {:trigger x*y} :: x*y == y*x
  {
  }

  /* the product of two positive integers is always greater than the individual value of either 
  multiplied integer */
  lemma lemma_mul_ordering_auto()
    ensures forall x:int, y:int {:trigger x*y} :: (0 < x && 0 < y && 0 <= x*y) ==> x <= x*y && y <= x*y
  {
    forall x:int, y:int | 0 < x && 0 < y && 0 <= x*y
        ensures x <= x*y && y <= x*y
    {
      lemma_mul_ordering(x, y);
    }
  }

  /* two integers that are multiplied by a positive number will maintain their numerical order */
  lemma lemma_mul_inequality(x:int, y:int, z:int)
    requires x <= y
    requires z >= 0
    ensures  x*z <= y*z
  {
    lemma_mul_auto_induction(z, u => u >= 0 ==> x * u <= y * u);
  }

  /* any two integers that are multiplied by a positive number will maintain their numerical order */
  lemma lemma_mul_inequality_auto()
    ensures  forall x:int, y:int, z:int {:trigger x*z, y*z} :: x <= y && z>=0 ==> x*z <= y*z
  {
    forall (x:int, y:int, z:int | x <= y && z>=0)
      ensures x*z <= y*z
    {
      lemma_mul_inequality(x, y, z);
    }
  }

  /* multiplying by a positive integer preserves inequality for all integers*/
  lemma lemma_mul_strict_inequality_auto()
    ensures  forall x:int, y:int, z:int {:trigger x*z, y*z} :: x < y && z>0 ==> x*z < y*z
  {
    forall (x:int, y:int, z:int | x < y && z>0)
      ensures x*z < y*z
    {
      lemma_mul_strict_inequality(x, y, z);
    }
  }

  /* the product of two bounded integers is less than or equal to the product of their upper bounds */
  lemma lemma_mul_upper_bound(x:int, x_bound:int, y:int, y_bound:int)
    requires x <= x_bound
    requires y <= y_bound
    requires 0<=x
    requires 0<=y
    ensures x*y <= x_bound * y_bound
  {
    lemma_mul_inequality(x, x_bound, y);
    lemma_mul_inequality(y, y_bound, x_bound);
  }

  // "use with caution" --> remove?
  //- This lemma is less precise than the non-strict version, since
  //- it uses two < facts to achieve only one < result. Thus, use it with
  //- caution -- it may be throwing away precision you'll require later.
  lemma lemma_mul_strict_upper_bound(x:int, x_bound:int, y:int, y_bound:int)
    requires x < x_bound
    requires y < y_bound
    requires 0<=x
    requires 0<=y
    ensures x*y < x_bound * y_bound
  {
    lemma_mul_auto_induction(x, u => 0 <= u ==> u * y <= u * y_bound);
    lemma_mul_auto_induction(y_bound, u => 1 <= u ==> x * u < x_bound * u);
  }

  // different than lemma_mul_inequality?
  /* any two integers that are multiplied by a positive number will maintain their numerical order */
  lemma lemma_mul_left_inequality(x:int, y:int, z:int)
    requires x > 0
    ensures y <= z ==> x*y <= x*z
    ensures y < z ==> x*y < x*z
  {
    lemma_mul_auto_induction(x, u => u > 0 ==> y <= z ==> u*y <= u*z);
    lemma_mul_auto_induction(x, u => u > 0 ==> y < z ==> u*y < u*z);
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, the numerical order of the 
  products x*z and y*z will also hold true for x and y alone */
  lemma lemma_mul_strict_inequality_auto_converse(x:int, y:int, z:int)
    requires x*z < y*z
    requires z >= 0
    ensures  x < y
  {
    lemma_mul_auto_induction(z, u => x * u < y * u && u >= 0 ==> x < y);
  }

  /* when any two integers, x and y, are each multiplied by a positive integer, z, the numerical order of 
  the products x*z and y*z will also hold true for x and y alone */
  lemma lemma_mul_strict_inequality_auto_converse_auto()
    ensures  forall x:int, y:int, z:int {:trigger x*z, y*z} :: x*z < y*z && z>=0 ==> x < y
  {
      forall (x:int, y:int, z:int | x*z < y*z && z>=0)
          ensures x < y;
      {
          lemma_mul_strict_inequality_auto_converse(x,y,z);
      }
  }

  /* when two integers, x and y, are each multiplied by a negative integer, z, the numerical order of the 
  products x*z and y*z will also hold true for x and y alone */
  lemma lemma_mul_inequaliy_converse(x:int, y:int, z:int)
    requires x*z <= y*z
    requires z > 0
    ensures  x <= y
  {
    lemma_mul_auto_induction(z, u => x * u <= y * u && u > 0 ==> x <= y);
  }

  /* when any two integers, x and y, are each multiplied by a negative integer, z, the numerical order of 
  the products x*z and y*z will also hold true for x and y alone */
  lemma lemma_mul_inequaliy_converse_auto()
    ensures  forall x:int, y:int, z:int {:trigger x*z, y*z} :: x*z <= y*z && z>0 ==> x <= y
  {
    forall (x:int, y:int, z:int | x*z <= y*z && z>0)
      ensures x <= y
    {
      lemma_mul_inequaliy_converse(x,y,z);
    }
  }

  lemma lemma_mul_equality_converse(x:int, y:int, z:int)
    requires x*z == y*z
    requires 0 < z
    ensures x == y
  {
    lemma_mul_auto_induction(z, u => x > y && 0 < u ==> x * u > y * u);
    lemma_mul_auto_induction(z, u => x < y && 0 < u ==> x * u < y * u);
  }
 
  lemma lemma_mul_is_distributive_add_auto()
    ensures forall x:int, y:int, z:int {:trigger x*(y + z)} :: x*(y + z) == x*y + x*z
  {
    forall (x:int, y:int, z:int)
      ensures x*(y + z) == x*y + x*z
    {
      lemma_mul_is_distributive_add(x,y,z);
    }
  }

  lemma lemma_mul_is_distributive_add_auto_other_way(x:int, y:int, z:int)
    ensures (y + z)*x == y*x + z*x
  {
    lemma_mul_auto();
  }

  lemma lemma_mul_is_distributive_sub(x:int, y:int, z:int)
    ensures x*(y - z) == x*y - x*z
  {
    lemma_mul_auto();
  }

  lemma lemma_mul_is_distributive_sub_auto()
    ensures forall x:int, y:int, z:int {:trigger x*(y - z)} :: x*(y - z) == x*y - x*z
  {
    forall (x:int, y:int, z:int)
      ensures x*(y - z) == x*y - x*z;
    {
      lemma_mul_is_distributive_sub(x,y,z);
    }
  }

  /* proves the distributive nature of multiplication*/
  lemma lemma_mul_is_distributive(x:int, y:int, z:int)
    ensures x*(y + z) == x*y + x*z
    ensures x*(y - z) == x*y - x*z
    ensures (y + z)*x == y*x + z*x
    ensures (y - z)*x == y*x - z*x
    ensures x*(y + z) == (y + z)*x
    ensures x*(y - z) == (y - z)*x
    ensures x*y == y*x
    ensures x*z == z*x
  {
    lemma_mul_auto();
  }

  lemma lemma_mul_is_distributive_auto()
    ensures forall x:int, y:int, z:int {:trigger x*(y + z)} :: x*(y + z) == x*y + x*z
    ensures forall x:int, y:int, z:int {:trigger x*(y - z)} :: x*(y - z) == x*y - x*z
    ensures forall x:int, y:int, z:int {:trigger (y + z)*x} :: (y + z)*x == y*x + z*x
    ensures forall x:int, y:int, z:int {:trigger (y - z)*x} :: (y - z)*x == y*x - z*x
  {
    lemma_mul_is_distributive_add_auto();
    lemma_mul_is_distributive_sub_auto();
    lemma_mul_is_commutative_auto();
  }

  lemma lemma_mul_strictly_positive_auto()
    ensures forall x:int, y:int {:trigger x*y} :: (0 < x && 0 < y) ==> (0 < x*y)
  {
    forall (x:int, y:int | 0 < x && 0 < y)
      ensures 0 < x*y
    {
      lemma_mul_strictly_positive(x,y);
    }
  }

  /* multiplying a positive integer by an integer greater than 1 will result in a product that 
  is greater than the original integer */
  lemma lemma_mul_strictly_increases(x:int, y:int)
    requires 1 < x
    requires 0 < y
    ensures y < x*y
  {
    lemma_mul_auto_induction(x, u => 1 < u ==> y < u * y);
  }

  lemma lemma_mul_strictly_increases_auto()
    ensures forall x:int, y:int {:trigger x*y} :: (1 < x && 0 < y) ==> (y < x*y)
  {
    forall (x:int, y:int | 1 < x && 0 < y)
      ensures y < x*y
    {
      lemma_mul_strictly_increases(x,y);
    }
  }

  /* multiplying an integer by a positive integer will result in a product thhat is greater than or
  equal to the original integer */
  lemma lemma_mul_increases(x:int, y:int)
    requires 0<x
    requires 0<y
    ensures y <= x*y
  {
    lemma_mul_auto_induction(x, u => 0 < u ==> y <= u * y);
  }

  lemma lemma_mul_increases_auto()
    ensures forall x:int, y:int {:trigger x*y} :: (0 < x && 0 < y) ==> (y <= x*y)
  {
    forall (x:int, y:int | 0 < x && 0 < y)
      ensures y <= x*y
    {
      lemma_mul_increases(x,y);
    }
  }

  /* multiplying two positive numbers will result in a positive product */
  lemma lemma_mul_nonnegative(x:int, y:int)
    requires 0 <= x
    requires 0 <= y
    ensures  0 <= x*y
  {
    lemma_mul_auto_induction(x, u => 0 <= u ==> 0 <= u * y);
  }
  
  lemma lemma_mul_nonnegative_auto()
    ensures forall x:int, y:int {:trigger x*y} :: 0 <= x && 0 <= y ==> 0 <= x*y
  {
    forall (x:int, y:int | 0 <= x && 0 <= y)
      ensures 0 <= x*y
    {
      lemma_mul_nonnegative(x,y);
    }
  }

  lemma lemma_mul_unary_negation(x:int, y:int)
    ensures (-x)*y == -(x*y) == x*(-y)
  {
    lemma_mul_auto_induction(x, u => (-u)*y == -(u*y) == u*(-y));
  }

  lemma lemma_mul_unary_negation_auto()
    ensures forall x:int, y:int {:trigger (-x)*y}{:trigger x*(-y)} :: (-x)*y == -(x*y) == x*(-y)
  {
    forall (x:int, y:int) 
      ensures (-x)*y == -(x*y) == x*(-y)
    {
      lemma_mul_unary_negation(x,y);
    }
  }

  lemma lemma_mul_one_to_one(m:int, x:int, y:int)
    requires m!=0
    requires m*x == m*y
    ensures x == y
  {
    lemma_mul_auto_induction(m, u => x > y && 0 < u ==> x * u > y * u);
    lemma_mul_auto_induction(m, u => x > y && 0 > u ==> x * u < y * u);
    lemma_mul_auto_induction(m, u => x < y && 0 < u ==> x * u < y * u);
    lemma_mul_auto_induction(m, u => x < y && 0 > u ==> x * u > y * u);
  }

  lemma lemma_mul_one_to_one_auto()
    ensures forall m:int, x:int, y:int {:trigger m*x, m*y} :: (m!=0 && m*x == m*y) ==> x==y
  {
    forall (m:int, x:int, y:int | m!=0 && m*x == m*y)
      ensures x==y
    {
      lemma_mul_one_to_one(m, x, y);
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // The big properties bundle. This can be a little dangerous, because
  // it may produce a trigger storm. Whether it does seems to depend on
  // how complex the expressions being mul'ed are. If that happens,
  // fall back on specifying an individiual _forall lemma or use
  // lemma_mul_auto/lemma_mul_auto_induction.
  //
  //////////////////////////////////////////////////////////////////////////////

  /* includes all properties of multiplication */
  lemma lemma_mul_properties()
    ensures forall x:int, y:int {:trigger x*y} :: x*y == y*x
    ensures forall x:int {:trigger x*1}{:trigger 1*x} :: x*1 == 1*x == x
    ensures forall x:int, y:int, z:int {:trigger x*z, y*z} :: x < y && z > 0 ==> x*z < y*z
    ensures forall x:int, y:int, z:int {:trigger x*z, y*z} :: x <= y && z >= 0 ==> x*z <= y*z
    ensures forall x:int, y:int, z:int {:trigger x*(y + z)} :: x*(y + z) == x*y + x*z
    ensures forall x:int, y:int, z:int {:trigger x*(y - z)} :: x*(y - z) == x*y - x*z
    ensures forall x:int, y:int, z:int {:trigger (y + z)*x} :: (y + z)*x == y*x + z*x
    ensures forall x:int, y:int, z:int {:trigger (y - z)*x} :: (y - z)*x == y*x - z*x
    ensures forall x:int, y:int, z:int {:trigger x*(y*z)}{:trigger (x*y)*z} :: x*(y*z) == (x*y)*z
    ensures forall x:int, y:int {:trigger x*y} :: x*y != 0 <==> x != 0 && y != 0
    ensures forall x:int, y:int {:trigger x*y} :: 0 <= x && 0 <= y ==> 0 <= x*y
    ensures forall x:int, y:int {:trigger x*y} :: 0 < x && 0 < y && 0 <= x*y ==> x <= x*y && y <= x*y
    ensures forall x:int, y:int {:trigger x*y} :: (1 < x && 0 < y) ==> (y < x*y)
    ensures forall x:int, y:int {:trigger x*y} :: (0 < x && 0 < y) ==> (y <= x*y)
    ensures forall x:int, y:int {:trigger x*y} :: (0 < x && 0 < y) ==> (0 < x*y)
  {
    lemma_mul_strict_inequality_auto();
    lemma_mul_inequality_auto();
    lemma_mul_is_distributive_auto();
    lemma_mul_is_associative_auto();
    lemma_mul_ordering_auto();
    lemma_mul_nonzero_auto();
    lemma_mul_nonnegative_auto();
    lemma_mul_strictly_increases_auto();
    lemma_mul_increases_auto();
  }

  /* multiplying two negative integers, -a and -b, is equivalent to multiplying a and b */
  lemma lemma_mul_cancels_negatives(a:int, b:int)
    ensures a*b == (-a)*(-b);
  {
    lemma_mul_properties();
  }

} 