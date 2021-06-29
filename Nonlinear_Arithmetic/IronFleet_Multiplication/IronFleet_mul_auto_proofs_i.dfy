include "IronFleet_mul_nonlinear_i.dfy"

module Math__mul_auto_proofs_i {

  import opened Math__mul_nonlinear_i

  lemma lemma_mul_induction_helper(f:int->bool, i:int)
    requires f(0)
    requires forall i {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures  f(i)
    decreases if i >= 0 then i else -i
  {
    if (i > 0)
    {
      assert f(i - 1) by {
        lemma_mul_induction_helper(f, i - 1);
      }
      var x := i - 1;
      assert f(x) ==> f(x + 1);
    }
    else if (i < 0)
    {
      assert f(i + 1) by {
        lemma_mul_induction_helper(f, i + 1);
      }
      var x := i + 1;
      assert f(x) ==> f(x - 1);
    }
  }

  lemma lemma_mul_induction_forall(f:int->bool)
    requires f(0)
    requires forall i {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    forall i ensures f(i) { lemma_mul_induction_helper(f, i); }
  }

  /* proves that multiplication is always commutative */
  lemma lemma_mul_auto_commutes()
    ensures  forall x:int, y:int {:trigger x * y} :: x * y == y * x
  {
    forall x:int, y:int
      ensures x * y == y * x
    {
      lemma_mul_induction_forall(i => x * i == i * x);
    }
  }

  /* proves the distributive property of multiplication when multiplying an interger
  by (x +/- 1) */
  lemma lemma_mul_auto_succ()
    ensures  forall x:int, y:int {:trigger (x + 1) * y} :: (x + 1) * y == x * y + y
    ensures  forall x:int, y:int {:trigger (x - 1) * y} :: (x - 1) * y == x * y - y
  {
    lemma_mul_auto_commutes();
    forall x:int, y:int
      ensures  (x + 1) * y == x * y + y
      ensures  (x - 1) * y == x * y - y
    {
      lemma_mul_is_distributive_add(y, x, 1);
      lemma_mul_is_distributive_add(y, x, -1);
    }
  }

  /* proves the distributive property of multiplication */
  lemma lemma_mul_auto_distributes()
    ensures  forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z
    ensures  forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z
  {
    lemma_mul_auto_succ();
    forall x:int, y:int, z:int
      ensures (x + y) * z == x * z + y * z
      ensures (x - y) * z == x * z - y * z
    {
      var f1 := i => (x + i) * z == x * z + i * z;
      var f2 := i => (x - i) * z == x * z - i * z;
      assert forall i {:trigger (x + (i + 1)) * z} :: (x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z;
      assert forall i {:trigger (x + (i - 1)) * z} :: (x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z;
      assert forall i {:trigger (x - (i + 1)) * z} :: (x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z;
      assert forall i {:trigger (x - (i - 1)) * z} :: (x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z;
      lemma_mul_induction_forall(f1);
      lemma_mul_induction_forall(f2);
      assert f1(y);
      assert f2(y);
    }
  }

} 