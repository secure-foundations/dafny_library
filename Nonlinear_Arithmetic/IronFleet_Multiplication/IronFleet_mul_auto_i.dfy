
/////REVISIT THIS FILE!!!

include "IronFleet_mul_auto_proofs_i.dfy"

module Math__mul_auto_i {

  import opened Math__mul_auto_proofs_i

  predicate mul_auto()
  {
    && (forall x:int, y:int {:trigger x * y} :: x * y == y * x)
    && (forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z)
    && (forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z)
  }

  lemma lemma_mul_auto()
    ensures  mul_auto()
  {
    lemma_mul_auto_commutes();
    lemma_mul_auto_distributes();
  }

  predicate t_mul_auto_le(x:int, y:int) { x <= y }

  lemma lemma_mul_auto_induction(x:int, f:int->bool)
    requires mul_auto() ==> f(0)
                          && (forall i {:trigger t_mul_auto_le(0, i)} :: t_mul_auto_le(0, i) && f(i) ==> f(i + 1))
                          && (forall i {:trigger t_mul_auto_le(i, 0)} :: t_mul_auto_le(i, 0) && f(i) ==> f(i - 1))
    ensures  mul_auto()
    ensures  f(x)
  {
    lemma_mul_auto_commutes();
    lemma_mul_auto_distributes();
    assert forall i {:trigger f(i)} :: t_mul_auto_le(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger f(i)} :: t_mul_auto_le(i, 0) && f(i) ==> f(i - 1);
    lemma_mul_induction_forall(f);
    assert f(x);
  }

  lemma lemma_mul_auto_induction_forall(f:int->bool)
    requires mul_auto() ==> f(0)
                          && (forall i {:trigger t_mul_auto_le(0, i)} :: t_mul_auto_le(0, i) && f(i) ==> f(i + 1))
                          && (forall i {:trigger t_mul_auto_le(i, 0)} :: t_mul_auto_le(i, 0) && f(i) ==> f(i - 1))
    ensures  mul_auto()
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    lemma_mul_auto_commutes();
    lemma_mul_auto_distributes();
    assert forall i {:trigger f(i)} :: t_mul_auto_le(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger f(i)} :: t_mul_auto_le(i, 0) && f(i) ==> f(i - 1);
    lemma_mul_induction_forall(f);
  }

} 