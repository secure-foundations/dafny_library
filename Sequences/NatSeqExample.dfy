include "NatSeq.dfy"
include "NatSeqConversions.dfy"

include "../Nonlinear_Arithmetic/DivMod.dfy"
include "../Nonlinear_Arithmetic/Power.dfy"

module uint8_32Example {

  import opened uint8_32

  import opened DivMod
  import opened Power

  method Main() {
    var n := 49602234234;

    // Convert n to uint8 and uint32 sequences
    var smallSeq, largeSeq := Small.from_nat(n), Large.from_nat(n);

    Small.lemma_nat_seq_nat(n);
    Large.lemma_nat_seq_nat(n);
    assert Small.to_nat(smallSeq) == Large.to_nat(largeSeq) == n;

    // Extend smallSeq
    var smallExtendedLen := |smallSeq| + E() - (|smallSeq| % E());
    lemma_sub_mod_noop_right(|smallSeq| + E(), |smallSeq|, E());
    lemma_mod_basics_auto();
    assert smallExtendedLen % E() == 0;

    Small.lemma_seq_nat_bound(smallSeq);
    lemma_power_increases_auto();
    var smallSeqExtended := Small.seq_extend(smallSeq, smallExtendedLen);
    assert Small.to_nat(smallSeqExtended) == n;

    // Conversions between smallSeqExtended and largeSeq
    lemma_to_small(largeSeq);
    lemma_to_large(smallSeqExtended);
    assert Small.to_nat(to_small(largeSeq)) == n;
    assert Large.to_nat(to_large(smallSeqExtended)) == n;

    lemma_small_large_small(smallSeqExtended);
    lemma_large_small_large(largeSeq);
    assert to_small(to_large(smallSeqExtended)) == smallSeqExtended;
    assert to_large(to_small(largeSeq)) == largeSeq;
  }

}
