include "NatSeqConversions.dfy"

module NatSeqExample {

  import opened uint8_32

  method Main() {
    var n := 49602234234;

    // Convert n to uint8 and uint32 sequences
    var smallSeq, largeSeq := Small.from_nat(n), Large.from_nat(n);

    Small.lemma_nat_seq_nat(n);
    Large.lemma_nat_seq_nat(n);
    assert Small.to_nat(smallSeq) == Large.to_nat(largeSeq) == n;

    // Extend smallSeq
    smallSeq := Small.seq_extend_multiple(smallSeq, E());
    assert Small.to_nat(smallSeq) == n;

    // Conversions between smallSeqExtended and largeSeq
    lemma_to_small(largeSeq);
    lemma_to_large(smallSeq);
    assert Small.to_nat(to_small(largeSeq)) == n;
    assert Large.to_nat(to_large(smallSeq)) == n;

    lemma_small_large_small(smallSeq);
    lemma_large_small_large(largeSeq);
    assert to_small(to_large(smallSeq)) == smallSeq;
    assert to_large(to_small(largeSeq)) == largeSeq;
  }

}
