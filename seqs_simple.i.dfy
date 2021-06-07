lemma lemma_seq_slice_start(intseq:seq<int>, j:int)
/* a sequence sliced from the first element to the jth element is
the same as that sequence sliced until the jth element*/
    requires 0<=j<|intseq|;
    ensures intseq[0..j]==intseq[..j];
{
}

lemma lemma_seq_slice_full_length(intseq:seq<int>)
/* a sequence is the same as that sequence sliced until the end 
of that sequence's length */
    ensures intseq==intseq[..|intseq|];
{
}

lemma lemma_seq_shift_after_slicing_bool(boolseq:seq<bool>, j:int)
/* if a sequence is sliced after the first element, the new sequence's
elements' values are shifted down by 1 */
    requires 0<=j<|boolseq|-1;
    ensures boolseq[1..][j] == boolseq[j+1];
{
}

lemma lemma_seq_shift_after_slicing_int(intseq:seq<int>, j:int)
/* if a sequence is sliced after the first element, the new sequence's
elements' values are shifted down by 1 */
    requires 0<=j<|intseq|-1;
    ensures intseq[1..][j] == intseq[j+1];
{
}

lemma lemma_seq_slice_concatenation_is_original(intseq:seq<int>, j:int)
/* a sequence that is sliced at the jth element concatenated with that same
sequence sliced from the jth element is equal to the original, unsliced sequence */
    requires 0<=j<|intseq|;
    ensures intseq[..j] + intseq[j..] == intseq;
{
}

lemma lemma_sequence_reduction(s:seq<int>, b:nat)
/* explains sequence reduction */
    requires 0<b<|s|;
    ensures s[0..b][0..b-1] == s[0..b-1];
{
    var t := s[0..b];
    forall (i | 0<=i<b-1)
        ensures s[0..b][0..b-1][i] == s[0..b-1][i];
    {
    }
}

lemma lemma_seq_concatenation_associative(a:seq<int>, b:seq<int>, c:seq<int>)
/* explains the associative nature of adding sequences*/
    ensures (a+b)+c == a+(b+c);
{
}

lemma lemma_subseq_concatenation(s: seq<int>, left: int, middle: int, right: int)
/* a subsequence is the same as concatenating two subsequences: one from the leftmost
element until some element in the middle, and one from the middle element to the 
rightmost element */
    requires 0 <= left <= middle <= right <= |s|;
    ensures s[left..right] == s[left..middle] + s[middle..right];
{
}

lemma lemma_seq_equality(a:seq<int>, b:seq<int>, len:int)
/* if sequence a and sequence b are of equall lengths and all of their
elements are equal, a and b are equal sequences */ 
    requires |a| == |b| == len;
    requires forall i {:trigger a[i]}{:trigger b[i]} :: 0 <= i < len ==> a[i] == b[i];
    ensures a == b;
{
    assert forall i :: 0 <= i < len ==> a[i] == b[i];
}

lemma lemma_seq_suffix(s: seq<int>, prefix_length: int, index: int)
/* if a sequence is sliced after the a certain length, the new sequence's
elements' values are shifted down by that length*/
    requires 0 <= prefix_length <= index < |s|;
    ensures s[index] == s[prefix_length..][index - prefix_length];
{
}
