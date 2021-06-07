lemma lemma_seq_slice_start<T>(intseq:seq<T>, j:int)
/* a sequence sliced from the first element to the jth element is
the same as that sequence sliced until the jth element*/
    requires 0<=j<|intseq|;
    ensures intseq[0..j]==intseq[..j];
{
}

lemma lemma_seq_slice_full_length<T>(intseq:seq<T>)
/* a sequence is the same as that sequence sliced until the end 
of that sequence's length */
    ensures intseq==intseq[..|intseq|];
{
}

lemma lemma_seq_shift_after_slicing<T>(sequence:seq<T>, j:int)
/* if a sequence is sliced after the first element, the new sequence's
elements' values are shifted down by 1 */
    requires 0<=j<|sequence|-1;
    ensures sequence[1..][j] == sequence[j+1];
{
}

lemma lemma_seq_slice_concatenation_is_original<T>(intseq:seq<T>, j:int)
/* a sequence that is sliced at the jth element concatenated with that same
sequence sliced from the jth element is equal to the original, unsliced sequence */
    requires 0<=j<|intseq|;
    ensures intseq[..j] + intseq[j..] == intseq;
{
}

lemma lemma_sequence_reduction<T>(s:seq<T>, b:nat)
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

lemma lemma_seq_concatenation_associative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
/* explains the associative nature of adding sequences*/
    ensures (a+b)+c == a+(b+c);
{
}

lemma lemma_subseq_concatenation<T>(s: seq<T>, left: int, middle: int, right: int)
/* a subsequence is the same as concatenating two subsequences: one from the leftmost
element until some element in the middle, and one from the middle element to the 
rightmost element */
    requires 0 <= left <= middle <= right <= |s|;
    ensures s[left..right] == s[left..middle] + s[middle..right];
{
}

lemma lemma_seq_equality<T>(a:seq<T>, b:seq<T>, len:int)
/* if sequence a and sequence b are of equall lengths and all of their
elements are equal, a and b are equal sequences */ 
    requires |a| == |b| == len;
    requires forall i {:trigger a[i]}{:trigger b[i]} :: 0 <= i < len ==> a[i] == b[i];
    ensures a == b;
{
    assert forall i :: 0 <= i < len ==> a[i] == b[i];
}

lemma lemma_seq_suffix<T>(s: seq<T>, prefix_length: int, index: int)
/* if a sequence is sliced after the a certain length, the new sequence's
elements' values are shifted down by that length*/
    requires 0 <= prefix_length <= index < |s|;
    ensures s[index] == s[prefix_length..][index - prefix_length];
{
}
