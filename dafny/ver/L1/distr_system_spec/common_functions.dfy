include "../../../spec/L1/types.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"


module EEACommonFunctions{
    import opened EEASpecTypes
    import opened EEAAuxiliaryFunctionsAndLemmas

    /**
     * @returns The union of all sets included in `sets`.
     */
    function setUnion<T(!new)>(sets:set<set<T>>):set<T>
    ensures forall e :: ((exists s | s in sets :: e in s) <==> e in setUnion(sets))
    {
        if sets == {} then
            {}
        else
            var s :| s in sets;
            s + setUnion(sets - {s})
    } 

    function setToSeq<T(!new)>(s:set<T>):seq<T>
    {
        if s == {} then
            []
        else
            var e :| e in s;
            setToSeq(s - {e}) +
            [e]
    }

    function seqToSet<T>(s:seq<T>): set<T>
    {
        set e | e in s
    } 

    predicate isMsgWithSignedPayload(m:QbftMessage)
    {
        || m.Proposal?
        || m.Prepare?
        || m.Commit?
        || m.RoundChange?
    }

    function recoverSignature(m:QbftMessage):Address
    requires isMsgWithSignedPayload(m)
    {
        if m.Proposal? then 
            recoverSignedProposalAuthor(m.proposalPayload)
        else if m.Prepare? then
            recoverSignedPrepareAuthor(m.preparePayload)
        else if m.Commit? then
            recoverSignedCommitAuthor(m.commitPayload)   
        else
            recoverSignedRoundChangeAuthor(m.roundChangePayload)                     
    }

    function signedProposalPayloads(
        s: set<QbftMessage>
    ): set<SignedProposal>
    {
        set m | && m in s 
                && m.Proposal?
              ::
                m.proposalPayload           
    }

    function signedRoundChangePayloads(
        s: set<QbftMessage>
    ): set<SignedRoundChange>
    {
        (set m | && m in s 
                && m.RoundChange?
              ::
                m.roundChangePayload)
        +
        setUnion(
                set m | && m in s 
                && m.Proposal?
              ::
                m.proposalJustification 
        )

    }    

    function signedPreparePayloads(
        s: set<QbftMessage>
    ): set<SignedPrepare>
    {
        (set m | && m in s 
                && m.Prepare?
              ::
                m.preparePayload)
        +
        setUnion(
                set m | && m in s 
                        && (
                            || m.Proposal?
                            || m.RoundChange?
                        )
              ::
                m.roundChangeJustification 
        )

    }     

    function getCommitSeals(msgs:set<QbftMessage>):set<Signature>
    {
        (set m,s |   && m in msgs
                    && m.NewBlock?
                    && s in m.block.header.commitSeals
                ::
                    s)
        +

        (set m,s |   && m in msgs
                    && m.Commit?
                    && m.commitPayload.unsignedPayload.commitSeal == s
                ::
                    s)
    }

    lemma lUniqueSeq<T>(s:seq<T>)
    requires isUniqueSequence(s)
    ensures |s| == |seqToSet(s)|
    {
        if s != []
        {
            var sseq := s[1..];
            lUniqueSeq(sseq);
            assert seqToSet(s) == seqToSet(sseq) + {s[0]};
        }
    }

    predicate isUniqueSequence<T(==)>(s:seq<T>) 
    {
        forall i,j |    && 0 <= i < |s| 
                        && 0 <= j < |s|
                        && i != j
                    ::
                        s[i] != s[j]
    }    

}