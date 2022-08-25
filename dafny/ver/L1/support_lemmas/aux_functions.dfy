include "../../../spec/L1/types.dfy"
include "../distr_system_spec/common_functions.dfy"
include "../distr_system_spec/network.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"
include "../../../spec/L1/node.dfy"
include "../distr_system_spec/distributed_system.dfy"
include "../../common/sets.dfy"
include "instrumented_specs.dfy"
include "axioms.dfy"
include "../theorems_defs.dfy"


module L1_AuxFunctionsProof
{
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_CommonFunctions
    import opened L1_Spec
    import opened HelperLemmasSets
    import opened L1_DistributedSystem
    import opened L1_InstrumentedSpecs  
    import opened L1_Axioms
    import opened L1_TheoremsDefs


    predicate adversaryTakesStep(
        s:  InstrDSState, 
        s': InstrDSState        
    )
    {
        && validInstrDSState(s)
        && InstrDSNextSingle(s, s')
        &&
            (exists messagesSentByTheNodes,
                    messagesReceivedByTheNodes,
                    node ::
                    
                    && InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
                    && !isInstrNodeHonest(s, node))
    }


    predicate isNodeThatTakesStep(
        s : InstrDSState, 
        s': InstrDSState,
        n : Address  
    )
    {
        && validInstrDSState(s)
        && InstrDSNextSingle(s, s')
        &&
            (exists messagesSentByTheNodes,
                    messagesReceivedByTheNodes
                    ::
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n))
    } 


    predicate nodeTakesStep(
        s:  InstrDSState, 
        s': InstrDSState,
        n : Address    
    )
    {
        && validInstrDSState(s)
        && InstrDSNextSingle(s, s')
        && n in s.nodes
        && n in s'.nodes
        &&
            (exists messagesSentByTheNodes,
                    messagesReceivedByTheNodes
                    ::
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n))
    }    

    predicate nodeSetDoesNotChange(
        s:InstrDSState, 
        s': InstrDSState
    ) 
    {
        s.nodes.Keys == s'.nodes.Keys
    }    

    predicate honestNodesDoNotChange
    (
        s:  InstrDSState, 
        s': InstrDSState
    )
    {
        getInstrDSStateHonestNodes(s) == getInstrDSStateHonestNodes(s') 
    } 

    function fromMultisetToSet<T(!new)>(m:multiset<T>): set<T>
    ensures forall e :: e in m <==> e in fromMultisetToSet(m)
    {
        set e | e in m
    }    

    function fromMultisetQbftMessagesWithRecipientToSetOfMessages(
        s: multiset<QbftMessageWithRecipient>
    ) : set<QbftMessage>
    {
        set m | m in s :: m.message
    }
    
    function allMessagesSentBy(s:set<QbftMessage>, n:Address): set<QbftMessage>
    {
        set m | && m in s 
                && isMsgWithSignedPayload(m)
                && recoverSignature(m) == n
    }    

    function allMessagesSentTo(
        e: Network,
        n: Address
    ) : set<QbftMessage>
    {
        set m | m in e.allMessagesSent && m.recipient == n :: m.message
    }


    function allMessagesSentWithoutRecipient(
        e: Network
    ): set<QbftMessage>
    {
        set m | m in e.allMessagesSent :: m.message
    }    


    function allMesssagesSentIncSentToItselfWithoutRecipient(
        s: InstrDSState
    ) : set<QbftMessage>
    {
        (
            allMessagesSentWithoutRecipient(s.environment)
        )
            +
        setUnion
        (
            set n:Address |
                        && n in s.nodes
                        && isInstrNodeHonest(s, n)
                    ::
                        s.nodes[n].messagesSentToItself
        )
    }  

    lemma lemmaAllMesssagesSentIncSentToItselfWithoutRecipient 
    (
        s: InstrDSState
    ) 
    ensures  allMessagesSentWithoutRecipient(s.environment) <= allMesssagesSentIncSentToItselfWithoutRecipient(s)
    ensures forall n | n in s.nodes && isInstrNodeHonest(s, n) :: s.nodes[n].messagesSentToItself <= allMesssagesSentIncSentToItselfWithoutRecipient(s)
    { }

    datatype SignedPayload = 
        | SignedProposalPayload(
            signedProposalPayload: SignedProposal
        )   
        | SignedPreparePayload(
            signedPreparePayload: SignedPrepare
        )   
        | SignedCommitPayload(
            signedCommitPayload: SignedCommit
        )           
        | SignedRoundChangePayload(
            signedRoundChangePayload: SignedRoundChange
        )   

    function recoverSignedPayloadSignature(m:SignedPayload):Address
    {
        if m.SignedProposalPayload? then 
            recoverSignedProposalAuthor(m.signedProposalPayload)
        else if m.SignedPreparePayload? then
            recoverSignedPrepareAuthor(m.signedPreparePayload)
        else if m.SignedCommitPayload? then
            recoverSignedCommitAuthor(m.signedCommitPayload)   
        else
            recoverSignedRoundChangeAuthor(m.signedRoundChangePayload)                     
    }        

    function getSignedPayload(m:QbftMessage): SignedPayload
    requires isMsgWithSignedPayload(m)
    {
        if m.Proposal? then
            SignedProposalPayload(m.proposalPayload)
        else if m.Prepare? then
            SignedPreparePayload(m.preparePayload)
        else if m.Commit? then
            SignedCommitPayload(m.commitPayload)
        else
            SignedRoundChangePayload(m.roundChangePayload)
    }            

    function getSetOfSignedPayloads(s:set<QbftMessage>): set<SignedPayload>            
    {
        var s1 := set m | 
                && m in s 
                && isMsgWithSignedPayload(m)
            ::
            getSignedPayload(m); //+ 

        var s2 := set m | 
                    && m in s
                    && m.Proposal?
                ::
                    m.proposalJustification;
        
        var s3 := setUnion(s2);

        var s4 := set m | m in s3 :: SignedRoundChangePayload(m);

        var s5 := set m | 
                    && m in s
                    && (
                        || m.Proposal?
                        || m.RoundChange?
                    )
                ::
                    m.roundChangeJustification;        
 
        var s7 := setUnion(s5);

        var s8 := set m | m in s7 :: SignedPreparePayload(m);             

        s1 + s4 + s8
    }

    lemma lemmaGetSetOfSignedPayloads()
    ensures forall s:set<QbftMessage>::
        getSetOfSignedPayloads(s) == 
        (set m | 
            && m in s 
            && isMsgWithSignedPayload(m)
            ::
            if m.Proposal? then
                SignedProposalPayload(m.proposalPayload)
            else if m.Prepare? then
                SignedPreparePayload(m.preparePayload)
            else if m.Commit? then
                SignedCommitPayload(m.commitPayload)
            else
                SignedRoundChangePayload(m.roundChangePayload))
        +
        (
            set m | 
                && m in setUnion(set m' | 
                                    && m' in s
                                    && m'.Proposal?
                                ::
                                    m'.proposalJustification)
                ::
                    SignedRoundChangePayload(m)
        )  +
        (
            set m | 
                && m in setUnion(set m' | 
                                    && m' in s
                                    && (
                                        || m'.Proposal?
                                        || m'.RoundChange?
                                    )
                                ::
                                    m'.roundChangeJustification)
                ::
                    SignedPreparePayload(m)
        )          
    {  }     

    lemma lemmaExtractSignedPreparesEx(
        S: set<QbftMessage>,
        pm: SignedPrepare,
        sender: Address
    )
    requires pm in  extractSignedPreparesEx(S)
    requires sender == recoverSignedPrepareAuthor(pm)
    ensures SignedPreparePayload(pm) in getSetOfSignedPayloads(S)
    ensures SignedPreparePayload(pm) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S), sender)
    {
        lemmaSignedPrepare();
    }

    function extractSignedRoundChangesEx(messages:set<QbftMessage>): set<SignedRoundChange>
    {
        var s1 := set m | && m in messages
                && m.RoundChange?
            ::
                m.roundChangePayload; 

        var s2 := set m |  && m in messages
                           && m.Proposal?
                ::
                    m.proposalJustification; 
        var s3 := setUnion(s2);
        s1 + s3
    }    

    lemma lemmaExtractSignedRoundChangeEx(
        S: set<QbftMessage>,
        rc: SignedRoundChange,
        sender: Address
    )
    requires rc in  extractSignedRoundChangesEx(S)
    requires sender == recoverSignedRoundChangeAuthor(rc)
    ensures SignedRoundChangePayload(rc) in getSetOfSignedPayloads(S)
    ensures SignedRoundChangePayload(rc) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S), sender)
    {
        lemmaSignedRoundChange();
    }

    lemma lemmaGetSetOfSignedPayloadsONSets(
        A: set<QbftMessage>,
        B: set<QbftMessage>,
        C: set<QbftMessage>
    )
    requires A == B + C 
    ensures getSetOfSignedPayloads(A) == getSetOfSignedPayloads(B) + getSetOfSignedPayloads(C)
    {

    }

    lemma lemmaGetSetOfSignedPayloadsONSetsFilter(
        A: set<QbftMessage>,
        B: set<QbftMessage>,
        C: set<QbftMessage>,
        n: Address
    )
    requires A == B + C 
    ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(A), n) == 
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(B), n) + filterSignedPayloadsByAuthor(getSetOfSignedPayloads(C), n)
    {

    }    


    lemma lemmaGetSetOfSignedPayloadsONSetsFour(
        A: set<QbftMessage>,
        B: set<QbftMessage>,
        C: set<QbftMessage>,
        D: set<QbftMessage>
    )
    requires A == B + C + D
    ensures getSetOfSignedPayloads(A) == getSetOfSignedPayloads(B) + getSetOfSignedPayloads(C) + getSetOfSignedPayloads(D)
    {

    }    

    lemma lemmaGetSetOfSignedPayloadsONSetsSetUnion(
        A: set<QbftMessage>,
        B: set<set<QbftMessage>>
    )
    requires A == setUnion(B)
    ensures getSetOfSignedPayloads(A) == setUnion(set b | b in B :: getSetOfSignedPayloads(b))
    {
        if B == {}
        {
            assert getSetOfSignedPayloads(A) == setUnion(set b | b in B :: getSetOfSignedPayloads(b));
        }
        else {
            var b: set<QbftMessage> :| b in B;
            var B':set<set<QbftMessage>> := B - {b};
            var A' := setUnion(B');
            lemmaGetSetOfSignedPayloadsONSetsSetUnion(A', B');
            assert A == setUnion(B') + b;
            lemmaGetSetOfSignedPayloadsONSets(A, setUnion(B'), b);
            assert getSetOfSignedPayloads(A) == getSetOfSignedPayloads(setUnion(B')) + getSetOfSignedPayloads(b);
            assert getSetOfSignedPayloads(A) == setUnion(set b | b in B :: getSetOfSignedPayloads(b));
        }
    }

    lemma lemmaGetSetOfSignedPayloadsONSetsSetUnionFilter(
        A: set<QbftMessage>,
        B: set<set<QbftMessage>>,
        n: Address
    )
    requires A == setUnion(B)
    ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(A), n) == setUnion(set b | b in B :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(b),n))
    {
        lemmaGetSetOfSignedPayloadsONSetsSetUnion(A, B);
        if B == {}
        {
            assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(A), n) == setUnion(set b | b in B :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(b),n));
        }
        else {
            var b: set<QbftMessage> :| b in B;
            var B':set<set<QbftMessage>> := B - {b};
            var A' := setUnion(B');
            lemmaGetSetOfSignedPayloadsONSetsSetUnionFilter(A', B', n);
            assert A == setUnion(B') + b;
            lemmaGetSetOfSignedPayloadsONSetsFilter(A, setUnion(B'), b, n);
        }
    }    

    lemma lemmaOnGetSetOfSignedPayloadsOfASetIncludesSignedPreparePyloadOfMemberOfTheSet(
        S: set<QbftMessage>,
        m: QbftMessage,
        sp: SignedPayload
    )
    requires || m.Prepare?
    requires sp == SignedPreparePayload(m.preparePayload)
    requires m in S 
    ensures sp in getSetOfSignedPayloads(S)
    {}

    lemma lemmaOnFilterSignedPayloadsByAuthorOfGetSetOfSignedPayloadsOfASetIncludesSignedPreparePyloadOfMemberOfTheSet(
        S: set<QbftMessage>,
        m: QbftMessage,
        sp: SignedPayload,
        sender: Address
    )
    requires || m.Prepare?
    requires sp == SignedPreparePayload(m.preparePayload)
    requires sender == recoverSignature(m)
    requires m in S 
    ensures sp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S), sender)
    {
        lemmaSignedPrepare();
    }   

    lemma lemmaOnFilterSignedPayloadsByAuthorOfGetSetOfSignedPayloadsOfASetIncludesSignedCommitPyloadOfMemberOfTheSet(
        S: set<QbftMessage>,
        m: QbftMessage,
        sp: SignedPayload,
        sender: Address
    )
    requires || m.Commit?
    requires sp == SignedCommitPayload(m.commitPayload)
    requires sender == recoverSignature(m)
    requires m in S 
    ensures sp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S), sender)
    {
        lemmaSignedCommit();
    }        

    lemma lemmaAllMesssagesSentIncSentToItselfWithoutRecipientFGFilter
    (
        s: InstrDSState,
        n: Address
    )   
    ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n) ==
    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) + 
    setUnion(set n' | n' in s.nodes && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n))
    {
        lemmaGetSetOfSignedPayloadsONSetsSetUnionFilter(
            setUnion(set n' | n' in s.nodes && isInstrNodeHonest(s, n') :: s.nodes[n'].messagesSentToItself),
            set n' | n' in s.nodes && isInstrNodeHonest(s, n') :: s.nodes[n'].messagesSentToItself,
            n
        );

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(setUnion(set n' | n' in s.nodes && isInstrNodeHonest(s, n') :: s.nodes[n'].messagesSentToItself)), n) ==
                setUnion(set n' | n' in s.nodes && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n));

        lemmaGetSetOfSignedPayloadsONSetsFilter(
            allMesssagesSentIncSentToItselfWithoutRecipient(s),
            allMessagesSentWithoutRecipient(s.environment),
            setUnion(set n' | n' in s.nodes && isInstrNodeHonest(s, n') :: s.nodes[n'].messagesSentToItself),
            n
        );
        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n) == 
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) + 
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(setUnion(set n' | n' in s.nodes && isInstrNodeHonest(s, n') :: s.nodes[n'].messagesSentToItself)), n) ;
    }

    function filterSignedPayloadsByAuthor(
        s: set<SignedPayload>,
        a: Address
    ):
    set<SignedPayload>
    {
        set m | m in s && recoverSignedPayloadSignature(m) == a
    }

    function filterSignedCommitSealByAuthor(
        s: set<Signature>,
        a: Address,
        h: Hash
    ):
    set<Signature>
    {
        set m | m in s && recoverSignedHashAuthor(h, m) == a
    }    

    function getSetOfSignedPreparePayloads(s:set<SignedPrepare>): set<SignedPayload>               
    {
        set m | 
                && m in s 
            ::
            SignedPreparePayload(m) 
    }    

    function getSetOfSignedPrepareSenders(msgs: set<SignedPrepare>):set<Address>
    {
        set m | m in msgs
            ::
                recoverSignedPrepareAuthor(m)
    }    

    function getSetOfSenders(msgs: set<QbftMessage>):set<Address>
    {
        set m | && m in msgs
                && isMsgWithSignedPayload(m)
            ::
                recoverSignature(m)
    }    

    function getAllMessagesSentByTheNode(
        s: InstrDSState,
        n: Address
    ): set<QbftMessage>
    requires n in s.nodes
    {
        fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent) + s.nodes[n].messagesSentToItself
    }

    function getAllMessagesSentByInsrNodeState(
        s: InstrNodeState
    ): set<QbftMessage>
    {
        fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent) + s.messagesSentToItself
    }    

    lemma lemmaConsistentBlockchainIsSymmetric()
    ensures forall bc1, bc2 :: consistentBlockchains(bc1, bc2) <==> consistentBlockchains(bc2, bc1)
    {

    }    

    predicate areBlocksTheSameExceptForTheCommitSeals(b1:Block, b2:Block)
    {
        b1 == b2.(header := b2.header.(commitSeals := b1.header.commitSeals))   
    }

    predicate areBlocksTheSameExceptForTheCommitSealsAndRound(b1:Block, b2:Block)
    {
        b1 == b2.(header := b2.header.(commitSeals := b1.header.commitSeals, roundNumber := b1.header.roundNumber))   
    }    

    predicate areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1:Blockchain, bc2:Blockchain)
    {
        && |bc1| == |bc2|
        && (forall i | 0 <= i < |bc1| :: areBlocksTheSameExceptForTheCommitSealsAndRound(bc1[i], bc2[i]))  
    }  

    lemma lemmaOnFromBlockchainToRawBlockchainEqualityImpliesBlockchainsAreTheSameExceptForTheCommitSealsAndRound(bc1: Blockchain, bc2: Blockchain)
    requires fromBlockchainToRawBlockchain(bc1) == fromBlockchainToRawBlockchain(bc2)
    ensures areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1, bc2)
    {
        var bc1' := fromBlockchainToRawBlockchain(bc1);
        var bc2' := fromBlockchainToRawBlockchain(bc2);

        assert |bc1'| == |bc2'| == |bc1| == |bc2|;
        forall i | 0 <= i < |bc1|
        ensures areBlocksTheSameExceptForTheCommitSealsAndRound(bc1[i], bc2[i]);
        {
            assert bc1'[i] == fromBlockToRawBlock(bc1[i]);
            assert bc2'[i] == fromBlockToRawBlock(bc2[i]);
            assert areBlocksTheSameExceptForTheCommitSealsAndRound(bc1[i], bc2[i]);
        }
    }

    lemma lemmaOnFromBlockchainToRawBlockchainPrefixImpliesBlockchainsTruncatedToTheSameLengthAreTheSameExceptForTheCommitSealsAndRound(bc1: Blockchain, bc2: Blockchain)
    requires fromBlockchainToRawBlockchain(bc1) <= fromBlockchainToRawBlockchain(bc2)
    ensures areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1, bc2[..|bc1|])
    ensures fromBlockchainToRawBlockchain(bc1) == fromBlockchainToRawBlockchain(bc2[..|bc1|])
    ensures areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1, bc2[..|bc1|])
    {
        var bc1' := fromBlockchainToRawBlockchain(bc1);
        var bc2' := fromBlockchainToRawBlockchain(bc2);

        assert |bc1'| == |bc1|;
        assert |bc2'| == |bc2|;

        forall i | 0 <= i < |bc1|
        ensures areBlocksTheSameExceptForTheCommitSealsAndRound(bc1[i], bc2[i]);
        {
            assert bc1'[i] == fromBlockToRawBlock(bc1[i]);
            assert bc2'[i] == fromBlockToRawBlock(bc2[i]);
            assert areBlocksTheSameExceptForTheCommitSealsAndRound(bc1[i], bc2[i]);
        }
    }

    lemma lemmaOnFromBlockchainToRawBlockchainIImpliesValidatorsEquality(bc1: Blockchain, bc2: Blockchain)
    requires    || fromBlockchainToRawBlockchain(bc1) == fromBlockchainToRawBlockchain(bc2)
                || areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1, bc2)
                || areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc2, bc1)
    ensures validators(bc1) == validators(bc2)
    {
        lemmaOnFromBlockchainToRawBlockchainEqualityImpliesBlockchainsAreTheSameExceptForTheCommitSealsAndRound(bc1, bc2);
    }    

    lemma {:fuel validators,0,0} lemmaOnFromBlockchainToRawBlockchainEquivalencePreservesValidProposalJustification(
        bc1: Blockchain, 
        bc2: Blockchain, 
        pm: QbftMessage)
    requires    || fromBlockchainToRawBlockchain(bc1) == fromBlockchainToRawBlockchain(bc2)
                || areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1, bc2)
                || areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc2, bc1)
    requires pm.Proposal?
    requires proposerPrecondition(bc1)
    requires proposerPrecondition(bc2)
    requires |bc1| > 1 ==> isUniqueSequence(validators(bc1[..|bc1|-1]))
    requires isValidProposalJustification(pm, bc1)
    ensures isValidProposalJustification(pm, bc2);
    ensures validators(bc1) == validators(bc2)
    {
        lemmaOnFromBlockchainToRawBlockchainEqualityImpliesBlockchainsAreTheSameExceptForTheCommitSealsAndRound(bc1, bc2);
        lemmaOnFromBlockchainToRawBlockchainIImpliesValidatorsEquality(bc1, bc2);
        assert |bc1| == |bc2|;
        lemmaOnFromBlockchainToRawBlockchainPrefixImpliesBlockchainsTruncatedToTheSameLengthAreTheSameExceptForTheCommitSealsAndRound(bc1[..|bc1|-1], bc1);
        lemmaOnFromBlockchainToRawBlockchainPrefixImpliesBlockchainsTruncatedToTheSameLengthAreTheSameExceptForTheCommitSealsAndRound(bc2[..|bc2|-1], bc2);
        lemmaOnFromBlockchainToRawBlockchainIImpliesValidatorsEquality(bc1[..|bc1|-1], bc2[..|bc2|-1]);
        assert validators(bc1) == validators(bc2);
        assert validators(bc1[..|bc1|-1]) == validators(bc2[..|bc2|-1]);
        assert proposer(pm.proposalPayload.unsignedPayload.round,bc1) == proposer(pm.proposalPayload.unsignedPayload.round,bc2);
        forall b : Block
        ensures validators(bc1  + [b]) == validators(bc2  + [b]);
        {
            assert areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1  + [b], bc2  + [b]);
            lemmaOnFromBlockchainToRawBlockchainIImpliesValidatorsEquality(bc1  + [b], bc2  + [b]);
        }
        assert forall b :: validateEthereumBlock(bc1, b) == validateEthereumBlock(bc2, b);
        assert forall b :: 
            validateNonPreparedBlock(b,bc1,pm.proposalPayload.unsignedPayload.round) <==> validateNonPreparedBlock(b,bc2,pm.proposalPayload.unsignedPayload.round);
    }       

    lemma lemmaFromBlockchainToRawBlockchainEquivalencePreservesValidNewBlock(b: Block, bc1: Blockchain, bc2: Blockchain)
    requires || fromBlockchainToRawBlockchain(bc1) == fromBlockchainToRawBlockchain(bc2)
             || areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1, bc2)
             || areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc2, bc1)
    ensures  ValidNewBlock(bc1, b) <==> ValidNewBlock(bc2, b)
    { }

    lemma lemmaAddBlocksThatAreTheSameExceptForCommitSealsAndRoundNumberToBlockchainsThatAreTheSameExceptForCommitSealsAndRoundNumberPreservesFromBlockchainToRawBlockchainEquivalence(
        b1: Block,
        b2: Block,
        bc1: Blockchain,
        bc2: Blockchain
    )
    requires areBlocksTheSameExceptForTheCommitSealsAndRound(b1, b2)
    requires areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1, bc2)
    ensures fromBlockchainToRawBlockchain(bc1 + [b1]) == fromBlockchainToRawBlockchain(bc2 + [b2])
    {
        lemmaOnFromBlockchainToRawBlockchainEqualityImpliesBlockchainsAreTheSameExceptForTheCommitSealsAndRound(bc1, bc2);
        assert areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1, bc2);
    }

    lemma lemmaAreBlocksTheSameExceptForTheCommitSealsAndRoundIsReflexiveAndAreBlocksTheSameExceptForTheCommitSealsAndRoundAndFromBlockchainToRawBlockchainEquivalenceAreEquivalent()
    ensures forall bc1, bc2 :: areBlocksTheSameExceptForTheCommitSealsAndRound(bc1,bc2)<==> areBlocksTheSameExceptForTheCommitSealsAndRound(bc2,bc1)
    ensures forall bc1, bc2 :: areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1,bc2) <==> fromBlockchainToRawBlockchain(bc1) == fromBlockchainToRawBlockchain(bc2)
    {
        forall bc1: Blockchain, bc2: Blockchain
        ensures areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1,bc2) <==> fromBlockchainToRawBlockchain(bc1) == fromBlockchainToRawBlockchain(bc2)
        {
            if fromBlockchainToRawBlockchain(bc1) == fromBlockchainToRawBlockchain(bc2)
            {
                lemmaOnFromBlockchainToRawBlockchainEqualityImpliesBlockchainsAreTheSameExceptForTheCommitSealsAndRound(bc1, bc2);
            }
            
        }
    }    

    // 2s 3.2.0
    lemma lemmaPrefixesOfConsistentBlockchainsAreConsistenAndIfOfTheSameLengthThenAreAlsoFromBlockchainToRawBlockchainEquivalentAndAreBlockchainsTheSameExceptForTheCommitSealsAndRound(
        bcp: Blockchain,
        bcp': Blockchain,
        bc: Blockchain,
        bc': Blockchain
    )
    requires bcp <= bc
    requires bcp' <= bc'
    requires consistentBlockchains(bc, bc')
    ensures  consistentBlockchains(bcp, bcp')
    ensures |bcp| == |bcp'| ==> && areBlockchainsTheSameExceptForTheCommitSealsAndRound(bcp, bcp')
                                && fromBlockchainToRawBlockchain(bcp) == fromBlockchainToRawBlockchain(bcp');
    {
        assert consistentBlockchains(bcp, bc);
        assert consistentBlockchains(bcp', bc');

        if |bcp| == |bcp'| 
        {
            assert fromBlockchainToRawBlockchain(bcp) == fromBlockchainToRawBlockchain(bcp');
            lemmaOnFromBlockchainToRawBlockchainEqualityImpliesBlockchainsAreTheSameExceptForTheCommitSealsAndRound(bcp, bcp');
        }
    }   

    // 2s 3.2.0
    lemma lemmaFromBlockchainToRawBlockchainEquivalenceImpliesConsistentencyWithExtensionOfOneOfTheBlockchains(
        bcp: Blockchain,
        bcp': Blockchain,
        bc': Blockchain
    ) 
    requires fromBlockchainToRawBlockchain(bcp) == fromBlockchainToRawBlockchain(bcp')
    requires bcp' <= bc'
    ensures consistentBlockchains(bcp, bc')
    { }    

    // 2s 3.2.0
    lemma lemmaConsistencyWithABlockchainImpliesConsistencyWithOneOfItsExtensions(
        bcs: Blockchain,
        bcl: Blockchain,
        bcle: Blockchain
    )
    requires consistentBlockchains(bcs, bcl)
    requires |bcs| <= |bcl|
    requires bcl <= bcle
    ensures consistentBlockchains(bcs, bcle)
    {  }    

    predicate proposerPrecondition(blockchain: Blockchain)
    {
            && |blockchain|  > 0
            && (|blockchain| > 1 ==> (blockchain[|blockchain|-1].header.proposer in validators(blockchain[..|blockchain|-1])))
            && (|validators(blockchain)| > 0)
    }

    predicate isValidProposalJustification(m:QbftMessage, blockchain: Blockchain)
    requires proposerPrecondition(blockchain)
    {
        && m.Proposal?
        && m.proposalPayload.unsignedPayload.height == |blockchain|
        && isProposalJustification(
            m.proposalJustification,
            m.roundChangeJustification,
            {m.proposedBlock},
            |blockchain|,
            m.proposalPayload.unsignedPayload.round,
            m.proposedBlock,
            b => validateNonPreparedBlock(b,blockchain,m.proposalPayload.unsignedPayload.round),
            proposer(m.proposalPayload.unsignedPayload.round,blockchain),
            validators(blockchain)
        )
        // NOTE: This check is not required by the QBFT paper as the message structure is a bit different
        && digest(m.proposedBlock) == m.proposalPayload.unsignedPayload.digest
    }  

    function truncateSeq<T>(
        blockchain: seq<T>,
        h: nat
    ): seq<T>
    ensures truncateSeq(blockchain, h) <= blockchain
    ensures |truncateSeq(blockchain, h)| <= h
    ensures |truncateSeq(blockchain, h)| < h ==> truncateSeq(blockchain, h) == blockchain
    ensures |blockchain| >= h ==> |truncateSeq(blockchain, h)| == h 
    {
        if |blockchain| >= h then
            blockchain[..h]
        else
            blockchain
    }   

    predicate isQuorumOfPrepares(
        height:nat,
        round:nat,
        digest:Hash,
        QofP:set<QbftMessage>,
        messagesReceived: set<QbftMessage>,
        blockchain: Blockchain
    )
    requires |blockchain| >= height
    {
        && QofP <= validPreparesForHeightRoundAndDigest(
                                    messagesReceived,
                                    height,
                                    round,
                                    digest,
                                    validators(blockchain[..height]))
        && |QofP| >= quorum(|validators(blockchain[..height])|) 
    }

    predicate isQuorumOfCommits(
        height:nat,
        round:nat,
        block:Block,
        QofC:set<QbftMessage>,
        messagesReceived: set<QbftMessage>,
        blockchain: Blockchain
    )
    requires |blockchain| >= height
    {
        && QofC <= validCommitsForHeightRoundAndDigest(
                                    messagesReceived,
                                    height,
                                    round,
                                    block,
                                    validators(blockchain[..height]))
        && |QofC| >= quorum(|validators(blockchain[..height])|) 
    }   

    function getCommitSealAuthors(
        h: Hash,
        css: set<Signature>
    ) : set<Address>
    ensures forall n | n in getCommitSealAuthors(h, css) :: exists cs :: cs in css && recoverSignedHashAuthor(h,cs) ==n
    {
        set cs | cs in css ::  recoverSignedHashAuthor(h,cs)
    }    

    predicate inclusiveRange(low:nat, value: nat, high:nat)
    {
        low <= value <= high
    }   

    function multisetUnion<T>(sets:seq<multiset<T>>):multiset<T>
    {
        if sets == [] then
            multiset{}
        else
            sets[0] + multisetUnion(sets[1..])
    }           

    function multisetUnionOnSet<T>(sets:seq<set<T>>):multiset<T>
    {
        if sets == [] then
            multiset{}
        else
            multiset(sets[0]) + multisetUnionOnSet(sets[1..])
    }   

    lemma lemmaMultisetUnionOnSet<T>(sets:seq<set<T>>)
    ensures forall e :: ((exists s | s in sets :: e in s) <==> e in multisetUnionOnSet(sets))
    {  }      

    lemma lemmaSetUnionOnSeq<T>(sets:seq<set<T>>)
    ensures forall e :: ((exists s | s in sets :: e in s) <==> e in setUnionOnSeq(sets))
    {  }         

    lemma lemmaSetUnionOnSeqEmpty<T>(sets:seq<set<T>>)
    requires sets == []
    ensures  setUnionOnSeq(sets) == {}
    {  }  

    lemma lemmaMultisetUnionPreservesConcatenationWithTheLastElement<T>(
        s: seq<multiset<T>>
    )
    requires |s| >= 1
    ensures multisetUnion(s) == multisetUnion(s[..|s|-1]) + s[|s|-1]
    {
        if |s| == 1
        {
            assert multisetUnion(s) == multisetUnion(s[..|s|-1]) + s[|s|-1];
        }
        else
        {
            calc {
                multisetUnion(s);
                s[0] + multisetUnion(s[1..]);
                s[0] + multisetUnion(s[1..][..|s[1..]|-1]) + s[1..][|s[1..]|-1];
                {
                    assert s[1..][..|s[1..]|-1] == s[1..|s|-1];
                }
                s[0] + multisetUnion(s[1..|s|-1]) + s[|s|-1];
                multisetUnion(s[..|s|-1]) +  s[|s|-1];
            }
        }
    }

    lemma lemmaMultisetUnionOnSetPreservesConcatenationWithTheLastElement<T>(
        s: seq<set<T>>
    )
    requires |s| >= 1
    ensures multisetUnionOnSet(s) == multisetUnionOnSet(s[..|s|-1]) + multiset(s[|s|-1])
    {
        if |s| == 1
        {
            assert multisetUnionOnSet(s) == multisetUnionOnSet(s[..|s|-1]) + multiset(s[|s|-1]);
        }
        else
        {
            calc {
                multisetUnionOnSet(s);
                multiset(s[0]) + multisetUnionOnSet(s[1..]);
                multiset(s[0]) + multisetUnionOnSet(s[1..][..|s[1..]|-1]) + multiset(s[1..][|s[1..]|-1]);
                {
                    assert s[1..][..|s[1..]|-1] == s[1..|s|-1];
                }
                multiset(s[0]) + multisetUnionOnSet(s[1..|s|-1]) + multiset(s[|s|-1]);
                multisetUnionOnSet(s[..|s|-1]) +  multiset(s[|s|-1]);
            }
        }
    }     

    lemma lemmaMultisetUnionOnSetPreservesConcatenationOfTruncatedSequenceWithItsLastElement<T>(
        s: seq<set<T>>,
        i: nat
    )
    requires |s| >= 1
    requires i + 1 <= |s|
    ensures multisetUnionOnSet(s[..i+1]) == multisetUnionOnSet(s[..i]) + multiset(s[i])
    {
        var j := i + 1;
        lemmaMultisetUnionOnSetPreservesConcatenationWithTheLastElement(s[..j]);
        assert multisetUnionOnSet(s[..j]) == multisetUnionOnSet(s[..j][..j-1]) + multiset(s[..j][j-1]);
        assert s[..j][..j-1] == s[..j-1];
        assert s[..j][j-1] == s[j-1];
    }        

    lemma lemmaUnionOnSetPreservesConcatenationWithTheLastElement<T>(
        s: seq<set<T>>
    )
    requires |s| >= 1
    ensures setUnionOnSeq(s) == setUnionOnSeq(s[..|s|-1]) + s[|s|-1]
    {
        if |s| == 1
        {
            assert setUnionOnSeq(s) == setUnionOnSeq(s[..|s|-1]) + s[|s|-1];
        }
        else
        {
            calc {
                setUnionOnSeq(s);
                s[0] + setUnionOnSeq(s[1..]);
                s[0] + setUnionOnSeq(s[1..][..|s[1..]|-1]) + s[1..][|s[1..]|-1];
                {
                    assert s[1..][..|s[1..]|-1] == s[1..][..|s|-2]== s[1..|s|-1];
                    assert s[1..][|s[1..]|-1] == s[1..][|s|-2] == s[|s| -1];
                }
                s[0] + setUnionOnSeq(s[1..|s|-1]) + s[|s|-1];
                setUnionOnSeq(s[..|s|-1]) +  s[|s|-1];
            }
        }
    }         
}