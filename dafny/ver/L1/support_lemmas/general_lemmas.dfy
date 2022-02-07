include "../../../spec/L1/types.dfy"
include "../distr_system_spec/common_functions.dfy"
include "../distr_system_spec/network.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"
include "../../../spec/L1/node.dfy"
include "../distr_system_spec/distributed_system.dfy"
include "../../common/sets.dfy"
include "instrumented_specs.dfy"
include "axioms.dfy"
include "aux_functions.dfy"
include "basic_invariants.dfy"
include "instr_node_state_invariants.dfy"
include "quorum.dfy"

module L1_GeneralLemmas
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
    import opened L1_AuxFunctionsProof
    import opened L1_AuxBasicInvariantsProof
    // import opened L1_NetworkingInvariants
    import opened L1_InstrNodeStateInvariants
    import opened L1_LemmaQuorum

    lemma lemmaHashBlockForCommitSeal(b:Block, b':Block)
    requires hashBlockForCommitSeal(b) == hashBlockForCommitSeal(b')
    ensures areBlocksTheSameExceptForTheCommitSeals(b,b')
    {
        lemmaSignedHash();
        lemmaDigest();

        var bForDigest := b.(
                header:= b.header.(
                    commitSeals := {})
            );

        var b'ForDigest := b'.(
                header:= b'.header.(
                    commitSeals := {})
            );

        assert hashBlockForCommitSeal(b) == digest(bForDigest);
        assert hashBlockForCommitSeal(b') == digest(b'ForDigest);
        assert  digest(bForDigest) ==  digest(b'ForDigest);
        assert bForDigest == b'ForDigest;

    }

    lemma lemmaSignedCommitPayloadInSetOfSignedPayloadsImplyNonSignedIsInSetOfNonSigned(
        m: QbftMessage,
        msgs: set<QbftMessage>
    )
    requires m.Commit? 
    requires getSignedPayload(m) in getSetOfSignedPayloads(msgs)
    ensures m in msgs
    {
        // lemmaSignedPrepare();
        // lemmaSignedCommit();
        // lemmaSignedProposal();
        // lemmaSignedRoundChange();
    }

    lemma lemmaSplitSetUnionHelper<T1, T2>(
        // A: set<set<T1>>,
        // B: set<set<T1>>,
        S: set<T2>,
        y: T2,
        p: T2 -> bool,
        q: T2 -> bool,
        m: T2 --> set<T1> 
    )
    // requires A == set x | p(x) :: m(x)
    requires p(y)
    requires !q(y)
    requires y in S
    requires forall x | x in S :: m.requires(x)
    requires forall x' | x' != y :: p(x') == q(x')
    ensures var A := set x | x in S && p(x) :: m(x); var B := set x | x in S && q(x) :: m(x);
                A == B + {m(y)}
    {
        // var A := set x | x in S && p(x) :: m(x); 
        // var B := set x | x in S && q(x) :: m(x);

        // var C := set x | x in S && p(x) ; 
        // var D := set x | x in S && q(x) ;        

        // assert  A == B + {m(y)};

        // // assert C == D + {y};
        // forall x | x in D 
        // {
        //     assert x in S;
        //     assert x != y;
        //     assert q(x);
        //     assert p(x);

        // }
        // assert D <= C;

        // if y !in S 
        // {
        //     assert A == B + {m(y)};
        // }
    }    

    lemma lemmaSplitSetUnion<T1, T2>(
        // A: set<set<T1>>,
        // B: set<set<T1>>,
        S: set<T2>,
        y: T2,
        p: T2 -> bool,
        q: T2 -> bool,
        m: T2 --> set<T1> 
    )
    // requires A == set x | p(x) :: m(x)
    requires p(y)
    requires !q(y)
    requires y in S
    requires forall x | x in S :: m.requires(x)
    requires forall x' | x' != y :: p(x') == q(x')
    ensures var A := set x | x in S && p(x) :: m(x); var B := set x | x in S && q(x) :: m(x);
            setUnion(A) == setUnion(B + {m(y)})
    {

    }

    lemma lemmaSetUnionBasic<T>(
        A: set<set<T>>,
        B: set<set<T>>,
        C: set<set<T>>,
        D: set<set<T>>
    )
    requires A == C 
    requires B == D 
    ensures setUnion(A + B) == setUnion(C + D)
    {

    }

    lemma lemmaSetUnionEquation<T>(
        A: set<T>,
        B: set<T>,
        C: set<set<T>>,
        D: set<T>,
        E: set<T>
    )
    requires A ==
            B + setUnion(C + {D})
    requires D <= B
    requires E <= D
    ensures  A ==
            B + setUnion(C + {E})
    {

    }



    // 5s 3.2.0
    lemma lemmaFromDSInstrNextNodeNodeNextSubStep(
        s: InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    ) returns (sForSubsteps: InstrDSState, newMessagesReceived: set<QbftMessage>, newMessagesSentToItself: set<QbftMessage>)
    requires validInstrDSState(s)  
    requires InstrDSNextSingle(s, s')
    requires InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node);  
    requires isInstrNodeHonest(s,node)
    ensures 
        sForSubsteps == s.(nodes := sForSubsteps.nodes)
    ensures sForSubsteps.nodes.Keys == s.nodes.Keys
    ensures sForSubsteps.nodes == s.nodes[node := sForSubsteps.nodes[node]]
    ensures sForSubsteps.nodes[node] == s.nodes[node].(nodeState := sForSubsteps.nodes[node].nodeState)
    ensures newMessagesReceived == set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;    
    ensures 
        sForSubsteps.nodes[node].nodeState == s.nodes[node].nodeState.(
            messagesReceived := s.nodes[node].nodeState.messagesReceived + newMessagesReceived,
            localTime := s'.nodes[node].nodeState.localTime
        )
    ensures 
        NodeNextSubStep(sForSubsteps.nodes[node].nodeState, s'.nodes[node].nodeState, messagesSentByTheNodes);  
    ensures s'.nodes[node].messagesSentToItself == s.nodes[node].messagesSentToItself + newMessagesSentToItself;   
    ensures newMessagesSentToItself ==  s'.nodes[node].nodeState.messagesReceived -  sForSubsteps.nodes[node].nodeState.messagesReceived
    ensures sForSubsteps == getStartStateForNodeNextSubstep(s, s', messagesReceivedByTheNodes, node)
    {
        var current := s.nodes[node];
        var next := s'.nodes[node];

        assert InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node);  
        newMessagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
        assert InstrNodeNextSingleStep(current,newMessagesReceived,next,messagesSentByTheNodes);
        assert NodeNextSingleStep(current.nodeState,newMessagesReceived,next.nodeState,messagesSentByTheNodes);

        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := current.nodeState.messagesReceived + newMessagesReceived,
                localTime := next.nodeState.localTime
            );

        var instrNodeStateForSubsteps := current.(
            nodeState := currentForSubsteps
        );

        sForSubsteps := s.(nodes := s.nodes[node := instrNodeStateForSubsteps]);

        var nextForSubsteps := next.nodeState;

        assert NodeNextSubStep(sForSubsteps.nodes[node].nodeState, nextForSubsteps, messagesSentByTheNodes); 

        newMessagesSentToItself :=  (next.nodeState.messagesReceived - currentForSubsteps.messagesReceived);
        assert next.messagesSentToItself == current.messagesSentToItself + newMessagesSentToItself;          
    }

    function getStartStateForNodeNextSubstep(
        s: InstrDSState,
        s': InstrDSState,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    ) : InstrDSState
    requires node in s.nodes
    requires node in s'.nodes
    {
        var newMessagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
        var currentForSubsteps :=
            s.nodes[node].nodeState.(
                messagesReceived := s.nodes[node].nodeState.messagesReceived + newMessagesReceived,
                localTime := s'.nodes[node].nodeState.localTime
            );
        var instrNodeStateForSubsteps := s.nodes[node].(
            nodeState := currentForSubsteps
        );
        s.(nodes := s.nodes[node := instrNodeStateForSubsteps])
    }    

    lemma lemmaValidatorsAreTheSameOfTheGenesisBlock(
    )
    ensures forall bc1, bc2 :: validators(bc1) == validators(bc2)
    {
        axiomRawValidatorsNeverChange();
    }     

    lemma lemmaSizeOfSetOfConsistentPreparesMatchesTheSizeOfTheSetOfAssociatedSignatures(msgs:set<QbftMessage>, h:nat, r:nat, d:Hash) 
    requires forall m | m in msgs ::   && m.Prepare?
                                    && m.preparePayload.unsignedPayload.height == h
                                    && m.preparePayload.unsignedPayload.round == r
                                    && m.preparePayload.unsignedPayload.digest == d

    ensures |getSetOfSenders(msgs)| == |msgs|
    ensures forall s | s in getSetOfSenders(msgs) :: (exists m :: m in msgs && recoverSignature(m) == s)
    {
        lemmaSignedPrepare();
        
        // senders := set m | m in msgs :: recoverSignature(m);

        lemma_MapSetCardinalityOver(msgs, getSetOfSenders(msgs), (m:QbftMessage) requires isMsgWithSignedPayload(m) => recoverSignature(m));
    }    

    lemma lemmaSizeOfSetOfConsistentSignedPreparesMatchesTheSizeOfTheSetOfAssociatedSignatures(msgs:set<SignedPrepare>, h:nat, r:nat, d:Hash) 
    requires forall m | m in msgs ::  
                                    && m.unsignedPayload.height == h
                                    && m.unsignedPayload.round == r
                                    && m.unsignedPayload.digest == d

    ensures |getSetOfSignedPrepareSenders(msgs)| == |msgs|
    ensures forall s | s in getSetOfSignedPrepareSenders(msgs) :: (exists m :: m in msgs && recoverSignedPrepareAuthor(m) == s)
    {
        lemmaSignedPrepare();
        
        // senders := set m | m in msgs :: recoverSignature(m);

        lemma_MapSetCardinalityOver(msgs, getSetOfSignedPrepareSenders(msgs), (m:SignedPrepare) => recoverSignedPrepareAuthor(m));
    }     

    // 1.1s
    lemma lemmaOnUnicityOfCommitSeal(
        h: Hash,
        cs1: Signature,
        cs2: Signature
    )
    requires cs1 != cs2
    ensures recoverSignedHashAuthor(h,cs1) != recoverSignedHashAuthor(h,cs2)
    {
        lemmaSignedHash();
    }         

}
