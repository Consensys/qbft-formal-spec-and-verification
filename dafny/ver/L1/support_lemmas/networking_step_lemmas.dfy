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
include "general_lemmas.dfy"
include "basic_invariants.dfy"
include "instr_node_state_invariants.dfy"
include "networking_invariants.dfy"
include "instr_dsstate_networking_common_invariants.dfy"

module L1_NetworkingStepLemmas
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
    import opened L1_InstrNodeStateInvariants
    import opened L1_InstrDSStateNetworkingCommonInvariants
    import opened L1_GeneralLemmas
    import opened L1_NetworkingInvariants

    predicate messagesSentByAnHonestNodeExcludingSentToItselfDoNotChange(
        s:  InstrDSState, 
        s': InstrDSState,
        n : Address
    )
    requires n in s.nodes
    requires n in s'.nodes
    {
        && filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) ==
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)),n)

        && filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)),n) ==
           filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)),n) 
    }

    predicate messagesSentByAnHonestNodeIncludingSentToItselfDoNotChange(
        s:  InstrDSState, 
        s': InstrDSState,
        n : Address
    )
    requires n in s.nodes
    requires n in s'.nodes
    {
        // TODO: allMesssagesSentIncSentToItselfWithoutRecipient and getAllMessagesSentByTheNode both include the messages
        // set to itself but this is indicated only in the name of one of them.
        && filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n) ==
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n)

        && filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, n)),n) ==
           filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', n)),n) 
    }   

    predicate messagesSentByHonestNodesIncludingSentToItselfDoNotChange
    (
        s:  InstrDSState, 
        s': InstrDSState
    )
    requires nodeSetDoesNotChange(s,s')
    requires honestNodesDoNotChange(s,s')
    {
        forall n | isInstrNodeHonest(s, n) :: messagesSentByAnHonestNodeIncludingSentToItselfDoNotChange(s, s', n)
    }   

    predicate messagesSentBHonestNodesExcludingSentToItselfDoNotChange
    (
        s:  InstrDSState, 
        s': InstrDSState
    )
    requires nodeSetDoesNotChange(s,s')
    requires honestNodesDoNotChange(s,s')
    {
        forall n | isInstrNodeHonest(s, n) :: messagesSentByAnHonestNodeExcludingSentToItselfDoNotChange(s, s', n)
    }   


    // 144s
    lemma lemmaAdversaryNextDoesNotChangeMessagesSentByHonestNodesExcludingSentToItself(
        s:  InstrDSState, 
        s': InstrDSState
    )
    requires invEnvMessagesSentYetToBeReceivedIsASubsetOfAllMessagesSent(s)
    requires invAdversaryMessagesReceivedHaveBeenSent(s)  
    requires adversaryTakesStep(s,s')
    ensures messagesSentBHonestNodesExcludingSentToItselfDoNotChange(s, s')
    {
        lemmaGetSetOfSignedPayloads();
        var messagesSentByTheNodes,
                    messagesReceivedByTheNodes,
                    node :|
                    
                    && InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
                    && !isInstrNodeHonest(s, node);  

        assert forall n :: isInstrNodeHonest(s,n) ==> isInstrNodeHonest(s',n);

        forall n,m | isInstrNodeHonest(s,n)  && m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))),n)
        ensures m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n)
        {
            if(m.SignedProposalPayload?)
            {
                // assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n);
            }
            else if(m.SignedPreparePayload?)
            {
                // assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n);
            }
            else if(m.SignedCommitPayload?)
            {
                // assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n);
            }
            else if(m.SignedRoundChangePayload?)
            {
                assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n);
            }            
            
        }

        assert forall n | isInstrNodeHonest(s,n) ::
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))),n) <=
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n);
    }   

    // 223s
    lemma lemmaAdversaryNextDoesNotChangeMessagesSentByHonestNodesIncludingSentToItself(
        s:  InstrDSState, 
        s': InstrDSState
    )
    requires invEnvMessagesSentYetToBeReceivedIsASubsetOfAllMessagesSent(s)
    requires invAdversaryMessagesReceivedHaveBeenSent(s)  
    requires adversaryTakesStep(s,s')
    ensures messagesSentByHonestNodesIncludingSentToItselfDoNotChange(s, s')
    {
        lemmaGetSetOfSignedPayloads();
        var messagesSentByTheNodes,
                    messagesReceivedByTheNodes,
                    node :|
                    
                    && InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
                    && !isInstrNodeHonest(s, node);  

        assert forall n :: isInstrNodeHonest(s,n) <==> isInstrNodeHonest(s',n);

        forall n,m | isInstrNodeHonest(s,n)  && m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))),n)
        ensures m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n)
        {
            // assume m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n);
            if(m.SignedProposalPayload?)
            {
                // assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n);
            }
            else if(m.SignedPreparePayload?)
            {
                // assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n);
            }
            else if(m.SignedCommitPayload?)
            {
                // assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n);
            }
            else if(m.SignedRoundChangePayload?)
            {
                assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n);
            }            
            
        }

        lemmaAllMesssagesSentIncSentToItselfWithoutRecipient(s);
        lemmaAllMesssagesSentIncSentToItselfWithoutRecipient(s');

        assert forall n | isInstrNodeHonest(s,n) ::
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))),n) <=
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n);

        assert forall n | isInstrNodeHonest(s,n) ::
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n) == 
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)),n);  

        assert forall n | isInstrNodeHonest(s,n) ::
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, n)),n) ==
           filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', n)),n);

        assert forall n | isInstrNodeHonest(s,n) ::
            s.nodes[n].messagesSentToItself == 
            s'.nodes[n].messagesSentToItself;     

        forall n | isInstrNodeHonest(s,n)
        ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n) ==
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n);   

        {
            lemmaAllMesssagesSentIncSentToItselfWithoutRecipientFGFilter(s , n);
            assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)),n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n) +
                    setUnion(set n' | n' in s.nodes && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n));            
            lemmaAllMesssagesSentIncSentToItselfWithoutRecipientFGFilter(s' , n);
            assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)),n) +
                    setUnion(set n' | n' in s'.nodes && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n));

        }       
    }   

    lemma lemmaAllMesssagesSentIncSentToItselfWithoutRecipientEqualOldPlusAllMessagesSentAtCurrentHonestStep(
        s:InstrDSState, 
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address        
    )
    requires validInstrDSState(s) 
    requires InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
    requires isInstrNodeHonest(s,node)   
    ensures 
            var current := s.nodes[node];
        var next := s'.nodes[node];     
        var messagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
        var newMessagesReceived := current.nodeState.messagesReceived + messagesReceived;   
    var newMessagesSentToItself :=  (next.nodeState.messagesReceived - newMessagesReceived - current.nodeState.messagesReceived);
            allMesssagesSentIncSentToItselfWithoutRecipient(s') == 
            allMesssagesSentIncSentToItselfWithoutRecipient(s) +
            fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + 
            newMessagesSentToItself;    
    {
        var current := s.nodes[node];
        var next := s'.nodes[node];     
        var messagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
        var newMessagesReceived := current.nodeState.messagesReceived + messagesReceived;                     
        var newMessagesSentToItself :=  (next.nodeState.messagesReceived - newMessagesReceived - current.nodeState.messagesReceived);
        assert next.messagesSentToItself == current.messagesSentToItself + newMessagesSentToItself;
        assert allMesssagesSentIncSentToItselfWithoutRecipient(s') == 
                allMesssagesSentIncSentToItselfWithoutRecipient(s) +
                fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + 
                newMessagesSentToItself;
    }         
}