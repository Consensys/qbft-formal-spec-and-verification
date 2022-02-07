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
include "instr_dsstate_networking_common_invariants.dfy"

module L1_NetworkingInvariants
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

    predicate invMessagesReceivedHaveBeenSent(
        s:InstrDSState,
        n:Address
    )
    requires n in s.nodes
    {
                                                // TODO: Put expression below into a function?
        s.nodes[n].nodeState.messagesReceived <= allMessagesSentWithoutRecipient(s.environment) + s.nodes[n].messagesSentToItself
    }     

    predicate invMessagesReceivedByHonestNodesHaveBeenSent(
        s:InstrDSState
    )
    {
        forall n | isInstrNodeHonest(s,n) :: invMessagesReceivedHaveBeenSent(s,n)
    }     

    predicate invMessagesReceivedByHonestNodesAreInAllMesssagesSentIncSentToItselfWithoutRecipient(
        s: InstrDSState
    )
    {
        forall n | isInstrNodeHonest(s,n) ::
            s.nodes[n].nodeState.messagesReceived  <= allMesssagesSentIncSentToItselfWithoutRecipient(s)
    }

    predicate invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(
        s: InstrDSState,
        n: Address
    ) 
    requires n in s.nodes
    {
                                                           // TODO: Change par of function below to take InstrDSState not environment?
        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n)
        ==
        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n)
    }

    // TODO: To be moved?
    predicate invAdversaryMessagesReceivedHaveBeenSent(
        s: InstrDSState
    ) 
    {
        && s.adversary.messagesReceived <= allMessagesSentWithoutRecipient(s.environment)
        && 
        (forall n | isInstrNodeHonest(s,n) ::
            allMessagesSentBy(s.adversary.messagesReceived,n) <= allMessagesSentBy(allMessagesSentWithoutRecipient(s.environment),n))
    }         

    predicate invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(
        s: InstrDSState,
        n: Address
    ) 
    requires n in s.nodes
    {
        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n)
        ==
        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, n)), n)
    }    

    predicate invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(
        s: InstrDSState
    ) 
    {
        forall n | isInstrNodeHonest(s,n) :: 
            invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s,n)
    }    

    predicate invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(
        s: InstrDSState
    ) 
    {
        forall n | isInstrNodeHonest(s,n) :: 
            invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s,n)
    }    

    // TODO: To be moved?
    predicate indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(
        s: InstrDSState
    )
    {
        && invAdversaryMessagesReceivedHaveBeenSent(s)
        && invNodesIdMatchesMapKey(s)
        && invEnvMessagesSentYetToBeReceivedIsASubsetOfAllMessagesSent(s)
    }

    // TODO: Internal?
    predicate invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(
        s: InstrDSState, 
        node: Address
    )  
    requires isInstrNodeHonest(s,node)
    {
        forall n | isInstrNodeHonest(s,n) && n != node ::
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), n) <=
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n)                 
    }

    predicate invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(
        s: InstrDSState
    ) 
    {
        forall node | isInstrNodeHonest(s, node):: invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, node)
    }

    predicate invAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(
        s: InstrDSState, 
        node: Address
    )  
    requires isInstrNodeHonest(s,node)
    {
        forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n)            
    }

    predicate invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(
        s: InstrDSState
    ) 
    {
        forall node | isInstrNodeHonest(s, node)::      invAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, node)
    }

    predicate invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(
        s: InstrDSState
    ) 
    {
        forall n1, n2, m | 
                && isInstrNodeHonest(s,n1) 
                && isInstrNodeHonest(s,n2) 
                && m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n1].nodeState.messagesReceived), n2)
            ::
                m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,n2))
    }

    // TODO: Move?
    predicate indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(
        s: InstrDSState
    )
    {
        && indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
        && invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
        && invNodesIdMatchesMapKey(s)         
    }

}
