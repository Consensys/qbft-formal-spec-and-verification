include "../../../spec/L1//types.dfy"
include "adversary.dfy"
include "common_functions.dfy"
include "network.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"
include "../../../spec/L1/node.dfy"

module L1_DistributedSystem
{
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_Spec
    import opened L1_Adversary
    import opened L1_CommonFunctions

    datatype DSState = DSState(
        configuration: Configuration,
        environment: Network,
        nodes: map<Address, NodeState>,
        adversary: Adversary
    )    

    predicate isHonest(s:DSState, n:Address)
    {
        n in (s.nodes.Keys - s.adversary.byz)
    }

    predicate IsValidConfiguration(
        configuration: Configuration
    )
    {
        && isUniqueSequence(configuration.nodes) 
        && isUniqueSequence(validators([configuration.genesisBlock]))
        && seqToSet(validators([configuration.genesisBlock])) <= seqToSet(configuration.nodes)
    }

    predicate DSInit(
        s: DSState,
        configuration: Configuration
    )
    {
        && IsValidConfiguration(configuration)
        && s.configuration == configuration
        && NetworkInit(s.environment,configuration)
        && (forall n :: n in configuration.nodes <==> n in s.nodes.Keys)
        && (forall n | n in s.nodes :: NodeInit(s.nodes[n],configuration,n))
        && AdversaryInit(s.adversary, configuration)
    }

    predicate validDSState(s:DSState)
    {
        forall ns | isHonest(s,ns) :: validNodeState(s.nodes[ns])
    }

    predicate DSNextNode(
        s : DSState,
        s': DSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )
    requires validDSState(s)
    {
        && NetworkNext(s.environment,s'.environment,messagesSentByTheNodes,messagesReceivedByTheNodes)
        && (forall mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.recipient == node)
        && var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
        && node in s.nodes
        && s'.nodes.Keys == s.nodes.Keys
        && (
            if isHonest(s,node) then
                && s'.nodes == s.nodes[node := s'.nodes[node]]
                && s'.adversary == s.adversary
                && NodeNext(s.nodes[node],messageReceived,s'.nodes[node],messagesSentByTheNodes)
            else
                && s'.nodes == s.nodes
                && AdversaryNext(s.adversary,messageReceived,s'.adversary,messagesSentByTheNodes)
        )
        && s'.configuration == s.configuration
    }

    predicate DSNext(
        s : DSState,
        s': DSState
    )
    requires validDSState(s)
    {
        ||  s == s'
        ||  (exists  messagesSentByTheNodes,
                    messagesReceivedByTheNodes,
                    node ::
                    DSNextNode(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
            )
    }
}

