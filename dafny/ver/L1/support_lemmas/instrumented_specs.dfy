include "../../../spec/L1/types.dfy"
include "../distr_system_spec/network.dfy"
include "../distr_system_spec/adversary.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"
include "../../../spec/L1/node.dfy"
include "../distr_system_spec/distributed_system.dfy"
include "../../common/sets.dfy"

module EEAInstrumentedSpecs
{
    import opened EEASpecTypes
    import opened EEASpecNetwork
    import opened EEAAuxiliaryFunctionsAndLemmas
    import opened EEASpec
    import opened HelperLemmasSets
    import opened EEADistributedSystem
    import opened EEAAdversary

    datatype InstrNodeState = InstrNodeState(
        nodeState: NodeState,
        proposalsAccepted: set<QbftMessage>,
        messagesSent: multiset<QbftMessageWithRecipient>,
        messagesSentToItself: set<QbftMessage>
    )

    datatype InstrDSState = InstrDSState(
        configuration: Configuration,
        environment: Network,
        nodes: map<Address, InstrNodeState>,
        adversary: Adversary
    )    

    predicate InstrNodeInit(s:InstrNodeState, c:Configuration, id:Address)
    {
        && NodeInit(s.nodeState, c, id)
        && s.proposalsAccepted == {}
        && s.messagesSent == multiset{}
        && s.messagesSentToItself == {}
    }

    predicate validInstrState(s:InstrNodeState)
    {
        && validNodeState(s.nodeState)
    }

    //======= SINGLE STEP INSTR SPEC

    predicate NodeNextSingleStep(
        current:NodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:NodeState,
        outQbftMessages: set<QbftMessageWithRecipient>
        )
    requires validNodeState(current)   
    {
        exists newTime ::
            var newMessagesReceived := current.messagesReceived + inQbftMessages;

            var currentWithNewMessagesReceived :=
                current.(
                    messagesReceived := newMessagesReceived,
                    localTime := newTime
                );

            NodeNextSubStep(currentWithNewMessagesReceived, next, outQbftMessages)
    }       

    function getSingletonOfAcceptedProposals(
        s: NodeState
    ): set<QbftMessage>
    {
        (if s.proposalAcceptedForCurrentRound.Optional? then
            {s.proposalAcceptedForCurrentRound.value}
        else
            {})
    }    

    predicate InstrNodeNextSingleStep(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    )
    requires validInstrState(current)
    {
        && NodeNextSingleStep(current.nodeState, inQbftMessages, next.nodeState, outQbftMessages)
        && next.proposalsAccepted == 
            current.proposalsAccepted + getSingletonOfAcceptedProposals(next.nodeState)
        &&  next.messagesSentToItself == current.messagesSentToItself + (next.nodeState.messagesReceived - inQbftMessages - current.nodeState.messagesReceived)
        &&  next.messagesSent == current.messagesSent + multiset(outQbftMessages)
    }    

    predicate InstrDSInit(s:InstrDSState, configuration:Configuration)
    {
        && IsValidConfiguration(configuration)
        && s.configuration == configuration
        && NetworkInit(s.environment,configuration)
        && (forall n :: n in configuration.nodes <==> n in s.nodes.Keys)
        && (forall n | n in s.nodes :: InstrNodeInit(s.nodes[n],configuration,n))
        && AdversaryInit(s.adversary, configuration)
    }       

    function getInstrDSStateHonestNodes(s:InstrDSState):set<Address>
    {
        s.nodes.Keys - s.adversary.byz
    }

    predicate isInstrNodeHonest(s:InstrDSState, n:Address)
    {
        n in getInstrDSStateHonestNodes(s)
    }    

    predicate validInstrDSState(s:InstrDSState)
    {
        forall ns | isInstrNodeHonest(s,ns) :: validInstrState(s.nodes[ns])
    }

    predicate InstrDSNextNodeSingle(
        s : InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )
    requires validInstrDSState(s)
    {
        && NetworkNext(s.environment,s'.environment,messagesSentByTheNodes,messagesReceivedByTheNodes)
        && (forall mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.recipient == node)
        && var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
        && node in s.nodes
        && s'.nodes.Keys == s.nodes.Keys
        && (
            if isInstrNodeHonest(s,node) then
                && s'.nodes == s.nodes[node := s'.nodes[node]]
                && s'.adversary == s.adversary
                && InstrNodeNextSingleStep(s.nodes[node],messageReceived,s'.nodes[node],messagesSentByTheNodes)
            else
                && s'.nodes == s.nodes
                && AdversaryNext(s.adversary,messageReceived,s'.adversary,messagesSentByTheNodes)
        )
        && s'.configuration == s.configuration
    }    

    predicate InstrDSNextSingle(s:InstrDSState, s':InstrDSState)
    requires validInstrDSState(s)
    {
        ||  s == s'
        ||  (exists  messagesSentByTheNodes,
                    messagesReceivedByTheNodes,
                    node ::
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
            )
    }    

    //==== MULTIPLE STEP INSTR SPEC

    predicate InstrNodeNextMultipleHelper(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>          
    )
    {
            exists s:seq<NodeState>, o:seq<set<QbftMessageWithRecipient>>, seqProposalsAccepted ::
                var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;
                var currentWithNewMessagesReceived :=
                        current.nodeState.(
                            messagesReceived := newMessagesReceived,
                            localTime := current.nodeState.localTime + 1
                        ); 
                && |s| >= 2
                && |o| == |s| - 1
                && s[0] == currentWithNewMessagesReceived
                && s[|s|-1] == next.nodeState
                && (forall i | 0 <= i < |s| - 1 ::
                    && validNodeState(s[i])  
                    && NodeNextSubStep(s[i], s[i+1], o[i])
                )          
                && (forall afterNext, messages | afterNext != s[|s|-1] :: 
                    !(
                        && validNodeState(s[|s|-1])
                        && NodeNextSubStep(s[|s|-1], afterNext, messages)
                    )
                )                
                && outQbftMessages == setUnionOnSeq(o)
                && seqProposalsAccepted == seq(
                    |s|-1 ,
                    (i:nat) requires i + 1 < |s| =>
                        getSingletonOfAcceptedProposals(s[i+1])
                )         
                && next.proposalsAccepted ==  current.proposalsAccepted + setUnionOnSeq(seqProposalsAccepted)                 
    }

    predicate InstrNodeNextMultiple(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    )
    requires validInstrState(current)
    {
        && NodeNext(current.nodeState, inQbftMessages, next.nodeState, outQbftMessages)
        && (
            InstrNodeNextMultipleHelper(current, inQbftMessages, next, outQbftMessages)
        )
        &&  next.messagesSentToItself == current.messagesSentToItself + (next.nodeState.messagesReceived - inQbftMessages - current.nodeState.messagesReceived)
        &&  next.messagesSent == current.messagesSent + multiset(outQbftMessages)
    }      

    predicate DSInstrNextNodeMultiple(
        s : InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )
    requires validInstrDSState(s)
    {
        && NetworkNext(s.environment,s'.environment,messagesSentByTheNodes,messagesReceivedByTheNodes)
        && (forall mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.recipient == node)
        && var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
        && node in s.nodes
        && s'.nodes.Keys == s.nodes.Keys
        && (
            if isInstrNodeHonest(s,node) then
                && s'.nodes == s.nodes[node := s'.nodes[node]]
                && s'.adversary == s.adversary
                && InstrNodeNextMultiple(s.nodes[node],messageReceived,s'.nodes[node],messagesSentByTheNodes)
            else
                && s'.nodes == s.nodes
                && AdversaryNext(s.adversary,messageReceived,s'.adversary,messagesSentByTheNodes)
        )
        && s'.configuration == s.configuration
    }      

    predicate InstrDSNextMultiple(s:InstrDSState, s':InstrDSState)
    requires validInstrDSState(s)
    {
        ||  s == s'
        ||  (exists  messagesSentByTheNodes,
                    messagesReceivedByTheNodes,
                    node ::
                    DSInstrNextNodeMultiple(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
            )
    }        

}