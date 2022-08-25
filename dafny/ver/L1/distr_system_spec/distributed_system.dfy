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

    function filterA<T>(
        s: seq<T>,
        seqNodes: seq<Address>,
        node: Address     
    ): seq<T>
    requires |seqNodes| == |s|
    {
        if s == [] then 
            []
        else 
            (
                if seqNodes[0] == node then
                    [s[0]] + filterA(s[1..], seqNodes[1..], node)
                else
                    []
            )
            + filterA(s[1..], seqNodes[1..], node)
    }   

    // function filterB(
    //     seqMessagesSentByTheNodes: seq<set<QbftMessageWithRecipient>>,
    //     seqNodes: seq<Address>,
    //     node: Address     
    // ): seq<set<QbftMessageWithRecipient>>
    // requires |seqNodes| == |seqMessagesSentByTheNodes| > 0
    // {
    //     if seqNodes == [] then 
    //         []
    //     else 
    //         (
    //             if seqNodes[0] == node then
    //                 [seqMessagesSentByTheNodes[0]] + filterA(seqMessagesSentByTheNodes[1..], seqNodes[1..], node)
    //             else
    //                 []
    //         )
    //         + filterA(seqMessagesSentByTheNodes[1..], seqNodes[1..], node)
    // }   




    // function QbftSpecificationBuilder(
    //     configuration: Configuration,
    //     id: Address
    // ): QbftSpecification
    // {
    //     var behaviours:=
    //         iset QbftNodeBehaviour: QbftNodeBehaviour |
    //             exists nt: iseq<NodeState> ::
    //                 && NodeInit(nt[0], configuration, id)
    //                 && QbftNodeBehaviour.initialBlockchain == nt[0].blockchain
    //                 && (forall i:nat ::
    //                         (
    //                             IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
    //                         //     var step := QbftNodeBehaviour.steps[i];
    //                         //     && validNodeState(nt[i])
    //                         // // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
    //                         // && step.newBlockchain == nt[i+1].blockchain
    //                         )
    //                 )
    //         ;

    //     QbftSpecification(behaviours)
    // }  

    datatype AdversarySpecificationStep = AdversarySpecificationStep(
        messageReceived: set<QbftMessage>,
        messagesToSend: set<QbftMessageWithRecipient>
    )

    datatype AdvesarySpecificationBehaviour = AdvesarySpecificationBehaviour(
        steps: iseq<AdversarySpecificationStep>
    )

    datatype AdversarySpecification = AdversarySpecification(
        behaviours: iset<AdvesarySpecificationBehaviour>
    )

    function AdversarySpecificationBuilder(
        configuration: Configuration,
        byzNodes: set<Address>
    ): AdversarySpecification
    {
        var behaviours:=
            iset advesarySpecificationBehaviour: AdvesarySpecificationBehaviour |
                exists nt: iseq<Adversary> ::
                    && AdversaryInit(nt[0], configuration)
                    && nt[0].byz == byzNodes
                    && (forall i:nat ::
                            var step := advesarySpecificationBehaviour.steps[i];
                            && AdversaryNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
                    )
            ;

        AdversarySpecification(behaviours)
    }  

    datatype EnvironmentSpecificationStep = EnvironmentSpecificationStep(
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>
    )

    datatype EnvironmentSpecificationBehaviour = EnvironmentSpecificationBehaviour(
        steps: iseq<EnvironmentSpecificationStep>
    )

    datatype EnvironmentSpecification = EnvironmentSpecification(
        behaviours: iset<EnvironmentSpecificationBehaviour>
    )    

    function EnvironmentSpecificationBuilder(
        configuration: Configuration
    ): EnvironmentSpecification
    {
        var behaviours:=
            iset environmentSpecificationBehaviour: EnvironmentSpecificationBehaviour |
                exists nt: iseq<Network> ::
                    && NetworkInit(nt[0], configuration)
                    && (forall i:nat ::
                            var step := environmentSpecificationBehaviour.steps[i];
                            && NetworkNext(nt[i], nt[i+1], step.messagesSentByTheNodes, step.messagesReceivedByTheNodes)
                    )
            ;

        EnvironmentSpecification(behaviours)
    }      



    datatype DSBehaviour = DSBehaviour(
        nodesBehaviours: map<Address, QbftNodeBehaviour>,
        adversaryBehaviour: AdvesarySpecificationBehaviour,
        environmentBehaviour: EnvironmentSpecificationBehaviour
    )

    datatype DSSepcification = DSSepcification(
        behaviours: iset<DSBehaviour>
    )

    predicate DSSpecificationBuilderHelper(
        dsBehaviour: DSBehaviour,
        allNodes: set<Address>,
        seqNodes: iseq<Address>,
        i: nat
    )
    {
        var honestNodes := dsBehaviour.nodesBehaviours.Keys;
        var environmentStep := dsBehaviour.environmentBehaviour.steps[i];
        var node := seqNodes[i];
        var messagesReceivedWithoutRecipient := (set mr:QbftMessageWithRecipient | mr in environmentStep.messagesReceivedByTheNodes :: mr.message);
        var byz := allNodes - honestNodes;
        && node in allNodes
        && (forall mr:QbftMessageWithRecipient | mr in environmentStep.messagesReceivedByTheNodes :: mr.recipient == node)                        
        &&  if node in honestNodes then
                var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, node, i);
                var nodeStep := dsBehaviour.nodesBehaviours[node].steps[stepsTakeByNodeSoFar];
                && nodeStep.messagesToSend == environmentStep.messagesSentByTheNodes
                && nodeStep.messagesReceived == messagesReceivedWithoutRecipient
            else 
                var stepsTakeByNodeSoFar := getStepsTakeByAversarySoFar(seqNodes, byz, i);
                var nodeStep := dsBehaviour.adversaryBehaviour.steps[stepsTakeByNodeSoFar];
                && nodeStep.messagesToSend == environmentStep.messagesSentByTheNodes
                && nodeStep.messageReceived == messagesReceivedWithoutRecipient
    }

    function DSSpecificationBuilder(
        configuration: Configuration
    ): DSSepcification 
    requires IsValidConfiguration(configuration)
    {
        var allNodes := seqToSet(configuration.nodes);
        var behaviours := 
            iset dsBehaviour: DSBehaviour |
                var honestNodes := dsBehaviour.nodesBehaviours.Keys;
                var byzNodes := allNodes - honestNodes;
                && honestNodes <= allNodes         
                && |byzNodes| <= f(|validators([configuration.genesisBlock])|)         
                && dsBehaviour.environmentBehaviour in EnvironmentSpecificationBuilder(configuration).behaviours
                && dsBehaviour.adversaryBehaviour in AdversarySpecificationBuilder(configuration, byzNodes).behaviours
                && (forall n | n in honestNodes :: IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n]))
                // && (forall )
                && exists seqNodes: iseq<Address> ::
                    && forall i: nat ::
                        DSSpecificationBuilderHelper(dsBehaviour, allNodes, seqNodes, i)
                        // var environmentStep := dsBehaviour.environmentBehaviour.steps[i];
                        // var node := seqNodes[i];
                        // var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, node, i);
                        // var messagesReceivedWithoutRecipient := (set mr:QbftMessageWithRecipient | mr in environmentStep.messagesReceivedByTheNodes :: mr.message);
                        // && node in allNodes
                        // && (forall mr:QbftMessageWithRecipient | mr in environmentStep.messagesReceivedByTheNodes :: mr.recipient == node)                        
                        // &&  if node in honestNodes then
                        //         var nodeStep := dsBehaviour.nodesBehaviours[node].steps[stepsTakeByNodeSoFar];
                        //         && nodeStep.messagesToSend == environmentStep.messagesSentByTheNodes
                        //         && nodeStep.messageReceived == messagesReceivedWithoutRecipient
                        //     else 
                        //         var nodeStep := dsBehaviour.adversaryBehaviour.steps[stepsTakeByNodeSoFar];
                        //         && nodeStep.messagesToSend == environmentStep.messagesSentByTheNodes
                        //         && nodeStep.messageReceived == messagesReceivedWithoutRecipient
            ;

        DSSepcification(behaviours)
    }

    lemma lemmajkfladjklfaHelper(
        QbftNodeBehaviour: QbftNodeBehaviour,
        configuration: Configuration,
        id: Address        
    )
    requires IsValidQbftBehaviour(configuration, id, QbftNodeBehaviour)
    {
        var nt: iseq<NodeState> :|
                    && NodeInit(nt[0], configuration, id)
                    && QbftNodeBehaviour.initialBlockchain == nt[0].blockchain
                    && (forall i:nat ::
                            (
                                IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
                                // var step := QbftNodeBehaviour.steps[i];
                                // && validNodeState(nt[i])
                                // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
                                // && step.newBlockchain == nt[i+1].blockchain
                            )
                    )
            ;
    }

    function getDummySeqNodes(
        configuration: Configuration,
        id: Address
    ): (ret: iseq<NodeState>)
    requires  |validators([configuration.genesisBlock])| > 0
    ensures NodeInit(ret[0], configuration, id)
    {
        var nt: iseq<NodeState> := 
            imap i: nat :: 
                var ns: NodeState := NodeState(
                    [configuration.genesisBlock],
                    0,
                    0,
                    id,
                    configuration,
                    {},
                    None,
                    None,
                    None,
                    0
                );
                assert NodeInit(ns, configuration, id);
                ns
            ;
        nt
    }

    // function getSeqHonestNodeStates(
    //     nodeStates: iseq<NodeState>,
    //     id: Address,
    //     i: nat,
    //     seqNodes: iseq<Address>
    // ): nat
    // {
    //     if i == 0 then
    //         (nodeStates[0], 0)
    //     else
    //         var prev := getSeqHonestNodeStates(nodeStates, id, i-1, seqNodes);
    //         var stateIndex := 
    //             if id == seqNodes[i-1] then
    //                 prev.1+1
    //             else
    //                 prev.1
    //             ;
    //         (prev + [nodeStates[stateIndex]], stateIndex)

    // }

    predicate pLemmajkfladjklfaGetSeqNodes(
       dsBehaviour: DSBehaviour,
       allNodes: set<Address>,
       seqNodes: iseq<Address>
    )
    {
        && (forall i: nat :: DSSpecificationBuilderHelper(dsBehaviour, allNodes, seqNodes, i))
        && (forall i: nat :: seqNodes[i] in allNodes)
    }


    lemma lemmajkfladjklfaGetSeqNodes (
       dsBehaviour: DSBehaviour,
       configuration: Configuration,
       allNodes: set<Address>
    ) returns (seqNodes: iseq<Address>)
    requires IsValidConfiguration(configuration)
    requires dsBehaviour in DSSpecificationBuilder(configuration).behaviours
    requires  |validators([configuration.genesisBlock])| > 0
    requires allNodes == seqToSet(configuration.nodes);
    ensures pLemmajkfladjklfaGetSeqNodes(dsBehaviour, allNodes, seqNodes)
    {
        seqNodes :|
            && forall i: nat ::
                DSSpecificationBuilderHelper(dsBehaviour, allNodes, seqNodes, i)
            ;   

        forall i: nat 
        ensures seqNodes[i] in allNodes;
        {
            assert  DSSpecificationBuilderHelper(dsBehaviour, allNodes, seqNodes, i);
            assert seqNodes[i] in allNodes;
        }     
    }

    predicate pLemmajkfladjklfaGetAdvStatesHelper(
        dsBehaviour: DSBehaviour,
        seqAdvStates: iseq<Adversary>,
        i: nat
    )
    {
        var step := dsBehaviour.adversaryBehaviour.steps[i];
        && AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)        
    }

    lemma lemmajkfladjklfaGetAdvStatesHelper(
       dsBehaviour: DSBehaviour,
       configuration: Configuration,
       allNodes: set<Address>
    ) returns (seqAdvStates: iseq<Adversary>)
    requires IsValidConfiguration(configuration)
    requires dsBehaviour in DSSpecificationBuilder(configuration).behaviours
    requires  |validators([configuration.genesisBlock])| > 0
    requires allNodes == seqToSet(configuration.nodes);
    ensures && AdversaryInit(seqAdvStates[0], configuration)
            && (forall i:nat ::
                    pLemmajkfladjklfaGetAdvStatesHelper(dsBehaviour, seqAdvStates, i)
                    // var step := dsBehaviour.adversaryBehaviour.steps[i];
                    // && AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
            )
        ;   
    ensures seqAdvStates[0].byz == allNodes - dsBehaviour.nodesBehaviours.Keys     
    {
        var byz := allNodes - dsBehaviour.nodesBehaviours.Keys;
        seqAdvStates :| 
            && AdversaryInit(seqAdvStates[0], configuration)
            && seqAdvStates[0].byz == byz
            && (forall i:nat ::
                    var step := dsBehaviour.adversaryBehaviour.steps[i];
                    && AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
            )
        ;           
    }

    lemma lemmajkfladjklfaGetAdvStatesHelper2(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,
        allNodes: set<Address>,
        seqNodes: iseq<Address>,
        seqAdvStatesOrig: iseq<Adversary>,
        seqAdvStates: iseq<Adversary>  
    ) 
    requires IsValidConfiguration(configuration)
    requires dsBehaviour in DSSpecificationBuilder(configuration).behaviours
    requires  |validators([configuration.genesisBlock])| > 0
    requires allNodes == seqToSet(configuration.nodes);
    requires && AdversaryInit(seqAdvStatesOrig[0], configuration)
            && (forall i:nat ::
                    pLemmajkfladjklfaGetAdvStatesHelper(dsBehaviour, seqAdvStatesOrig, i)
                    // var step := dsBehaviour.adversaryBehaviour.steps[i];
                    // && AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
            )
        ;        
    requires
            var byz := allNodes - dsBehaviour.nodesBehaviours.Keys;  
            seqAdvStates ==   
                imap i: nat :: 
                    var stepsTakeByNodeSoFar := getStepsTakeByAversarySoFar(seqNodes, byz, i);
                    seqAdvStatesOrig[stepsTakeByNodeSoFar];
    ensures && AdversaryInit(seqAdvStates[0], configuration)
    ensures 
                var byz := allNodes - dsBehaviour.nodesBehaviours.Keys;
                var adversarySpecificationBehaviour := dsBehaviour.adversaryBehaviour;
            forall i: nat ::
                if seqNodes[i] in byz then
                    var stepsTakenByNodeSoFar := getStepsTakeByAversarySoFar(seqNodes, byz, i);
                    var step := adversarySpecificationBehaviour.steps[stepsTakenByNodeSoFar];
                    AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
                else
                    seqAdvStates[i] == seqAdvStates[i+1];  

    // ensures seqAdvStates[0].byz == allNodes - dsBehaviour.nodesBehaviours.Keys   
    {

        var byz := allNodes - dsBehaviour.nodesBehaviours.Keys;
        var adversarySpecificationBehaviour := dsBehaviour.adversaryBehaviour;

        forall i: nat 
        ensures
            if seqNodes[i] in byz then
                var stepsTakenByNodeSoFar := getStepsTakeByAversarySoFar(seqNodes, byz, i);
                var step := adversarySpecificationBehaviour.steps[stepsTakenByNodeSoFar];
                AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
            else
                seqAdvStates[i] == seqAdvStates[i+1];
        {
            lemmaGetStepsTakeByAdversarySoFar(seqNodes, byz, i);
            if seqNodes[i] in byz 
            {
                var stepsTakenByNodeSoFar := getStepsTakeByAversarySoFar(seqNodes, byz, i);
                assert getStepsTakeByAversarySoFar(seqNodes, byz, i + 1) == stepsTakenByNodeSoFar + 1;

                assert seqAdvStates[i] == seqAdvStatesOrig[stepsTakenByNodeSoFar];
                assert seqAdvStates[i+1] == seqAdvStatesOrig[stepsTakenByNodeSoFar+1];

                // lemmaGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, nt, stepsTakenByNodeSoFar);

                // // assert IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,stepsTakenByNodeSoFar);
                // assert validNodeState(seqNodeStates[i]); 
                // assert validNodeState(nt[stepsTakenByNodeSoFar]); 
                var step := adversarySpecificationBehaviour.steps[stepsTakenByNodeSoFar];
                assert pLemmajkfladjklfaGetAdvStatesHelper(dsBehaviour, seqAdvStatesOrig, stepsTakenByNodeSoFar);
                assert AdversaryNext(seqAdvStatesOrig[stepsTakenByNodeSoFar], step.messageReceived, seqAdvStatesOrig[stepsTakenByNodeSoFar+1], step.messagesToSend);
                assert AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend);
                // assert NodeNext(nt[stepsTakenByNodeSoFar], step.messageReceived, nt[stepsTakenByNodeSoFar+1], step.messagesToSend);
                // assert NodeNext(seqNodeStates[i], step.messageReceived, seqNodeStates[i+1], step.messagesToSend);
            }
            else
            {
                assert seqAdvStates[i] == seqAdvStates[i+1];
            }
        }        
    }


    lemma lemmajkfladjklfaGetAdvStates(
       dsBehaviour: DSBehaviour,
       configuration: Configuration,
       allNodes: set<Address>,
       seqNodes: iseq<Address>
    ) returns (seqAdvStates: iseq<Adversary>)
    requires IsValidConfiguration(configuration)
    requires dsBehaviour in DSSpecificationBuilder(configuration).behaviours
    requires  |validators([configuration.genesisBlock])| > 0
    requires allNodes == seqToSet(configuration.nodes);
    // ensures && AdversaryInit(seqAdvStates[0], configuration)
    //         && (forall i:nat ::
    //                 var step := dsBehaviour.adversaryBehaviour.steps[i];
    //                 && AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
    //         )
    //     ;   
    ensures seqAdvStates[0].byz == allNodes - dsBehaviour.nodesBehaviours.Keys 
    ensures forall i: nat ::  seqAdvStates[0].byz == seqAdvStates[i].byz
    ensures AdversaryInit(seqAdvStates[0], configuration)
    ensures 
        var adversarySpecificationBehaviour := dsBehaviour.adversaryBehaviour;
        var byz := allNodes - dsBehaviour.nodesBehaviours.Keys;
        forall i: nat ::
            if seqNodes[i] in byz then
                var stepsTakenByNodeSoFar := getStepsTakeByAversarySoFar(seqNodes, byz, i);
                var step := adversarySpecificationBehaviour.steps[stepsTakenByNodeSoFar];
                AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
            else
                seqAdvStates[i] == seqAdvStates[i+1];        
    {      
        var byz := allNodes - dsBehaviour.nodesBehaviours.Keys;
        var seqAdvStatesOrig := lemmajkfladjklfaGetAdvStatesHelper(dsBehaviour, configuration, allNodes);
        // var seqAdvStatesOrig: iseq<Adversary> :| 
        //     && AdversaryInit(seqAdvStatesOrig[0], configuration)
        //     && seqAdvStatesOrig[0].byz == byz
        //     && (forall i:nat ::
        //             var step := dsBehaviour.adversaryBehaviour.steps[i];
        //             && AdversaryNext(seqAdvStatesOrig[i], step.messageReceived, seqAdvStatesOrig[i+1], step.messagesToSend)
        //     )
        // ;    

        assert seqAdvStatesOrig[0].byz == allNodes - dsBehaviour.nodesBehaviours.Keys;

        seqAdvStates := 
            imap i: nat :: 
            var stepsTakeByNodeSoFar := getStepsTakeByAversarySoFar(seqNodes, byz, i);
            seqAdvStatesOrig[stepsTakeByNodeSoFar];

        var adversarySpecificationBehaviour := dsBehaviour.adversaryBehaviour;

        forall i: nat 
        ensures
            if seqNodes[i] in byz then
                var stepsTakenByNodeSoFar := getStepsTakeByAversarySoFar(seqNodes, byz, i);
                var step := adversarySpecificationBehaviour.steps[stepsTakenByNodeSoFar];
                AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
            else
                seqAdvStates[i] == seqAdvStates[i+1];
        {
            lemmajkfladjklfaGetAdvStatesHelper2(dsBehaviour, configuration, allNodes, seqNodes, seqAdvStatesOrig, seqAdvStates);
        }

        forall i: nat
        ensures seqAdvStatesOrig[0].byz == seqAdvStatesOrig[i].byz
        {
            lemmajkfladjklfaGetDsStatesHelper(dsBehaviour, configuration, seqAdvStatesOrig, i);
        }

        assert forall i: nat :: seqAdvStates[0].byz == seqAdvStates[i].byz;
    }

    predicate lemmajkfladjklfaGetEnvStatesHelper(
        seqEnvStates: iseq<Network>,
        environmentSpecificationBehaviour: EnvironmentSpecificationBehaviour,
        i: nat
    )
    {
        var step := environmentSpecificationBehaviour.steps[i];
        && NetworkNext(seqEnvStates[i], seqEnvStates[i+1], step.messagesSentByTheNodes, step.messagesReceivedByTheNodes)
    }

    lemma lemmajkfladjklfaGetEnvStates(
       dsBehaviour: DSBehaviour,
       configuration: Configuration
    ) returns (seqEnvStates: iseq<Network>)
    requires IsValidConfiguration(configuration)
    requires dsBehaviour in DSSpecificationBuilder(configuration).behaviours
    ensures     && NetworkInit(seqEnvStates[0], configuration)
                && (forall i:nat ::
                        lemmajkfladjklfaGetEnvStatesHelper(seqEnvStates, dsBehaviour.environmentBehaviour, i)
                        // var step := dsBehaviour.environmentBehaviour.steps[i];
                        // && NetworkNext(seqEnvStates[i], seqEnvStates[i+1], step.messagesSentByTheNodes, step.messagesReceivedByTheNodes)
                )
    {
        seqEnvStates :|
                && NetworkInit(seqEnvStates[0], configuration)
                && (forall i:nat ::
                        var step := dsBehaviour.environmentBehaviour.steps[i];
                        && NetworkNext(seqEnvStates[i], seqEnvStates[i+1], step.messagesSentByTheNodes, step.messagesReceivedByTheNodes)
                )
        ;       
         
    }

    function getStepsTakeByNodeSoFar(
        seqNodes: iseq<Address>,
        node: Address,
        step: nat
    ): nat 
    {
        var stepsTakenByNode :=
            set i: nat |
                && i < step 
                && seqNodes[i] == node
            ;

        |stepsTakenByNode|
    }

    function getStepsTakeByAversarySoFar(
        seqNodes: iseq<Address>,
        byz: set<Address>,
        step: nat
    ): nat     
    {
        var stepsTakenByAdversary :=
            set i: nat |
                && i < step 
                && seqNodes[i] in byz
            ;

        |stepsTakenByAdversary|        
    }    


    function getStepsTakeByNodeSoFarReverseHelper(
        seqNodes: iseq<Address>,
        node: Address,
        ret: nat,
        test: nat
    ): (inv: nat)
    requires getStepsTakeByNodeSoFar(seqNodes,node, test) >= ret 
    ensures getStepsTakeByNodeSoFar(seqNodes, node, inv) == ret 
    {
        if getStepsTakeByNodeSoFar(seqNodes, node, test) == ret then 
            test 
        else
            assert test > 0 by {
                if test == 0 
                {
                    assert getStepsTakeByNodeSoFar(seqNodes, node, test) == 0;
                    assert ret == 0;
                    assert false;
                }
            }
            var retTest := getStepsTakeByNodeSoFar(seqNodes, node, test);
            assert retTest > 0;
            var retTestMinusOne := getStepsTakeByNodeSoFar(seqNodes, node, test-1);
            lemmaGetStepsTakeByNodeSoFar(seqNodes, node, test - 1);
            assert retTest -1 <= retTestMinusOne <= retTest;

            var inv := getStepsTakeByNodeSoFarReverseHelper(seqNodes, node, ret, test-1);
            inv
    }

    // predicate pGetStepsTakeByNodeSoFarReversePrecondition(
    //     seqNodes: iseq<Address>,
    //     node: Address,
    //     ret: nat
    // ): (inv: nat)

    function getStepsTakeByNodeSoFarReverse(
        seqNodes: iseq<Address>,
        node: Address,
        ret: nat
    ): (inv: nat)
    requires exists bound: nat :: getStepsTakeByNodeSoFar(seqNodes,node, bound) >= ret
    ensures getStepsTakeByNodeSoFar(seqNodes, node, inv) == ret 
    {
        var bound: nat :| getStepsTakeByNodeSoFar(seqNodes,node, bound) >= ret;
        getStepsTakeByNodeSoFarReverseHelper(seqNodes, node, ret, bound)
    }

    lemma lemmaGetStepsTakeByNodeSoFar
    (
        seqNodes: iseq<Address>,
        node: Address,
        step: nat        
    )
    ensures 
        if seqNodes[step] == node  then
            getStepsTakeByNodeSoFar(seqNodes,node, step) + 1 == getStepsTakeByNodeSoFar(seqNodes, node, step +1)
        else
            getStepsTakeByNodeSoFar(seqNodes,node, step)  == getStepsTakeByNodeSoFar(seqNodes, node, step +1)

    ensures getStepsTakeByNodeSoFar(seqNodes,node, step)  <= getStepsTakeByNodeSoFar(seqNodes, node, step +1)
    {
        assert getStepsTakeByNodeSoFar(seqNodes,node, 0) == 0;
        var stepsTakenByNode :=
            set i: nat |
                && i < step 
                && seqNodes[i] == node
            ;

        var stepsTakenByNodePlusOne :=
            set i: nat |
                && i < (step + 1)
                && seqNodes[i] == node
            ;   

        
        if seqNodes[step] == node 
        {
            assert step !in stepsTakenByNode;
            assert stepsTakenByNodePlusOne == stepsTakenByNode + {step};
            assert |stepsTakenByNode| + 1 == |stepsTakenByNodePlusOne|;
            assert getStepsTakeByNodeSoFar(seqNodes,node, step) + 1 == getStepsTakeByNodeSoFar(seqNodes, node, step +1);
        }
        else
        {
            assert stepsTakenByNodePlusOne == stepsTakenByNode;
            assert |stepsTakenByNode| == |stepsTakenByNodePlusOne|;
            assert getStepsTakeByNodeSoFar(seqNodes,node, step)  == getStepsTakeByNodeSoFar(seqNodes, node, step +1);            
        }
    }

    lemma lemmaGetStepsTakeByAdversarySoFar
    (
        seqNodes: iseq<Address>,
        byz: set<Address>,
        step: nat        
    )
    ensures 
        if seqNodes[step] in byz  then
            getStepsTakeByAversarySoFar(seqNodes, byz, step) + 1 == getStepsTakeByAversarySoFar(seqNodes, byz, step +1)
        else
            getStepsTakeByAversarySoFar(seqNodes, byz, step) == getStepsTakeByAversarySoFar(seqNodes, byz, step +1)
    {
        // assert getStepsTakeByNodeSoFar(seqNodes,node, 0) == 0;
        var stepsTakenByNode :=
            set i: nat |
                && i < step 
                && seqNodes[i] in byz
            ;

        var stepsTakenByNodePlusOne :=
            set i: nat |
                && i < (step + 1)
                && seqNodes[i] in byz
            ;   

        
        if seqNodes[step] in byz
        {
            assert step !in stepsTakenByNode;
            assert stepsTakenByNodePlusOne == stepsTakenByNode + {step};
            assert |stepsTakenByNode| + 1 == |stepsTakenByNodePlusOne|;
            assert getStepsTakeByAversarySoFar(seqNodes, byz, step) + 1 == getStepsTakeByAversarySoFar(seqNodes, byz, step +1);
        }
        else
        {
            assert stepsTakenByNodePlusOne == stepsTakenByNode;
            assert |stepsTakenByNode| == |stepsTakenByNodePlusOne|;
            assert getStepsTakeByAversarySoFar(seqNodes, byz, step) == getStepsTakeByAversarySoFar(seqNodes, byz, step +1);      
        }
    }    

    lemma lemmaGetSeqHonestNodeStatesHelper(
        QbftNodeBehaviour: QbftNodeBehaviour,
        nt: iseq<NodeState>,
        i: nat
    )
    requires IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i);
    ensures validNodeState(nt[i])
    ensures 
                var step := QbftNodeBehaviour.steps[i];
                NodeNext(nt[i], step.messagesReceived, nt[i+1], step.messagesToSend);
    {  }

    predicate pGetSeqHonestNodeStatesHelper(
        QbftNodeBehaviour: QbftNodeBehaviour,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>,
        n: Address,
        i: nat
    )
    {
        if seqNodes[i] == n then 
            var stepsTakenByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
            var step := QbftNodeBehaviour.steps[stepsTakenByNodeSoFar];
            && validNodeState(seqNodeStates[i])
            && NodeNext(seqNodeStates[i], step.messagesReceived, seqNodeStates[i+1], step.messagesToSend)
            // && step.newBlockchain == seqNodeStates[i+1].blockchain
        else
            seqNodeStates[i] == seqNodeStates[i+1]        
    }

    // lemma lemmaHonestNodesAllValidsRecursive(
    //     QbftNodeBehaviour: QbftNodeBehaviour,
    //     nt: iseq<NodeState>,
    //     configuration: Configuration,
    //     n: Address,
    //     i: nat
    // )
    // requires 
    //         && NodeInit(nt[0], configuration, n)
    //         && (forall i:nat ::
    //                 IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
    //                 // var step := QbftNodeBehaviour.steps[i];
    //                 // && validNodeState(nt[i])
    //                 // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
    //                 // && step.newBlockchain == nt[i+1].blockchain
    //         );      

    // lemma lemmaHonestNodesAllValids(
    //     QbftNodeBehaviour: QbftNodeBehaviour,
    //     nt: iseq<NodeState>,
    //     configuration: Configuration,
    //     n: Address,
    //     i: nat
    // )
    // requires 
    //         && NodeInit(nt[0], configuration, n)
    //         && (forall i:nat ::
    //                 IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
    //                 // var step := QbftNodeBehaviour.steps[i];
    //                 // && validNodeState(nt[i])
    //                 // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
    //                 // && step.newBlockchain == nt[i+1].blockchain
    //         );    
    // {
    //     if i == 0
    //     {
    //         assert validNodeState(nt[i]);
    //     }
    //     else
    //     {
    //         lemmaHonestNodesAllValidsRecursive(QbftNodeBehaviour, nt, configuration, n, i-1);

    //     }
    // }




    lemma lemmaGetSeqHonestNodeStates2Helper(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,       
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>
    ) returns (nt: iseq<NodeState>)
    requires n in dsBehaviour.nodesBehaviours
    requires IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n])
    // requires  |validators([configuration.genesisBlock])| > 0    
    requires seqNodeStates == getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes)    
    ensures var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
            && NodeInit(nt[0], configuration, n)
            && QbftNodeBehaviour.initialBlockchain == nt[0].blockchain
            && (forall i:nat ::
                    IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
                    // var step := QbftNodeBehaviour.steps[i];
                    // && validNodeState(nt[i])
                    // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
                    // && step.newBlockchain == nt[i+1].blockchain
            )
            &&  seqNodeStates == 
                imap i: nat :: 
                    var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
                    nt[stepsTakeByNodeSoFar] ;    
    {
        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        nt :|
            && NodeInit(nt[0], configuration, n)
            && QbftNodeBehaviour.initialBlockchain == nt[0].blockchain
            && (forall i:nat ::
                    IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
                    // var step := QbftNodeBehaviour.steps[i];
                    // && validNodeState(nt[i])
                    // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
                    // && step.newBlockchain == nt[i+1].blockchain
            )
            &&  seqNodeStates == 
                imap i: nat :: 
                    var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
                    nt[stepsTakeByNodeSoFar] ;         
    }

    lemma lemmaGetSeqHonestNodeStates2(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,       
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>,
        i: nat
    )
    requires n in dsBehaviour.nodesBehaviours
    requires IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n])
    requires  |validators([configuration.genesisBlock])| > 0    
    requires seqNodeStates == getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes)
    ensures validNodeState(seqNodeStates[i]);
    {
        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        lemmaGetSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes, seqNodeStates);
        var nt := lemmaGetSeqHonestNodeStates2Helper(dsBehaviour, configuration, n, seqNodes, seqNodeStates);       
        var j :| seqNodeStates[i] == nt[j];
        assert IsValidQbftBehaviourStep(QbftNodeBehaviour, nt , j);
        assert validNodeState(seqNodeStates[i]);
    }



    lemma lemmaGetSeqHonestNodeStates3Helepr(a: Blockchain, b: Blockchain, c: Blockchain)
    requires a == b 
    requires c == b
    ensures a == c
    ensures c == a
    { }

    lemma lemmaGetSeqHonestNodeStates3Helepr2(
        seqNodes: iseq<Address>,
        n: Address,
        i: nat,
        prevI: nat   
    )
    requires prevI == i - 1 
    ensures getStepsTakeByNodeSoFar(seqNodes, n, prevI) == getStepsTakeByNodeSoFar(seqNodes, n, i-1);
    {  }

    lemma lemmaGetSeqHonestNodeStates3Helper3(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,       
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>,
        i: nat
    )
    requires n in dsBehaviour.nodesBehaviours
    requires IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n])
    requires  |validators([configuration.genesisBlock])| > 0    
    requires seqNodeStates == getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes) 
    requires i > 0
    requires getStepsTakeByNodeSoFar(seqNodes, n, i) == 0;  
    ensures 
            var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
            seqNodeStates[i].blockchain ==  QbftNodeBehaviour.initialBlockchain;
    decreases i,0
    {
        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        var nt: iseq<NodeState> :|
            && NodeInit(nt[0], configuration, n)
            && QbftNodeBehaviour.initialBlockchain == nt[0].blockchain
            && (forall i:nat ::
                    IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
                    // var step := QbftNodeBehaviour.steps[i];
                    // && validNodeState(nt[i])
                    // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
                    // && step.newBlockchain == nt[i+1].blockchain
            )
            &&  seqNodeStates == 
                imap i: nat :: 
                    var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
                    nt[stepsTakeByNodeSoFar] ;

        var stpesTakenByTheNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
        var prevI:nat := i-1;
        lemmaGetSeqHonestNodeStates3(dsBehaviour, configuration, n, seqNodes, seqNodeStates, prevI);
        lemmaGetSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes, seqNodeStates);

        
        var stpesTakenByTheNodeSoFarPrev := getStepsTakeByNodeSoFar(seqNodes, n, prevI);

        lemmaGetStepsTakeByNodeSoFar(seqNodes, n, prevI);
        assert stpesTakenByTheNodeSoFarPrev == 0;
        var stepsTakenByNode :=
            set j: nat |
                && j <  i
                && seqNodes[j] == n;

        assert |stepsTakenByNode| == 0;   
        assert stepsTakenByNode == {}; 

        forall j: nat | j < i
        ensures seqNodes[j] != n
        {
            if seqNodes[j] == n 
            {
                assert j in stepsTakenByNode;   
                assert stepsTakenByNode != {};
                assert false;
            }

            assert seqNodes[j] != n;
        }

        assert seqNodes[prevI] != n;
        assert pGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, seqNodes, seqNodeStates, n, prevI);
        assert seqNodeStates[prevI] == seqNodeStates[prevI+1];
        assert seqNodeStates[prevI] == seqNodeStates[i];
        assert seqNodeStates[i].blockchain ==  QbftNodeBehaviour.initialBlockchain;                    
    } 

    lemma lemmaGetSeqHonestNodeStates3(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,       
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>,
        i: nat
    )
    requires n in dsBehaviour.nodesBehaviours
    requires IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n])
    requires  |validators([configuration.genesisBlock])| > 0    
    requires seqNodeStates == getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes)
    ensures var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
            var stpesTakenByTheNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
            if stpesTakenByTheNodeSoFar == 0 then
                seqNodeStates[i].blockchain ==  QbftNodeBehaviour.initialBlockchain
            else
                var stpesTakenByTheNodeSoFarPrev := stpesTakenByTheNodeSoFar - 1;
                var step := QbftNodeBehaviour.steps[stpesTakenByTheNodeSoFarPrev];
                seqNodeStates[i].blockchain == step.newBlockchain  
    decreases i
    {
        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        var nt: iseq<NodeState> :|
            && NodeInit(nt[0], configuration, n)
            && QbftNodeBehaviour.initialBlockchain == nt[0].blockchain
            && (forall i:nat ::
                    IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
                    // var step := QbftNodeBehaviour.steps[i];
                    // && validNodeState(nt[i])
                    // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
                    // && step.newBlockchain == nt[i+1].blockchain
            )
            &&  seqNodeStates == 
                imap i: nat :: 
                    var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
                    nt[stepsTakeByNodeSoFar] ;

        // if i == 0
        // {
        //     assert seqNodeStates[i].blockchain ==  QbftNodeBehaviour.initialBlockchain;
        //         // assert seqNodeStates[i+1].blockchain == QbftNodeBehaviour.steps[getStepsTakeByNodeSoFar(seqNodes, n, i)].newBlockchain;            
        // }
        // else 
        // {

        // }


        // var stpesTakenByTheNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);

        // lemmaGetSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes, seqNodeStates);
        // assert pGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, seqNodes, seqNodeStates, n, i);
        // assert QbftNodeBehaviour.steps[i].newBlockchain == nt[getStepsTakeByNodeSoFar(seqNodes, n, i)+1].blockchain;

        // assert stpesTakenByTheNodeSoFar > 0 ==> i > 0;
        
        var stpesTakenByTheNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
        
        if i == 0
        {
            assert seqNodeStates[i].blockchain ==  QbftNodeBehaviour.initialBlockchain;
            assert stpesTakenByTheNodeSoFar == 0;
                // assert seqNodeStates[i+1].blockchain == QbftNodeBehaviour.steps[getStepsTakeByNodeSoFar(seqNodes, n, i)].newBlockchain;            
        }
        else
        {
            var prevI:nat := i-1;
            lemmaGetSeqHonestNodeStates3(dsBehaviour, configuration, n, seqNodes, seqNodeStates, prevI);
            
            var stpesTakenByTheNodeSoFarPrev := getStepsTakeByNodeSoFar(seqNodes, n, prevI);

            lemmaGetStepsTakeByNodeSoFar(seqNodes, n, prevI);

            if stpesTakenByTheNodeSoFar == 0
            {
                lemmaGetSeqHonestNodeStates3Helper3(dsBehaviour, configuration, n, seqNodes, seqNodeStates, i);
                // assert stpesTakenByTheNodeSoFarPrev == 0;
                // var stepsTakenByNode :=
                //     set j: nat |
                //         && j <  i
                //         && seqNodes[j] == n;

                // assert |stepsTakenByNode| == 0;   
                // assert stepsTakenByNode == {}; 

                // forall j: nat | j < i
                // ensures seqNodes[j] != n
                // {
                //     if seqNodes[j] == n 
                //     {
                //         assert j in stepsTakenByNode;   
                //         assert stepsTakenByNode != {};
                //         assert false;
                //     }

                //     assert seqNodes[j] != n;
                // }

                // assert seqNodes[prevI] != n;
                // assert seqNodeStates[i-1] == seqNodeStates[i];
                // assert seqNodeStates[i].blockchain ==  QbftNodeBehaviour.initialBlockchain;
                // assume seqNodeStates[i].blockchain ==  QbftNodeBehaviour.initialBlockchain;
            }
            else
            {
                if seqNodes[prevI] == n 
                {
                    calc == {
                        getStepsTakeByNodeSoFar(seqNodes, n, prevI) + 1; 
                        getStepsTakeByNodeSoFar(seqNodes, n, prevI+1);
                        calc == {
                            prevI + 1;
                            i;
                        }
                        getStepsTakeByNodeSoFar(seqNodes, n, i);
                    }
                    assert stpesTakenByTheNodeSoFarPrev + 1 == stpesTakenByTheNodeSoFar;

                    // var stepsTakenByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
                    assert seqNodeStates[i] == nt[stpesTakenByTheNodeSoFar];
                    assert seqNodeStates[prevI] == nt[stpesTakenByTheNodeSoFarPrev];

                    assert IsValidQbftBehaviourStep(QbftNodeBehaviour, nt, stpesTakenByTheNodeSoFarPrev); 

                    // assert IsValidQbftBehaviourStep(QbftNodeBehaviour, nt, stpesTakenByTheNodeSoFar); 
                    var prevStep := QbftNodeBehaviour.steps[prevI];
                    // assert seqNodeStates[i].blockchain == prevStep.newBlockchain;
                    // assert     
                    // assert pGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, seqNodes, seqNodeStates, n, prevI);
                    var step := QbftNodeBehaviour.steps[stpesTakenByTheNodeSoFarPrev];
                    var bc := nt[stpesTakenByTheNodeSoFarPrev+1].blockchain;
                    assert step.newBlockchain ==  bc;
                    assert seqNodeStates[i].blockchain == bc; // == step.newBlockchain;


                    lemmaGetSeqHonestNodeStates3Helepr(step.newBlockchain, bc, seqNodeStates[i].blockchain);

                    assert seqNodeStates[i].blockchain == step.newBlockchain;
                    assert seqNodeStates[i].blockchain == QbftNodeBehaviour.steps[stpesTakenByTheNodeSoFarPrev].newBlockchain;

                    assert seqNodeStates[i].blockchain == QbftNodeBehaviour.steps[getStepsTakeByNodeSoFar(seqNodes, n, i)-1].newBlockchain by 
                    {
                        calc == {
                            seqNodeStates[i].blockchain; 
                            QbftNodeBehaviour.steps[getStepsTakeByNodeSoFar(seqNodes, n, prevI)].newBlockchain;
                            calc == {
                                getStepsTakeByNodeSoFar(seqNodes, n, prevI);
                                getStepsTakeByNodeSoFar(seqNodes, n, i) - 1;
                            }
                            QbftNodeBehaviour.steps[getStepsTakeByNodeSoFar(seqNodes, n, i)-1].newBlockchain;
                        }
                    }
                }
                else
                {
                    assert getStepsTakeByNodeSoFar(seqNodes, n, prevI) == getStepsTakeByNodeSoFar(seqNodes, n, prevI+1);
                    assert seqNodeStates[prevI] == seqNodeStates[prevI+1] == seqNodeStates[i];

                    assert seqNodeStates[i].blockchain == QbftNodeBehaviour.steps[getStepsTakeByNodeSoFar(seqNodes, n, i)-1].newBlockchain;
                }
            }
        }
        
        

        // forall i: nat 
        // {
        //         assert seqNodeStates[i].blockchain == nt[getStepsTakeByNodeSoFar(seqNodes, n, i)].blockchain;     

        //         assert seqNodeStates[i+1].blockchain == QbftNodeBehaviour.steps[getStepsTakeByNodeSoFar(seqNodes, n, i)].newBlockchain;             
        // }
    } 

    predicate pLemmaGetSeqHonestNodeStates4(
        seqNodes: iseq<Address>,
        n: Address,
        j: nat, 
        upperBound: nat
    )
    {
        getStepsTakeByNodeSoFar(seqNodes, n, j) <= upperBound
    }

    predicate pLemmaGetSeqHonestNodeStates42(
        seqNodes: iseq<Address>,
        n: Address,
        upperBound: nat
    )
    {
        forall j: nat :: pLemmaGetSeqHonestNodeStates4(seqNodes, n, j, upperBound)
    }    

    predicate pGetStepsTakeByNodeSoFarIsLimited
    (
        seqNodes: iseq<Address>,
        n: Address
    )
    {
        exists max:nat :: pLemmaGetSeqHonestNodeStates42(seqNodes, n, max)
    }

    function getMaxWhenGetStepsTakeByNodeSoFarIsLimitedHelper
    (
        seqNodes: iseq<Address>,
        n: Address,
        test: nat
    ) : (imaxAndMax: (nat, nat))
    requires  pLemmaGetSeqHonestNodeStates42(seqNodes, n, test)
    ensures getStepsTakeByNodeSoFar(seqNodes, n, imaxAndMax.0) == imaxAndMax.1;
    ensures pLemmaGetSeqHonestNodeStates42(seqNodes, n, imaxAndMax.1)
    {
        if test == 0 then
            var imaxAndMax := (0, 0);
            assert getStepsTakeByNodeSoFar(seqNodes, n, imaxAndMax.0) == imaxAndMax.1;
            imaxAndMax
        
        else
        
            if exists j: nat :: getStepsTakeByNodeSoFar(seqNodes, n, j) == test then
            
                var max := test;
                var imax :| getStepsTakeByNodeSoFar(seqNodes, n, imax) == max;
                var imaxAndMax := (imax, max);
                assert getStepsTakeByNodeSoFar(seqNodes, n, imax) == max;
                imaxAndMax
            
            else
                assert forall j: nat :: getStepsTakeByNodeSoFar(seqNodes, n, j) < test by
                {
                    forall j: nat 
                    ensures getStepsTakeByNodeSoFar(seqNodes, n, j) < test
                    {
                        assert getStepsTakeByNodeSoFar(seqNodes, n, j) != test;
                        assert pLemmaGetSeqHonestNodeStates4(seqNodes, n, j, test);
                        assert getStepsTakeByNodeSoFar(seqNodes, n, j) <= test;
                    }
                    // 
                }
                // assert forall j: nat :: getStepsTakeByNodeSoFar(seqNodes, n, j) < test;
                getMaxWhenGetStepsTakeByNodeSoFarIsLimitedHelper(seqNodes, n, test - 1)
            
    
    }

    function getMaxWhenGetStepsTakeByNodeSoFarIsLimited
    (
        seqNodes: iseq<Address>,
        n: Address        
    ) : (imaxAndMax: (nat, nat))
    requires pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n)
    ensures getStepsTakeByNodeSoFar(seqNodes, n, imaxAndMax.0) == imaxAndMax.1;
    ensures pLemmaGetSeqHonestNodeStates42(seqNodes, n, imaxAndMax.1)
    {
        var upperBound: nat :| pLemmaGetSeqHonestNodeStates42(seqNodes, n, upperBound);
        getMaxWhenGetStepsTakeByNodeSoFarIsLimitedHelper(seqNodes, n, upperBound)
    }    

    lemma lemmaGetStepsTakeByNodeSoFarIsLimitedHelper
    (
        seqNodes: iseq<Address>,
        n: Address,
        test: nat
    ) returns (imax: nat, max: nat)
    requires  pLemmaGetSeqHonestNodeStates42(seqNodes, n, test)
    ensures getStepsTakeByNodeSoFar(seqNodes, n, imax) == max;
    ensures pLemmaGetSeqHonestNodeStates42(seqNodes, n, max)
    {
        if test == 0
        {
            max := 0;
            imax := 0;
            assert getStepsTakeByNodeSoFar(seqNodes, n, imax) == max;
        }
        else
        {
            if exists j: nat :: getStepsTakeByNodeSoFar(seqNodes, n, j) == test
            {
                max := test;
                imax :| getStepsTakeByNodeSoFar(seqNodes, n, imax) == max;
                assert getStepsTakeByNodeSoFar(seqNodes, n, imax) == max;
            }
            else
            {
                forall j: nat 
                ensures getStepsTakeByNodeSoFar(seqNodes, n, j) < test
                {
                    assert getStepsTakeByNodeSoFar(seqNodes, n, j) != test;
                    assert pLemmaGetSeqHonestNodeStates4(seqNodes, n, j, test);
                    assert getStepsTakeByNodeSoFar(seqNodes, n, j) <= test;
                }
                // assert forall j: nat :: !(getStepsTakeByNodeSoFar(seqNodes, n, j) == test);
                // assert forall j: nat :: getStepsTakeByNodeSoFar(seqNodes, n, j) < test;
                imax, max := lemmaGetStepsTakeByNodeSoFarIsLimitedHelper(seqNodes, n, test - 1);
            }
        }
    }


    lemma lemmaGetStepsTakeByNodeSoFarIsLimited
    (
        seqNodes: iseq<Address>,
        n: Address        
    ) returns (imax: nat, max: nat)
    requires pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n)
    ensures getStepsTakeByNodeSoFar(seqNodes, n, imax) == max;
    ensures pLemmaGetSeqHonestNodeStates42(seqNodes, n, max)
    {
        var upperBound: nat :| pLemmaGetSeqHonestNodeStates42(seqNodes, n, upperBound);
        imax, max := lemmaGetStepsTakeByNodeSoFarIsLimitedHelper(seqNodes, n, upperBound);
    }

    // lemma lemmaGetSeqHonestNodeStates4Recursive(
    //     dsBehaviour: DSBehaviour,
    //     configuration: Configuration,       
    //     n: Address,
    //     seqNodes: iseq<Address>,
    //     seqNodeStates: iseq<NodeState>,
    //     i: nat
    // )
    // requires n in dsBehaviour.nodesBehaviours
    // requires dsBehaviour.nodesBehaviours[n] in QbftSpecificationBuilder(configuration, n).behaviours
    // requires  |validators([configuration.genesisBlock])| > 0    
    // requires seqNodeStates == getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes)
    // // ensures var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
    // //         var stpesTakenByTheNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
    // //         if stpesTakenByTheNodeSoFar == 0 then
    // //             seqNodeStates[i].blockchain ==  QbftNodeBehaviour.initialBlockchain
    // //         else
    // //             var stpesTakenByTheNodeSoFarPrev := stpesTakenByTheNodeSoFar - 1;
    // //             var step := QbftNodeBehaviour.steps[stpesTakenByTheNodeSoFarPrev];
    // //             seqNodeStates[i].blockchain == step.newBlockchain  

    predicate pLemmaGetSeqHonestNodeStates4ForAll(
        dsBehaviour: DSBehaviour,
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>,
        i: nat
    )
    {
        && n in dsBehaviour.nodesBehaviours
        && getStepsTakeByNodeSoFarReverse.requires(seqNodes, n, i + 1)
        && var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        QbftNodeBehaviour.steps[i].newBlockchain == seqNodeStates[getStepsTakeByNodeSoFarReverse(seqNodes, n, i + 1)].blockchain        
    }

    predicate pLemmaGetSeqHonestNodeStates4ForAll2(
        dsBehaviour: DSBehaviour,
        n: Address,
        seqNodes: iseq<Address>,
        seqDsStates: iseq<DSState>,
        i: nat
    )
    {
        && getStepsTakeByNodeSoFarReverse.requires(seqNodes, n, i + 1)
        && n in dsBehaviour.nodesBehaviours
        && var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        var inv := getStepsTakeByNodeSoFarReverse(seqNodes, n, i + 1);
        && n in seqDsStates[inv].nodes
        && QbftNodeBehaviour.steps[i].newBlockchain == seqDsStates[inv].nodes[n].blockchain        
    }    

    lemma lemmaGetSeqHonestNodeStates4ForAll(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,       
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>
    )
    requires n in dsBehaviour.nodesBehaviours
    requires IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n])
    requires  |validators([configuration.genesisBlock])| > 0    
    requires seqNodeStates == getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes)
    ensures 
            if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n) then
                forall i: nat | i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1 :: pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates, i) 
            else
                forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates, i) 
    {
        if !pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n)
        {
            forall i: nat 
            ensures pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates, i)          
            {
                lemmaGetSeqHonestNodeStates4(dsBehaviour, configuration, n, seqNodes, seqNodeStates, i);
            }
        }
        else
        {
            forall i: nat | i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1
            ensures pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates, i)              
            {
                lemmaGetSeqHonestNodeStates4(dsBehaviour, configuration, n, seqNodes, seqNodeStates, i);
            }
        }
    }

    lemma lemmaGetSeqHonestNodeStates4(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,       
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>,
        i: nat
    )
    requires n in dsBehaviour.nodesBehaviours
    requires IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n])
    requires  |validators([configuration.genesisBlock])| > 0    
    requires seqNodeStates == getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes)
    requires 
                || !pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n)
                || (
                    && pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n)
                    && i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1
                )
    ensures getStepsTakeByNodeSoFarReverse.requires(seqNodes, n, i + 1);
    // ensures exists bound: nat :: getStepsTakeByNodeSoFar(seqNodes,n, bound) >= i + 1
    ensures var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
            QbftNodeBehaviour.steps[i].newBlockchain == seqNodeStates[getStepsTakeByNodeSoFarReverse(seqNodes, n, i + 1)].blockchain;
    // ensures var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
    //         var stpesTakenByTheNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
    //         if stpesTakenByTheNodeSoFar == 0 then
    //             seqNodeStates[i].blockchain ==  QbftNodeBehaviour.initialBlockchain
    //         else
    //             var stpesTakenByTheNodeSoFarPrev := stpesTakenByTheNodeSoFar - 1;
    //             var step := QbftNodeBehaviour.steps[stpesTakenByTheNodeSoFarPrev];
    //             seqNodeStates[i].blockchain == step.newBlockchain  
    // decreases i
    {
        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        var nt: iseq<NodeState> :|
            && NodeInit(nt[0], configuration, n)
            && QbftNodeBehaviour.initialBlockchain == nt[0].blockchain
            && (forall i:nat ::
                    IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
                    // var step := QbftNodeBehaviour.steps[i];
                    // && validNodeState(nt[i])
                    // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
                    // && step.newBlockchain == nt[i+1].blockchain
            )
            &&  seqNodeStates == 
                imap i: nat :: 
                    var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
                    nt[stepsTakeByNodeSoFar] ;  

        var step := QbftNodeBehaviour.steps[i];

        assert IsValidQbftBehaviourStep(QbftNodeBehaviour, nt, i);

        assert step.newBlockchain == nt[i+1].blockchain;


        if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n)
        {
            var (imax, max) := getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n);

            assert i + 1 <= max;
            // {
            var inv := getStepsTakeByNodeSoFarReverse(seqNodes, n, i + 1);
            assert step.newBlockchain == seqNodeStates[getStepsTakeByNodeSoFarReverse(seqNodes, n, i + 1)].blockchain;

            assert exists bound: nat :: getStepsTakeByNodeSoFar(seqNodes,n, bound) >= i + 1;
            // }
            // var max :| 
            //     && (exists j :: getStepsTakeByNodeSoFar(seqNodes, n, j) == max)
            //     && pLemmaGetSeqHonestNodeStates42(seqNodes, n, max)
            //     ;
            // var max :| pLemmaGetSeqHonestNodeStates42(seqNodes, n, max);
            // if i + 1 <= max 
            // {

            //     // assert getStepsTakeByNodeSoFar(seqNodes,n, max) >= i + 1;
            //     // var inv := getStepsTakeByNodeSoFarReverse(seqNodes, n, i + 1);
            // }

        }
        else
        {
            // assert exists bound :: getStepsTakeByNodeSoFar(seqNodes, n, bound) >= i + 1;

            // assert forall max: nat:: !(forall j: nat :: getStepsTakeByNodeSoFar(seqNodes, n, j) <= max);

            assert !(exists max:nat :: pLemmaGetSeqHonestNodeStates42(seqNodes, n, max));
            assert forall max: nat :: !pLemmaGetSeqHonestNodeStates42(seqNodes, n, max);

            assert !pLemmaGetSeqHonestNodeStates42(seqNodes, n, i+1);
            assert exists j:nat :: !pLemmaGetSeqHonestNodeStates4(seqNodes, n, j, i +1);
            var bound :| !pLemmaGetSeqHonestNodeStates4(seqNodes, n, bound, i +1);
            assert getStepsTakeByNodeSoFar(seqNodes, n, bound) >= i + 1;

            var inv := getStepsTakeByNodeSoFarReverse(seqNodes, n, i + 1);

            assert step.newBlockchain == seqNodeStates[getStepsTakeByNodeSoFarReverse(seqNodes, n, i + 1)].blockchain;

            assert exists bound: nat :: getStepsTakeByNodeSoFar(seqNodes,n, bound) >= i + 1;

            // assert !(forall max: nat, j:nat :: getStepsTakeByNodeSoFar(seqNodes, n, j) <= max);
        }

        assert getStepsTakeByNodeSoFarReverse.requires(seqNodes, n, i + 1);
        
    }   

    lemma lemmaGetSeqHonestNodeStates5(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,       
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>
    )
    requires n in dsBehaviour.nodesBehaviours
    requires IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n])
    requires  |validators([configuration.genesisBlock])| > 0    
    requires seqNodeStates == getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes)  
    ensures seqNodeStates[0].blockchain == dsBehaviour.nodesBehaviours[n].initialBlockchain;
    {
        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        var nt: iseq<NodeState> :|
            && NodeInit(nt[0], configuration, n)
            && QbftNodeBehaviour.initialBlockchain == nt[0].blockchain
            && (forall i:nat ::
                    IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
                    // var step := QbftNodeBehaviour.steps[i];
                    // && validNodeState(nt[i])
                    // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
                    // && step.newBlockchain == nt[i+1].blockchain
            )
            &&  seqNodeStates == 
                imap i: nat :: 
                    var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
                    nt[stepsTakeByNodeSoFar] ;  

        assert seqNodeStates[0] == nt[0];
        assert seqNodeStates[0].blockchain == dsBehaviour.nodesBehaviours[n].initialBlockchain;
    }  

    predicate pLemmaGetSeqHonestNodeStates3ForAll2
    (
        dsBehaviour: DSBehaviour,   
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeState: NodeState,
        i: nat
    )
    {
        && n in dsBehaviour.nodesBehaviours
        &&
        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        var stpesTakenByTheNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
        seqNodeState.blockchain ==
            if stpesTakenByTheNodeSoFar == 0 then
                QbftNodeBehaviour.initialBlockchain
            else
                var stpesTakenByTheNodeSoFarPrev := stpesTakenByTheNodeSoFar - 1;
                var step := QbftNodeBehaviour.steps[stpesTakenByTheNodeSoFarPrev];
                step.newBlockchain
    }  

    predicate pLemmaGetSeqHonestNodeStates3ForAll
    (
        dsBehaviour: DSBehaviour,   
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>,
        i: nat
    )
    {
        && n in dsBehaviour.nodesBehaviours
        &&
        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        var stpesTakenByTheNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
        seqNodeStates[i].blockchain ==
            if stpesTakenByTheNodeSoFar == 0 then
                QbftNodeBehaviour.initialBlockchain
            else
                var stpesTakenByTheNodeSoFarPrev := stpesTakenByTheNodeSoFar - 1;
                var step := QbftNodeBehaviour.steps[stpesTakenByTheNodeSoFarPrev];
                step.newBlockchain
    }

    lemma lemmaGetSeqHonestNodeStates3ForAll(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,       
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>
    )
    requires n in dsBehaviour.nodesBehaviours
    requires IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n])
    requires  |validators([configuration.genesisBlock])| > 0    
    requires seqNodeStates == getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes)

    ensures 
            forall i: nat :: pLemmaGetSeqHonestNodeStates3ForAll(dsBehaviour, n, seqNodes, seqNodeStates, i)
  
    // decreases i
    {
        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        var nt: iseq<NodeState> :|
            && NodeInit(nt[0], configuration, n)
            && QbftNodeBehaviour.initialBlockchain == nt[0].blockchain
            && (forall i:nat ::
                    IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
                    // var step := QbftNodeBehaviour.steps[i];
                    // && validNodeState(nt[i])
                    // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
                    // && step.newBlockchain == nt[i+1].blockchain
            )
            &&  seqNodeStates == 
                imap i: nat :: 
                    var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
                    nt[stepsTakeByNodeSoFar] ; 

        forall i: nat 
        ensures pLemmaGetSeqHonestNodeStates3ForAll(dsBehaviour, n, seqNodes, seqNodeStates, i)
        
        // var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        //         var stpesTakenByTheNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
        //         if stpesTakenByTheNodeSoFar == 0 then
        //             seqNodeStates[i].blockchain ==  QbftNodeBehaviour.initialBlockchain
        //         else
        //             var stpesTakenByTheNodeSoFarPrev := stpesTakenByTheNodeSoFar - 1;
        //             var step := QbftNodeBehaviour.steps[stpesTakenByTheNodeSoFarPrev];
        //             seqNodeStates[i].blockchain == step.newBlockchain          
        {
            lemmaGetSeqHonestNodeStates3(
                dsBehaviour,
                configuration,
                n,
                seqNodes,
                seqNodeStates,
                i
            );
        }        

    }

    lemma lemmaGetSeqHonestNodeStates(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,       
        n: Address,
        seqNodes: iseq<Address>,
        seqNodeStates: iseq<NodeState>
    )
    requires n in dsBehaviour.nodesBehaviours
    requires IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n])
    requires  |validators([configuration.genesisBlock])| > 0    
    requires seqNodeStates == getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes)
    ensures var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
            forall i:nat ::
                pGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, seqNodes, seqNodeStates, n, i)
                // if seqNodes[i] == n then 
                //     var stepsTakenByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
                //     var step := QbftNodeBehaviour.steps[stepsTakenByNodeSoFar];
                //     && validNodeState(seqNodeStates[i])
                //     && NodeNext(seqNodeStates[i], step.messageReceived, seqNodeStates[i+1], step.messagesToSend)
                // else
                //     seqNodeStates[i] == seqNodeStates[i+1]
    {
        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        var nt: iseq<NodeState> :|
            && NodeInit(nt[0], configuration, n)
            && QbftNodeBehaviour.initialBlockchain == nt[0].blockchain
            && (forall i:nat ::
                    IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
                    // var step := QbftNodeBehaviour.steps[i];
                    // && validNodeState(nt[i])
                    // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
                    // && step.newBlockchain == nt[i+1].blockchain
            )
            &&  seqNodeStates == 
                imap i: nat :: 
                    var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
                    nt[stepsTakeByNodeSoFar] ;   

        // assert forall i: nat :: IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i); 
        // assert forall i: nat :: validNodeState(nt[i]);  

        // forall i: nat 
        // ensures validNodeState(nt[i]); 
        // {
        //     assert IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i);
        //     assert validNodeState(nt[i]); 
        // }

        forall i: nat 
        ensures 
            pGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, seqNodes, seqNodeStates, n, i)
            // if seqNodes[i] == n then 
            //     var stepsTakenByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
            //     var step := QbftNodeBehaviour.steps[stepsTakenByNodeSoFar];
            //     && validNodeState(seqNodeStates[i])
            //     && NodeNext(seqNodeStates[i], step.messageReceived, seqNodeStates[i+1], step.messagesToSend)
            // else
            //     seqNodeStates[i] == seqNodeStates[i+1]
        {
            lemmaGetStepsTakeByNodeSoFar(seqNodes, n, i);
            if seqNodes[i] == n 
            {
                var stepsTakenByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
                assert getStepsTakeByNodeSoFar(seqNodes, n, i + 1) == stepsTakenByNodeSoFar + 1;

                assert seqNodeStates[i] == nt[stepsTakenByNodeSoFar];

                lemmaGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, nt, stepsTakenByNodeSoFar);

                // assert IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,stepsTakenByNodeSoFar);
                assert validNodeState(seqNodeStates[i]); 
                assert validNodeState(nt[stepsTakenByNodeSoFar]); 
                var step := QbftNodeBehaviour.steps[stepsTakenByNodeSoFar];
                assert NodeNext(nt[stepsTakenByNodeSoFar], step.messagesReceived, nt[stepsTakenByNodeSoFar+1], step.messagesToSend);
                assert NodeNext(seqNodeStates[i], step.messagesReceived, seqNodeStates[i+1], step.messagesToSend);

               
            }
            else
            {
                assert seqNodeStates[i] == seqNodeStates[i+1];
            }


        }


        // forall i: nat 
        // {
        //         assert seqNodeStates[i].blockchain == nt[getStepsTakeByNodeSoFar(seqNodes, n, i)].blockchain;     

        //         assert seqNodeStates[i+1].blockchain == QbftNodeBehaviour.steps[getStepsTakeByNodeSoFar(seqNodes, n, i)].newBlockchain;             
        // }
    }

    // function getSeqAdvStates(
    //     dsBehaviour: DSBehaviour,
    //     configuration: Configuration,       
    //     n: Address,
    //     seqNodes: iseq<Address>
    // ): (ret: iseq<Adversary>)
    // requires n in dsBehaviour.nodesBehaviours
    // requires dsBehaviour.adversaryBehaviour in AdversarySpecificationBuilder(configuration, n).behaviours
    // requires  |validators([configuration.genesisBlock])| > 0
    // // ensures NodeInit(ret[0], configuration, n)
    // {
    //     var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
    //     var seqAdvStates: iseq<Adversary> :|
    //         && AdversaryInit(seqAdvStates[0], configuration)
    //         && seqAdvStates[0].byz == allNodes - dsBehaviour.nodesBehaviours.Keys
    //         && (forall i:nat ::
    //                 var step := dsBehaviour.adversaryBehaviour.steps[i];
    //                 && AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
    //         );
    //     imap i: nat :: 
    //         var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
    //         nt[stepsTakeByNodeSoFar]   
    // }  


    function getSeqHonestNodeStates(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,       
        n: Address,
        seqNodes: iseq<Address>
    ): (ret: iseq<NodeState>)
    requires n in dsBehaviour.nodesBehaviours
    requires IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n])
    requires  |validators([configuration.genesisBlock])| > 0
    // ensures NodeInit(ret[0], configuration, n)
    {
        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n];
        var nt: iseq<NodeState> :|
            && NodeInit(nt[0], configuration, n)
            && QbftNodeBehaviour.initialBlockchain == nt[0].blockchain
            && (forall i:nat ::
                    IsValidQbftBehaviourStep(QbftNodeBehaviour, nt ,i)
                    // var step := QbftNodeBehaviour.steps[i];
                    // && validNodeState(nt[i])
                    // && NodeNext(nt[i], step.messageReceived, nt[i+1], step.messagesToSend)
                    // && step.newBlockchain == nt[i+1].blockchain
            );
        imap i: nat :: 
            var stepsTakeByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
            nt[stepsTakeByNodeSoFar]   
    }    

    function getSeqNodeStates(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,       
        n: Address,
        honestNodes: set<Address>,
        seqNodes: iseq<Address>
    ): (seqNodeStates: iseq<NodeState>)
    requires n in honestNodes ==> n in dsBehaviour.nodesBehaviours
    requires n in honestNodes ==> IsValidQbftBehaviour(configuration, n, dsBehaviour.nodesBehaviours[n])
    requires  |validators([configuration.genesisBlock])| > 0
    // ensures 
    // ensures
    //     var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n]; 
    //     n in honestNodes ==>
    //         (
    //             forall i:nat ::
    //                 if seqNodes[i] == n then 
    //                     var stepsTakenByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, n, i);
    //                     var step := QbftNodeBehaviour.steps[stepsTakenByNodeSoFar];
    //                     && validNodeState(seqNodeStates[i])
    //                     && NodeNext(seqNodeStates[i], step.messageReceived, seqNodeStates[i+1], step.messagesToSend)
    //                 else
    //                     seqNodeStates[i] == seqNodeStates[i+1]
    //         )
    // ensures NodeInit(ret[0], configuration, n)
    {
        if n in honestNodes then
                var ret := getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes);
                ret
            else
                getDummySeqNodes(configuration, n)    
    }    

    lemma lemmajkfladjklfaGetSeqNodeStates(
       dsBehaviour: DSBehaviour,
       configuration: Configuration,
       allNodes: set<Address>,
       honestNodes: set<Address>,
       seqNodes: iseq<Address>     
    ) returns ( seqsNodeStates: map<Address, iseq<NodeState>>)
    requires IsValidConfiguration(configuration)
    requires dsBehaviour in DSSpecificationBuilder(configuration).behaviours
    requires  |validators([configuration.genesisBlock])| > 0
    requires allNodes == seqToSet(configuration.nodes);
    requires honestNodes == dsBehaviour.nodesBehaviours.Keys; 
    ensures  seqsNodeStates.Keys == allNodes  
    ensures 
            forall n | n in allNodes ::
                if n in honestNodes then
                    (
                        var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n]; 
                        var seqNodeStates := seqsNodeStates[n];
                        forall i:nat ::
                            pGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, seqNodes, seqNodeStates, n, i)
                    )   
                else
                    (forall i: nat :: seqsNodeStates[n][0] == seqsNodeStates[n][i])
    ensures forall n | n in allNodes :: NodeInit(seqsNodeStates[n][0], configuration, n)
    ensures forall n, i:nat | n in honestNodes :: validNodeState(seqsNodeStates[n][i])
    ensures forall n, i:nat | n in honestNodes :: pLemmaGetSeqHonestNodeStates3ForAll(dsBehaviour, n, seqNodes, seqsNodeStates[n], i)
    ensures forall n | n in honestNodes ::
            if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n) then
                forall i: nat | i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1 :: pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqsNodeStates[n], i) 
            else
                forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqsNodeStates[n], i) 
    ensures forall n | n in honestNodes  ::
        (seqsNodeStates[n][0].blockchain == dsBehaviour.nodesBehaviours[n].initialBlockchain)       
    {
        seqsNodeStates
        
        :=
            map n | n in allNodes ::
                getSeqNodeStates(dsBehaviour, configuration, n, honestNodes, seqNodes)
            ;    

        forall n | n in allNodes
        ensures
            if n in honestNodes then
                (
                    var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[n]; 
                    var seqNodeStates := seqsNodeStates[n];
                    forall i:nat ::
                        pGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, seqNodes, seqNodeStates, n, i)
                )  
            else
                (
                    forall i: nat :: seqsNodeStates[n][0] == seqsNodeStates[n][i]
                )      
        ensures NodeInit(seqsNodeStates[n][0], configuration, n);
        ensures n in honestNodes ==> (forall i:nat :: validNodeState(seqsNodeStates[n][i]))
        ensures n in honestNodes ==> (forall i: nat :: pLemmaGetSeqHonestNodeStates3ForAll(dsBehaviour, n, seqNodes, seqsNodeStates[n], i))
        ensures n in honestNodes ==>
            if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n) then
                forall i: nat | i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1 :: pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqsNodeStates[n], i) 
            else
                forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqsNodeStates[n], i)  
        ensures n in honestNodes ==>  (seqsNodeStates[n][0].blockchain == dsBehaviour.nodesBehaviours[n].initialBlockchain)  
        {
            var seqNodeStates := seqsNodeStates[n];

            if n in honestNodes
            {
                assert seqNodeStates == getSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes);
                lemmaGetSeqHonestNodeStates(dsBehaviour, configuration, n, seqNodes, seqNodeStates);
                assert NodeInit(seqNodeStates[0], configuration, n);

                forall i:nat 
                ensures validNodeState(seqNodeStates[i])
                {
                    lemmaGetSeqHonestNodeStates2(dsBehaviour, configuration, n, seqNodes, seqNodeStates, i);
                }

                lemmaGetSeqHonestNodeStates3ForAll(dsBehaviour, configuration, n, seqNodes, seqsNodeStates[n]);
                lemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, configuration, n, seqNodes, seqsNodeStates[n]);

                lemmaGetSeqHonestNodeStates5(dsBehaviour, configuration, n, seqNodes, seqsNodeStates[n]);
            }
            else
            {
                assert NodeInit(seqNodeStates[0], configuration, n);
                assert forall i: nat :: seqNodeStates[0] == seqNodeStates[i];
            }
        } 

         
 
    }

    lemma lemmajkfladjklfaGetDsStates(
       configuration: Configuration,
       seqEnvStates: iseq<Network>,
       seqNodeStates: map<Address, iseq<NodeState>>,
       seqAdvStates: iseq<Adversary>,
       allNodes: set<Address>
    ) returns (dsStates: iseq<DSState>)
    requires seqNodeStates.Keys == allNodes
    ensures dsStates ==             
            imap i: nat ::
                DSState(
                    configuration,
                    seqEnvStates[i],
                    map n | n in allNodes :: seqNodeStates[n][i],
                    seqAdvStates[i]
                );
    ensures forall i: nat :: dsStates[i].nodes.Keys == allNodes
    {
        dsStates := 
            imap i: nat ::
                DSState(
                    configuration,
                    seqEnvStates[i],
                    map n | n in allNodes :: seqNodeStates[n][i],
                    seqAdvStates[i]
                );

    }

    lemma lemmajkfladjklfaGetDsStatesHelper(
        dsBehaviour: DSBehaviour,
        configuration: Configuration,
        seqAdvStates: iseq<Adversary>,
        i: nat
    )
    // requires seqNodeStates.Keys == allNodes
    // requires  dsStates == 
    //             imap i: nat ::
    //                 DSState(
    //                     configuration,
    //                     seqEnvStates[i],
    //                     map n | n in allNodes :: seqNodeStates[n][i],
    //                     seqAdvStates[i]
    //                 );
    // requires dsBehaviour.adversaryBehaviour in AdversarySpecificationBuilder(configuration).behaviours
    requires    && AdversaryInit(seqAdvStates[0], configuration)
                && (forall i:nat ::
                        pLemmajkfladjklfaGetAdvStatesHelper(dsBehaviour, seqAdvStates, i)
                        // var step := dsBehaviour.adversaryBehaviour.steps[i];
                        // && AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
                )
    ensures seqAdvStates[0].byz == seqAdvStates[i].byz
    {
        // assert seqAdvStates[0].byz == seqAdvStates[0].byz;
        for j := 0 to i
            invariant seqAdvStates[0].byz == seqAdvStates[j].byz
        {
            var step := dsBehaviour.adversaryBehaviour.steps[j];
            assert pLemmajkfladjklfaGetAdvStatesHelper(dsBehaviour, seqAdvStates, j);
            assert AdversaryNext(seqAdvStates[j], step.messageReceived, seqAdvStates[j+1], step.messagesToSend);
            assert seqAdvStates[j].byz == seqAdvStates[j+1].byz;
        }
    } 

    lemma lemmajkfladjklfaHelper2(
        s: NodeState,
        mIn: set<QbftMessage>,
        s': NodeState,
        mOut: set<QbftMessageWithRecipient>,
        mIn': set<QbftMessage>,
        mOut': set<QbftMessageWithRecipient>
    )
    requires validNodeState(s)
    requires NodeNext(s, mIn, s', mOut)
    requires mIn == mIn' 
    requires mOut == mOut' 
    ensures NodeNext(s, mIn', s', mOut')
    {

    }

    lemma lemmajkfladjklfaHelper3(
        s: DSState,
        s': DSState,
        allNodes: set<Address>,
        node: Address
    )   
    requires s.nodes.Keys == s'.nodes.Keys == allNodes;   
    requires node in allNodes
    requires forall node' | node' in allNodes && node != node' :: s.nodes[node'] == s'.nodes[node'];
    ensures s'.nodes == s.nodes[node := s'.nodes[node]];
    {

    }   

    lemma lemmajkfladjklfaHelper4(
        s: DSState,
        s': DSState,
        allNodes: set<Address>
    )   
    requires s.nodes.Keys == s'.nodes.Keys == allNodes;   
    requires forall node' | node' in allNodes :: s.nodes[node'] == s'.nodes[node'];
    ensures s'.nodes == s.nodes;
    {

    }      


    lemma lemmajkfladjklfaHelper5(
        s: Adversary,
        mIn: set<QbftMessage>,
        s': Adversary,
        mOut: set<QbftMessageWithRecipient>,
        mIn': set<QbftMessage>,
        mOut': set<QbftMessageWithRecipient>
    )
    requires AdversaryNext(s, mIn, s', mOut)
    requires mIn == mIn' 
    requires mOut == mOut' 
    ensures AdversaryNext(s, mIn', s', mOut')
    {

    }     

    // lemma lemmajkfladjklfaHelper6(
    //    dsBehaviour: DSBehaviour,
    //    configuration: Configuration,
    //    dsStates: iseq<DSState>,
    //    i: nat
    // )     
    // requires IsValidConfiguration(configuration)
    // requires dsBehaviour in DSSpecificationBuilder(configuration).behaviours
    // requires  |validators([configuration.genesisBlock])| > 0
    // // ensures forall i: nat :: validDSState(dsStates[i]);    
    // {
    //         var s := dsStates[i];
    //         var s' := dsStates[i+1];
    //         var environmentStep := dsBehaviour.environmentBehaviour.steps[i];
    //         var messagesReceivedWithoutRecipient := (set mr:QbftMessageWithRecipient | mr in environmentStep.messagesReceivedByTheNodes :: mr.message);            


    //         assert s'.configuration == s.configuration;
    //         assert s.environment == seqEnvStates[i];
    //         assert s'.environment == seqEnvStates[i+1];
    //         assert lemmajkfladjklfaGetEnvStatesHelper(seqEnvStates, dsBehaviour.environmentBehaviour, i);
    //         assert NetworkNext(s.environment,s'.environment,environmentStep.messagesSentByTheNodes,environmentStep.messagesReceivedByTheNodes);  
    //         var node := seqNodes[i];
    //         assert DSSpecificationBuilderHelper(dsBehaviour, allNodes, honestNodes, seqNodes, i);
    //         assert s.nodes.Keys == allNodes;
    //         assert node in s.nodes;   
    //         assert s.nodes.Keys == s'.nodes.Keys; 
    //         assert s.configuration == configuration;  
            
    //         // lemmajkfladjklfaGetDsStatesHelper(dsBehaviour, dsStates, configuration, seqAdvStates, i);

    //         if isHonest(s, node)
    //         {
    //             assert node in allNodes;
    //             assert node !in s.adversary.byz;
    //             assert node !in byzNodes;
    //             assert node in honestNodes;

    //             var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[node];

    //             assert pGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, seqNodes, seqNodeStates[node], node, i);

    //             var stepsTakenByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, node, i);
    //             var step := QbftNodeBehaviour.steps[stepsTakenByNodeSoFar];                

    //             assert
    //             && validNodeState(seqNodeStates[node][i])
    //             && NodeNext(seqNodeStates[node][i], step.messageReceived, seqNodeStates[node][i+1], step.messagesToSend)  
    //             ;    

    //             forall node' | node' in allNodes && node' != node 
    //             ensures seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
    //             {
    //                 // assert 
    //                 // lemmaGetSeqHonestNodeStates(dsBehaviour, configuration, node', seqNodes, seqNodeStates[node']);
    //                 // assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
    //                 assert seqNodes[i] != node';
    //                 if node' in honestNodes 
    //                 {
    //                     assert node' in allNodes;
    //                     assert pGetSeqHonestNodeStatesHelper(dsBehaviour.nodesBehaviours[node'], seqNodes, seqNodeStates[node'], node', i);
    //                     assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
    //                 }
    //                 else
    //                 {
    //                     assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
    //                 }
    //             }     

    //             // assert  s'.nodes == s.nodes[node := s'.nodes[node]];
    //             assert s.nodes == map n | n in allNodes :: seqNodeStates[n][i];
    //             assert s'.nodes == map n | n in allNodes :: seqNodeStates[n][i+1];
    //             assert forall node' | node' in allNodes && node != node' :: s.nodes[node'] == s'.nodes[node'];
    //             assert s.nodes.Keys == s'.nodes.Keys == allNodes;
    //             lemmajkfladjklfaHelper3(s, s', allNodes, node);
    //             assert s'.nodes == s.nodes[node := s'.nodes[node]];

    //             lemmaGetStepsTakeByAdversarySoFar(seqNodes, byzNodes, i);

    //             // assert get(seqNodes, byzNodes, i) == lemmaGetStepsTakeByAdversarySoFar(seqNodes, byzNodes, i+1);
    //             assert s.adversary == s'.adversary;

    //             assert step.messagesToSend == environmentStep.messagesSentByTheNodes;
    //             assert step.messageReceived == messagesReceivedWithoutRecipient; 

    //             lemmajkfladjklfaHelper2(seqNodeStates[node][i], step.messageReceived, seqNodeStates[node][i+1], step.messagesToSend, messagesReceivedWithoutRecipient, environmentStep.messagesSentByTheNodes);

    //             assert NodeNext(seqNodeStates[node][i], messagesReceivedWithoutRecipient, seqNodeStates[node][i+1], environmentStep.messagesSentByTheNodes);
                


    //         }  
    //         else
    //         {
    //             assert node in byzNodes;
    //             var stepsTakenByNodeSoFar := getStepsTakeByAversarySoFar(seqNodes, byzNodes, i);
    //             lemmaGetStepsTakeByAdversarySoFar(seqNodes, byzNodes, i);
    //             var stepsTakenByNodeSoFarPlusOne := getStepsTakeByAversarySoFar(seqNodes, byzNodes, i + 1);
    //             assert stepsTakenByNodeSoFar + 1 == stepsTakenByNodeSoFarPlusOne;
    //             var adversaryBehaviour := dsBehaviour.adversaryBehaviour;
    //             // var seqAdvStates := adversaryBehaviour.steps;
    //             var step := adversaryBehaviour.steps[stepsTakenByNodeSoFar];



    //             assert AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend);

    //             assert AdversaryNext(s.adversary, step.messageReceived, s'.adversary, step.messagesToSend);

    //             lemmajkfladjklfaHelper5(s.adversary, step.messageReceived, s'.adversary, step.messagesToSend, messagesReceivedWithoutRecipient, environmentStep.messagesSentByTheNodes);

    //             assert AdversaryNext(s.adversary, messagesReceivedWithoutRecipient, s'.adversary, environmentStep.messagesSentByTheNodes);

    //             forall node' | node' in allNodes 
    //             ensures seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
    //             {
    //                 // assert 
    //                 // lemmaGetSeqHonestNodeStates(dsBehaviour, configuration, node', seqNodes, seqNodeStates[node']);
    //                 // assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];

    //                 if node' in honestNodes
    //                 {
    //                     assert seqNodes[i] != node';

    //                     assert node' in allNodes;
    //                     assert pGetSeqHonestNodeStatesHelper(dsBehaviour.nodesBehaviours[node'], seqNodes, seqNodeStates[node'], node', i);
    //                     assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
    //                 }
    //                 else
    //                 {
    //                     assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
    //                 }

    //             }                 

    //             lemmajkfladjklfaHelper4(s, s', allNodes);

    //             assert s.nodes == s'.nodes;

    //             // assert step.messagesToSend == environmentStep.messagesSentByTheNodes;

    //             // assert AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
    //         } 

    //         assert forall n | n in honestNodes :: validNodeState(seqNodeStates[n][i]);
    //         // lemmaGetSeqHonestNodeStates2(dsBehaviour, configuration, )

    //         // forall node': Address | node' in honestNodes
    //         // {
    //         //     // var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[node'];
    //         //     // assert pGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, seqNodes, seqNodeStates[node'], node', i);

    //         //     // assert validNodeState(seqNodeStates[node'][i]);
    //         //     lemmaGetSeqHonestNodeStates2(dsBehaviour, configuration, node', seqNodes, seqNodeStates[node'], i);
    //         // }

    //         // assert
    //         // && NetworkNext(s.environment,s'.environment,environmentStep.messagesSentByTheNodes,environmentStep.messagesReceivedByTheNodes)
    //         // && (forall mr:QbftMessageWithRecipient | mr in environmentStep.messagesReceivedByTheNodes :: mr.recipient == node)
    //         // && var messageReceived := set mr:QbftMessageWithRecipient | mr in environmentStep.messagesReceivedByTheNodes :: mr.message;
    //         // && node in s.nodes
    //         // && s'.nodes.Keys == s.nodes.Keys
    //         // && (
    //         //     if isHonest(s,node) then
    //         //         && s'.nodes == s.nodes[node := s'.nodes[node]]
    //         //         && s'.adversary == s.adversary
    //         //         && NodeNext(s.nodes[node],messageReceived,s'.nodes[node],environmentStep.messagesSentByTheNodes)
    //         //     else
    //         //         && s'.nodes == s.nodes
    //         //         && AdversaryNext(s.adversary,messageReceived,s'.adversary,environmentStep.messagesSentByTheNodes)
    //         // )
    //         // && s'.configuration == s.configuration  
    //         // ;          

    //         assert DSNextNode(s, s', environmentStep.messagesSentByTheNodes, environmentStep.messagesReceivedByTheNodes, node);        
    // }

    predicate pLemmajkfladjklfa(
        dsStates: iseq<DSState>,
        seqNodes: iseq<Address>,
        environmentBehaviour: EnvironmentSpecificationBehaviour,
        i: nat
    )
    {
        var environmentStep := environmentBehaviour.steps[i];
        && validDSState(dsStates[i])
        && DSNextNode(dsStates[i], dsStates[i+1], environmentStep.messagesSentByTheNodes, environmentStep.messagesReceivedByTheNodes, seqNodes[i])     
    }

    lemma lemmajkfladjklfa (
       dsBehaviour: DSBehaviour,
       configuration: Configuration,
       seqNodes: iseq<Address>
    ) returns (dsStates: iseq<DSState>)
    requires IsValidConfiguration(configuration)
    requires dsBehaviour in DSSpecificationBuilder(configuration).behaviours
    requires  |validators([configuration.genesisBlock])| > 0
    requires    var allNodes := seqToSet(configuration.nodes);
                pLemmajkfladjklfaGetSeqNodes(dsBehaviour, allNodes, seqNodes)

    // ensures forall i: nat :: validDSState(dsStates[i]);
    // ensures forall i: nat :: seqNodes[i] in dsStates[i].nodes
    ensures DSInit(dsStates[0], configuration)
    ensures 
            forall i: nat :: pLemmajkfladjklfa(dsStates, seqNodes, dsBehaviour.environmentBehaviour, i)
    //                 var environmentStep := dsBehaviour.environmentBehaviour.steps[i];
    //                 && validDSState(dsStates[i])
    //                 && DSNextNode(dsStates[i], dsStates[i+1], environmentStep.messagesSentByTheNodes, environmentStep.messagesReceivedByTheNodes, seqNodes[i]);    

    ensures forall i: nat :: dsBehaviour.nodesBehaviours.Keys <= dsStates[i].nodes.Keys
    ensures forall n, i:nat | n in dsBehaviour.nodesBehaviours.Keys :: pLemmaGetSeqHonestNodeStates3ForAll2(dsBehaviour, n, seqNodes, dsStates[i].nodes[n], i);    
    ensures forall n: Address, i: nat :: (isHonest(dsStates[i], n) <==> n in dsBehaviour.nodesBehaviours.Keys);
    ensures forall n | n in dsBehaviour.nodesBehaviours.Keys ::
            if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n) then
                forall i: nat | i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1 :: pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i) 
            else
                forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i)  
    ensures forall n | n in dsBehaviour.nodesBehaviours.Keys  ::
        (dsStates[0].nodes[n].blockchain == dsBehaviour.nodesBehaviours[n].initialBlockchain)                 
    {
        var allNodes := seqToSet(configuration.nodes);
        var honestNodes := dsBehaviour.nodesBehaviours.Keys;
        var byzNodes := allNodes - honestNodes;
       
        // seqNodes := lemmajkfladjklfaGetSeqNodes(dsBehaviour, configuration, allNodes);
             

        var seqAdvStates := lemmajkfladjklfaGetAdvStates(dsBehaviour, configuration, allNodes, seqNodes);

        var seqEnvStates := lemmajkfladjklfaGetEnvStates(dsBehaviour, configuration);           

        var seqNodeStates := lemmajkfladjklfaGetSeqNodeStates(dsBehaviour, configuration, allNodes, honestNodes, seqNodes);

        dsStates := lemmajkfladjklfaGetDsStates(
            configuration,
            seqEnvStates,
            seqNodeStates,
            seqAdvStates,
            allNodes
        );

        assert forall i: nat :: dsStates[i].adversary == seqAdvStates[i];

        forall i:nat, n: Address //| n in honestNodes
        ensures isHonest(dsStates[i], n) <==> n in honestNodes
        {
            if n in honestNodes
            {
                assert n in dsStates[i].nodes;
                assert n !in seqAdvStates[0].byz;
                assert n !in seqAdvStates[i].byz;
                assert isHonest(dsStates[i], n);
            }

            if isHonest(dsStates[i], n)
            {
                assert n in honestNodes;
            }
        }    

        // assert forall i: nat, n: Address :: (isHonest(dsStates[i], n) <==> n in honestNodes);

        assert DSInit(dsStates[0], configuration);

        forall i: nat 
        ensures pLemmajkfladjklfa(dsStates, seqNodes, dsBehaviour.environmentBehaviour, i)
        // ensures validDSState(dsStates[i]);
        // ensures 
        //             var environmentStep := dsBehaviour.environmentBehaviour.steps[i];
        //             DSNextNode(dsStates[i], dsStates[i+1], environmentStep.messagesSentByTheNodes, environmentStep.messagesReceivedByTheNodes, seqNodes[i]);
        {
            var s := dsStates[i];
            var s' := dsStates[i+1];
            var environmentStep := dsBehaviour.environmentBehaviour.steps[i];
            var messagesReceivedWithoutRecipient := (set mr:QbftMessageWithRecipient | mr in environmentStep.messagesReceivedByTheNodes :: mr.message);            


            assert s'.configuration == s.configuration;
            assert s.environment == seqEnvStates[i];
            assert s'.environment == seqEnvStates[i+1];
            assert lemmajkfladjklfaGetEnvStatesHelper(seqEnvStates, dsBehaviour.environmentBehaviour, i);
            assert NetworkNext(s.environment,s'.environment,environmentStep.messagesSentByTheNodes,environmentStep.messagesReceivedByTheNodes);  
            var node := seqNodes[i];
            assert DSSpecificationBuilderHelper(dsBehaviour, allNodes, seqNodes, i);
            assert s.nodes.Keys == allNodes;
            assert node in s.nodes;   
            assert s.nodes.Keys == s'.nodes.Keys; 
            assert s.configuration == configuration;  
            
            // lemmajkfladjklfaGetDsStatesHelper(dsBehaviour, dsStates, configuration, seqAdvStates, i);

            if isHonest(s, node)
            {
                assert node in allNodes;
                assert node !in s.adversary.byz;
                assert node !in byzNodes;
                assert node in honestNodes;

                var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[node];

                assert pGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, seqNodes, seqNodeStates[node], node, i);

                var stepsTakenByNodeSoFar := getStepsTakeByNodeSoFar(seqNodes, node, i);
                var step := QbftNodeBehaviour.steps[stepsTakenByNodeSoFar];                

                assert
                && validNodeState(seqNodeStates[node][i])
                && NodeNext(seqNodeStates[node][i], step.messagesReceived, seqNodeStates[node][i+1], step.messagesToSend)  
                ;    

                forall node' | node' in allNodes && node' != node 
                ensures seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
                {
                    // assert 
                    // lemmaGetSeqHonestNodeStates(dsBehaviour, configuration, node', seqNodes, seqNodeStates[node']);
                    // assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
                    assert seqNodes[i] != node';
                    if node' in honestNodes 
                    {
                        assert node' in allNodes;
                        assert pGetSeqHonestNodeStatesHelper(dsBehaviour.nodesBehaviours[node'], seqNodes, seqNodeStates[node'], node', i);
                        assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
                    }
                    else
                    {
                        assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
                    }
                }     

                // assert  s'.nodes == s.nodes[node := s'.nodes[node]];
                assert s.nodes == map n | n in allNodes :: seqNodeStates[n][i];
                assert s'.nodes == map n | n in allNodes :: seqNodeStates[n][i+1];
                assert forall node' | node' in allNodes && node != node' :: s.nodes[node'] == s'.nodes[node'];
                assert s.nodes.Keys == s'.nodes.Keys == allNodes;
                lemmajkfladjklfaHelper3(s, s', allNodes, node);
                assert s'.nodes == s.nodes[node := s'.nodes[node]];

                lemmaGetStepsTakeByAdversarySoFar(seqNodes, byzNodes, i);

                // assert get(seqNodes, byzNodes, i) == lemmaGetStepsTakeByAdversarySoFar(seqNodes, byzNodes, i+1);
                assert s.adversary == s'.adversary;

                assert step.messagesToSend == environmentStep.messagesSentByTheNodes;
                assert step.messagesReceived == messagesReceivedWithoutRecipient; 

                lemmajkfladjklfaHelper2(seqNodeStates[node][i], step.messagesReceived, seqNodeStates[node][i+1], step.messagesToSend, messagesReceivedWithoutRecipient, environmentStep.messagesSentByTheNodes);

                assert NodeNext(seqNodeStates[node][i], messagesReceivedWithoutRecipient, seqNodeStates[node][i+1], environmentStep.messagesSentByTheNodes);

            }  
            else
            {
                assert node in byzNodes;
                var stepsTakenByNodeSoFar := getStepsTakeByAversarySoFar(seqNodes, byzNodes, i);
                lemmaGetStepsTakeByAdversarySoFar(seqNodes, byzNodes, i);
                var stepsTakenByNodeSoFarPlusOne := getStepsTakeByAversarySoFar(seqNodes, byzNodes, i + 1);
                assert stepsTakenByNodeSoFar + 1 == stepsTakenByNodeSoFarPlusOne;
                var adversaryBehaviour := dsBehaviour.adversaryBehaviour;
                // var seqAdvStates := adversaryBehaviour.steps;
                var step := adversaryBehaviour.steps[stepsTakenByNodeSoFar];



                assert AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend);

                assert AdversaryNext(s.adversary, step.messageReceived, s'.adversary, step.messagesToSend);

                lemmajkfladjklfaHelper5(s.adversary, step.messageReceived, s'.adversary, step.messagesToSend, messagesReceivedWithoutRecipient, environmentStep.messagesSentByTheNodes);

                assert AdversaryNext(s.adversary, messagesReceivedWithoutRecipient, s'.adversary, environmentStep.messagesSentByTheNodes);

                forall node' | node' in allNodes 
                ensures seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
                {
                    // assert 
                    // lemmaGetSeqHonestNodeStates(dsBehaviour, configuration, node', seqNodes, seqNodeStates[node']);
                    // assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];

                    if node' in honestNodes
                    {
                        assert seqNodes[i] != node';

                        assert node' in allNodes;
                        assert pGetSeqHonestNodeStatesHelper(dsBehaviour.nodesBehaviours[node'], seqNodes, seqNodeStates[node'], node', i);
                        assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
                    }
                    else
                    {
                        assert seqNodeStates[node'][i] == seqNodeStates[node'][i+1];
                    }

                }                 

                lemmajkfladjklfaHelper4(s, s', allNodes);

                assert s.nodes == s'.nodes;

                // assert step.messagesToSend == environmentStep.messagesSentByTheNodes;

                // assert AdversaryNext(seqAdvStates[i], step.messageReceived, seqAdvStates[i+1], step.messagesToSend)
            } 

            assert forall n | n in honestNodes :: validNodeState(seqNodeStates[n][i]);
            // lemmaGetSeqHonestNodeStates2(dsBehaviour, configuration, )

            // forall node': Address | node' in honestNodes
            // {
            //     // var QbftNodeBehaviour := dsBehaviour.nodesBehaviours[node'];
            //     // assert pGetSeqHonestNodeStatesHelper(QbftNodeBehaviour, seqNodes, seqNodeStates[node'], node', i);

            //     // assert validNodeState(seqNodeStates[node'][i]);
            //     lemmaGetSeqHonestNodeStates2(dsBehaviour, configuration, node', seqNodes, seqNodeStates[node'], i);
            // }

            // assert
            // && NetworkNext(s.environment,s'.environment,environmentStep.messagesSentByTheNodes,environmentStep.messagesReceivedByTheNodes)
            // && (forall mr:QbftMessageWithRecipient | mr in environmentStep.messagesReceivedByTheNodes :: mr.recipient == node)
            // && var messageReceived := set mr:QbftMessageWithRecipient | mr in environmentStep.messagesReceivedByTheNodes :: mr.message;
            // && node in s.nodes
            // && s'.nodes.Keys == s.nodes.Keys
            // && (
            //     if isHonest(s,node) then
            //         && s'.nodes == s.nodes[node := s'.nodes[node]]
            //         && s'.adversary == s.adversary
            //         && NodeNext(s.nodes[node],messageReceived,s'.nodes[node],environmentStep.messagesSentByTheNodes)
            //     else
            //         && s'.nodes == s.nodes
            //         && AdversaryNext(s.adversary,messageReceived,s'.adversary,environmentStep.messagesSentByTheNodes)
            // )
            // && s'.configuration == s.configuration  
            // ;          

            assert DSNextNode(s, s', environmentStep.messagesSentByTheNodes, environmentStep.messagesReceivedByTheNodes, node);
        }

        forall n, i:nat | n in honestNodes 
        ensures pLemmaGetSeqHonestNodeStates3ForAll2(dsBehaviour, n, seqNodes, dsStates[i].nodes[n], i);
        {
            assert pLemmaGetSeqHonestNodeStates3ForAll(dsBehaviour, n, seqNodes, seqNodeStates[n], i);
            assert pLemmaGetSeqHonestNodeStates3ForAll2(dsBehaviour, n, seqNodes, seqNodeStates[n][i], i);
            assert pLemmaGetSeqHonestNodeStates3ForAll2(dsBehaviour, n, seqNodes, dsStates[i].nodes[n], i);
            // assert 
            // lemmaGetSeqHonestNodeStates3ForAll(dsBehaviour, configuration, n, seqNodes, seqNodeStates[n]);
        }        

        forall n | n in honestNodes 
        ensures 
            if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n) then
                forall i: nat | i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1 :: pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i) 
            else
                forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i)  
        {
            if !pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n)
            {
                forall i: nat
                ensures pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i);
                {
                    assert seqNodeStates[n][i] == dsStates[i].nodes[n];

                    // assert forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates[n], i);
                    assert pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates[n], i);
                    assert pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i);
                }

            }
            else
            {
                forall i: nat | i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1
                ensures pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i);
                {
                    assert seqNodeStates[n][i] == dsStates[i].nodes[n];

                    // assert forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates[n], i);
                    assert pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates[n], i);
                    assert pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i);
                }
            }
        }        
        // // assert dsStates

        
    }



    lemma lemmajkfladjklfa2 (
       dsBehaviour: DSBehaviour,
       configuration: Configuration
    ) returns (seqNodes: iseq<Address>, dsStates: iseq<DSState>)
    requires IsValidConfiguration(configuration)
    requires dsBehaviour in DSSpecificationBuilder(configuration).behaviours
    requires  |validators([configuration.genesisBlock])| > 0
    ensures forall i: nat :: dsBehaviour.nodesBehaviours.Keys <= dsStates[i].nodes.Keys
    // ensures forall n, i:nat | n in dsBehaviour.nodesBehaviours.Keys :: pLemmaGetSeqHonestNodeStates3ForAll2(dsBehaviour, n, seqNodes, dsStates[i].nodes[n], i);
    // ensures forall i: nat :: validDSState(dsStates[i]);
    // ensures forall i: nat :: seqNodes[i] in dsStates[i].nodes
    // ensures 
            // forall i: nat :: pLemmajkfladjklfa(dsStates, seqNodes, dsBehaviour.environmentBehaviour, i)
    //                 var environmentStep := dsBehaviour.environmentBehaviour.steps[i];
    //                 && validDSState(dsStates[i])
    //                 && DSNextNode(dsStates[i], dsStates[i+1], environmentStep.messagesSentByTheNodes, environmentStep.messagesReceivedByTheNodes, seqNodes[i]);  
    // ensures forall n | n in dsBehaviour.nodesBehaviours.Keys ::
    //         if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n) then
    //             forall i: nat | i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1 :: pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i) 
    //         else
    //             forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i)        
    {
        var allNodes := seqToSet(configuration.nodes);
        var honestNodes := dsBehaviour.nodesBehaviours.Keys;
        var byzNodes := allNodes - honestNodes;
       
        seqNodes := lemmajkfladjklfaGetSeqNodes(dsBehaviour, configuration, allNodes);
             

        var seqAdvStates := lemmajkfladjklfaGetAdvStates(dsBehaviour, configuration, allNodes, seqNodes);

        var seqEnvStates := lemmajkfladjklfaGetEnvStates(dsBehaviour, configuration);           

        var seqNodeStates := lemmajkfladjklfaGetSeqNodeStates(dsBehaviour, configuration, allNodes, honestNodes, seqNodes);

        dsStates := lemmajkfladjklfaGetDsStates(
            configuration,
            seqEnvStates,
            seqNodeStates,
            seqAdvStates,
            allNodes
        );

        forall n, i:nat //| n in honestNodes
        ensures isHonest(dsStates[i], n) <==> n in honestNodes
        {
            if n in honestNodes
            {
                assert n in dsStates[i].nodes;
                assert n !in seqAdvStates[0].byz;
                assert n !in seqAdvStates[i].byz;
                assert isHonest(dsStates[i], n);
            }

            if isHonest(dsStates[i], n)
            {
                assert n in honestNodes;
            }
        }
        
        // assert forall i: nat, n: Address :: (isHonest(dsStates[i], n) ==> n in honestNodes);
        // assert forall i: nat, n: Address :: (isHonest(dsStates[i], n) <== n in honestNodes);

        // forall n | n in honestNodes 
        // ensures 
        //     if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n) then
        //         forall i: nat | i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1 :: pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i) 
        //     else
        //         forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i)  
        // {
        //     if !pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n)
        //     {
        //         forall i: nat
        //         ensures pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i);
        //         {
        //             assert seqNodeStates[n][i] == dsStates[i].nodes[n];

        //             // assert forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates[n], i);
        //             assert pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates[n], i);
        //             assert pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i);
        //         }

        //     }
        //     else
        //     {
        //         forall i: nat | i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1
        //         ensures pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i);
        //         {
        //             assert seqNodeStates[n][i] == dsStates[i].nodes[n];

        //             // assert forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates[n], i);
        //             assert pLemmaGetSeqHonestNodeStates4ForAll(dsBehaviour, n, seqNodes, seqNodeStates[n], i);
        //             assert pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i);
        //         }
        //     }
        // }
    }    

}

