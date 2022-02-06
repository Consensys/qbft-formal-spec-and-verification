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
include "networking_step_lemmas.dfy"
include "instr_dsstate_networking_common_invariants.dfy"

module EEANetworkingInvariantsLemmas
{
    import opened EEASpecTypes
    import opened EEASpecNetwork
    import opened EEAAuxiliaryFunctionsAndLemmas
    import opened EEACommonFunctions
    import opened EEASpec
    import opened HelperLemmasSets
    import opened EEADistributedSystem
    import opened EEAInstrumentedSpecs
    import opened EEAAxioms
    import opened EEAAuxFunctionsProof
    import opened EEAAuxBasicInvariantsProof
    import opened EEAInstrNodeStateInvariants
    import opened EEAInstrDSStateNetworkingCommonInvariants
    import opened EEAGeneralLemmas
    import opened EEANetworkingInvariants
    import opened EEANetworkingStepLemmas

    lemma lemmaMessagesReceivedByAnHonestNodeHaveBeenSent(
        s:InstrDSState, 
        s': InstrDSState,
        n: Address
    )    
    requires validInstrDSState(s)
    requires isInstrNodeHonest(s,n)
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invMessagesReceivedHaveBeenSent(s, n)
    requires InstrDSNextSingle(s, s')
    requires isNodeThatTakesStep(s, s', n);
    ensures invMessagesReceivedHaveBeenSent(s', n)
    {

        if s == s' 
        {
            // assert invMessagesReceivedHaveBeenSent(s',n);
            assert invMessagesReceivedHaveBeenSent(s',n);
        }
        else
        {
            var messagesSentByTheNodes,
                messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n);

                assert invMessagesReceivedHaveBeenSent(s',n);                
        }
    }    


    lemma lemmaMessagesReceivedByHonestNodesHaveBeenSent(
        s:  InstrDSState, 
        s': InstrDSState
    )    
    requires validInstrDSState(s)
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invMessagesReceivedByHonestNodesHaveBeenSent(s)    
    requires InstrDSNextSingle(s, s')             
    ensures invMessagesReceivedByHonestNodesHaveBeenSent(s')
    {  
        if s != s'
        {
            var node :| isNodeThatTakesStep(s, s', node);

            if isInstrNodeHonest(s,node)
            {
                
                lemmaMessagesReceivedByAnHonestNodeHaveBeenSent(s,s',node);

                assert forall n | isInstrNodeHonest(s,n) && n != node :: invMessagesReceivedHaveBeenSent(s',n);

                assert invMessagesReceivedByHonestNodesHaveBeenSent(s');


            }
            else
            {
                assert invMessagesReceivedByHonestNodesHaveBeenSent(s');
            }         
        }
        else {
            assert invMessagesReceivedByHonestNodesHaveBeenSent(s');
        }
    }    

    lemma lemmaInvMessagesReceivedByHonestNodesAreInAllMesssagesSentIncSentToItselfWithoutRecipient
    (
        s: InstrDSState
    )
    requires invMessagesReceivedByHonestNodesHaveBeenSent(s)
    ensures invMessagesReceivedByHonestNodesAreInAllMesssagesSentIncSentToItselfWithoutRecipient(s)
    {
        lemmaAllMesssagesSentIncSentToItselfWithoutRecipient(s);
    }  

    // 500s
    lemma lemmaInvSetOfMessagesSentAndSignedByAnHonestNodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(
        s:InstrDSState, 
        s': InstrDSState,
        n: Address
    )    
    requires validInstrDSState(s)   
    requires isInstrNodeHonest(s,n)
    requires invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s,n)
    requires nodeTakesStep(s,s', n)
    ensures isInstrNodeHonest(s',n)
    ensures invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s',n);
    {
        lemmaGetSetOfSignedPayloads();
        var messagesSentByTheNodes,
            messagesReceivedByTheNodes :|
                InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n);  

        assert getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)) ==
                    getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)) + 
                    getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))); 

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) +
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n); 
    }  

    // 203s 3.2.0
    lemma lemmaiInvSetOfMessagesSentAndSignedByAnHonestNodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(
        s:InstrDSState, 
        s': InstrDSState,
        n: Address
    )    
    requires validInstrDSState(s)   
    requires isInstrNodeHonest(s,n)
    requires invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s,n)
    requires InstrDSNextSingle(s, s')
    requires nodeTakesStep(s,s', n)
    ensures isInstrNodeHonest(s',n)
    ensures invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s',n);
    {
        lemmaGetSetOfSignedPayloads();
        lemmaAllMesssagesSentIncSentToItselfWithoutRecipient(s);
        lemmaAllMesssagesSentIncSentToItselfWithoutRecipient(s');
        var messagesSentByTheNodes,
            messagesReceivedByTheNodes :|
                InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n);  

        var _,_, messagesSentToItself := lemmaFromDSInstrNextNodeNodeNextSubStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n);

        assert allMesssagesSentIncSentToItselfWithoutRecipient(s') ==
                    allMesssagesSentIncSentToItselfWithoutRecipient(s) +
                    fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) +
                    messagesSentToItself; 

        lemmaGetSetOfSignedPayloadsONSetsFour(
                allMesssagesSentIncSentToItselfWithoutRecipient(s'),
                allMesssagesSentIncSentToItselfWithoutRecipient(s),
                fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)),
                messagesSentToItself
        );

        assert getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')) ==
                    getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)) +
                    getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))) +
                    getSetOfSignedPayloads(messagesSentToItself);         

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n) +
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) +
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(messagesSentToItself), n); 

        assert getAllMessagesSentByTheNode(s', n) ==
                    getAllMessagesSentByTheNode(s, n) + 
                    fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) +
                    messagesSentToItself;   

        lemmaGetSetOfSignedPayloadsONSetsFour(
            getAllMessagesSentByTheNode(s', n),
            getAllMessagesSentByTheNode(s, n),
            fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)),
            messagesSentToItself
        );              

        assert getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', n)) ==
                    getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, n)) + 
                    getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))) +
                    getSetOfSignedPayloads(messagesSentToItself); 

    } 

    // 94s
    lemma lemmaInvAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(
        s : InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )  
    requires validInstrDSState(s) 
    requires isInstrNodeHonest(s,node)
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, node);
    requires InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
    ensures invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node);
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();   
        lemmaGetSetOfSignedPayloads();

        var current := s.nodes[node];
        var next := s'.nodes[node];

        var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

        var newMessagesReceived := current.nodeState.messagesReceived + messageReceived;

        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );

        var nextForSubsteps := next.nodeState;

        assert currentForSubsteps.id == nextForSubsteps.id;
        assert next.messagesSent == current.messagesSent + multiset(messagesSentByTheNodes);        
        // assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), n)

        assert forall n | isInstrNodeHonest(s,n) && n != node ::
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n) <=
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);
          

        if(     
                // || (currentForSubsteps == nextForSubsteps && outQbftMessages == {})
                || UponBlockTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponProposal(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponPrepare(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponCommit(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponNewBlock(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
        )
        {
            assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n)  ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(nextForSubsteps.messagesReceived), n) ;
            
            assert invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node);
            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) ==
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n);

            // assume invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);

            // assert forall n | isInstrNodeHonest(s,n) && n != node ::
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);             
        }         
        else if(     
                || UponRoundChange(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponRoundTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                )
        {
            assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n)  ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(nextForSubsteps.messagesReceived), n) ;

            assert invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node);
            // assert forall n | isInstrNodeHonest(s,n) && n != current.nodeState.id ::
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) <=
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(current.nodeState.messagesReceived), n) ;

            // assume forall n | isInstrNodeHonest(s,n) && n != current.nodeState.id ::
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(current.nodeState.messagesReceived), n) <=
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);

            // assume invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, current.nodeState.id);
                

            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
            //         // filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) +
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n);

            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n) ==
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) +
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n);
                    
            // // assume invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);

            // assert forall n | isInstrNodeHonest(s,n) && n != node ::
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);                

        } 
        else if(currentForSubsteps == nextForSubsteps)
        {
            assert messagesSentByTheNodes == {};

            assert currentForSubsteps.messagesReceived == nextForSubsteps.messagesReceived;

            assert invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node);

            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) ==
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n);            
            // assert invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);
            // assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s');

            // assert forall n | isInstrNodeHonest(s,n) && n != node ::
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);             
        }     
        else
        {
            assert false;
        }         
    }      
    
    // 44s
    lemma lemmaInvAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(
        s : InstrDSState,
        s': InstrDSState
    )  
    requires validInstrDSState(s) 
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s);
    requires InstrDSNextSingle(s, s')
    ensures invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s');
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();


        if s != s'
        {
            var node :| isNodeThatTakesStep(s, s', node);

            if isInstrNodeHonest(s,node)
            {
                var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                lemmaInvAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                assert invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node);

                assert forall n |  isInstrNodeHonest(s,n) && n != node ::
                    s.nodes[n].nodeState.messagesReceived == s'.nodes[n].nodeState.messagesReceived;

                assert allMessagesSentWithoutRecipient(s.environment) <= allMessagesSentWithoutRecipient(s'.environment);

                forall node' |  isInstrNodeHonest(s,node') && node' != node
                ensures invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node')
                {
                    assert forall n | isInstrNodeHonest(s,n) && n != node' ::
                        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node'].nodeState.messagesReceived), n) <=
                        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) ;

                    assert s.nodes[node'].nodeState.messagesReceived == s'.nodes[node'].nodeState.messagesReceived;
                    assert invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node');
                }

                assert invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s');
            }
            else{
                forall node |  isInstrNodeHonest(s,node)
                ensures invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node)
                {
                    assert forall n | isInstrNodeHonest(s,n) && n != node ::
                        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), n) <=
                        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) ;

                    assert s.nodes[node].nodeState.messagesReceived == s'.nodes[node].nodeState.messagesReceived;
                    assert invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node);
                }
                assert invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s');
            }
        }
    }  

    lemma lemmaInvAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(
        s : InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )  
    requires validInstrDSState(s) 
    requires isInstrNodeHonest(s,node)
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, node);
    requires invAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, node);
    requires InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
    ensures invAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node);
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();   
        lemmaGetSetOfSignedPayloads();

        var current := s.nodes[node];
        var next := s'.nodes[node];

        var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

        var newMessagesReceived := current.nodeState.messagesReceived + messageReceived;

        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );

        var nextForSubsteps := next.nodeState;

        assert currentForSubsteps.id == nextForSubsteps.id;
        assert next.messagesSent == current.messagesSent + multiset(messagesSentByTheNodes);        

        var newMessagesSentToItself :=  (next.nodeState.messagesReceived - newMessagesReceived - current.nodeState.messagesReceived);
        assert next.messagesSentToItself == current.messagesSentToItself + newMessagesSentToItself;
        // assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), n)

        // assume forall n | isInstrNodeHonest(s,n) && n != node ::
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(newMessagesSentToItself), n) <=
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n);

        // assume forall n | isInstrNodeHonest(s,n) && n != node ::
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n) <=
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);

        // assume forall n | isInstrNodeHonest(s,n) && n != node ::
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(newMessagesSentToItself), n)  <=
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);  

        forall n | isInstrNodeHonest(s,n) && n != node
        ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(next.messagesSentToItself), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n); 
        {
            calc {
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(newMessagesSentToItself), n); 
                <=
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n);
                <= 
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);  
            } 

            // assume filterSignedPayloadsByAuthor(getSetOfSignedPayloads(newMessagesSentToItself), n)
            //     <=
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n)
            //     <= 
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);  

            assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(newMessagesSentToItself), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n);  

            assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(current.messagesSentToItself ), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n);  

            assert  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(next.messagesSentToItself), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n); 
        }          
          
        assert invAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node); 

       
    }  

    // 44s
    lemma lemmaInvallSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(
        s : InstrDSState,
        s': InstrDSState
    )  
    requires validInstrDSState(s) 
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s);
    requires invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s);
    requires InstrDSNextSingle(s, s')
    ensures invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s');
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();


        if s != s'
        {
            var node :| isNodeThatTakesStep(s, s', node);

            if isInstrNodeHonest(s,node)
            {
                var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                lemmaInvAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                assert invAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node);

                assert forall n |  isInstrNodeHonest(s,n) && n != node ::
                    s.nodes[n].messagesSentToItself == s'.nodes[n].messagesSentToItself;

                assert allMessagesSentWithoutRecipient(s.environment) <= allMessagesSentWithoutRecipient(s'.environment);

                forall node' |  isInstrNodeHonest(s,node') && node' != node
                ensures invAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node')
                {
                    assert forall n | isInstrNodeHonest(s,n) && n != node' ::
                        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node'].nodeState.messagesReceived), n) <=
                        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) ;

                    assert s.nodes[node'].messagesSentToItself == s'.nodes[node'].messagesSentToItself;
                    assert invAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node');
                }

                assert invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s');
            }
            else{
                forall node' |  isInstrNodeHonest(s,node')
                ensures invAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node')
                {
                    assert forall n | isInstrNodeHonest(s,n) && n != node' ::
                        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node'].nodeState.messagesReceived), n) <=
                        filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) ;

                    assert s.nodes[node'].messagesSentToItself == s'.nodes[node'].messagesSentToItself;
                    assert invAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s', node');
                }

                assert invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s');
            }
        }
    }     

    // 384s
    // TODO: Only Internal
    lemma lMessagesSentByTheNodesOnHonestStepAreSubsetOfMessagesSentByAllHonestNodesThatDoNotTakeTheStep(
        s : InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )  
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
    // requires InstrDSNextSingle(s, s')
    // requires isNodeThatTakesStep(s, s', node)
    requires isInstrNodeHonest(s,node)
    requires invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, node);
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    ensures  forall n | isInstrNodeHonest(s,n) && n != node ::
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n); 
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();   
        lemmaGetSetOfSignedPayloads();
        // lemmaNodesThatTakesAStepDoesNotChangeMessageSentByOtherNodesThatAreHonest(s,s',node);

        var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;


        // var inQbftMessages, outQbftMessages :|
        //             InstrNodeNextSingleStep(s.nodes[node], inQbftMessages, s'.nodes[node], outQbftMessages);  

        assert NodeNextSingleStep(s.nodes[node].nodeState, messageReceived, s'.nodes[node].nodeState, messagesSentByTheNodes);

        var current := s.nodes[node];
        var next := s'.nodes[node];

        var newMessagesReceived := current.nodeState.messagesReceived + messageReceived;

        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );

        var nextForSubsteps := next.nodeState;

        assert currentForSubsteps.id == nextForSubsteps.id;
        assert next.messagesSent == current.messagesSent + multiset(messagesSentByTheNodes);

        lemmaInvSetOfMessagesSentAndSignedByAnHonestNodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s, s', node);

        if(     
                // || (currentForSubsteps == nextForSubsteps && outQbftMessages == {})
                || UponBlockTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponProposal(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponPrepare(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponCommit(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponNewBlock(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
        )
        {
            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) ==
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n);

            // assume invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);

            assert forall n | isInstrNodeHonest(s,n) && n != node ::
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);             
        }         
        else if(     
                || UponRoundChange(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponRoundTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                )
        {

            assert forall n | isInstrNodeHonest(s,n) && n != current.nodeState.id ::
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) <=
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(current.nodeState.messagesReceived), n) ;

            // assume forall n | isInstrNodeHonest(s,n) && n != current.nodeState.id ::
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(current.nodeState.messagesReceived), n) <=
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);

            // assume invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, current.nodeState.id);
                

            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
            //         // filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) +
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n);

            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n) ==
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) +
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n);
                    
            // // assume invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);

            assert forall n | isInstrNodeHonest(s,n) && n != node ::
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);                

        } 
        else if(currentForSubsteps == nextForSubsteps)
        {
            assert messagesSentByTheNodes == {};

            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) ==
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n);            
            // assert invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);
            // assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s');

            assert forall n | isInstrNodeHonest(s,n) && n != node ::
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);             
        }     
        else
        {
            assert false;
        }            
    }

    // 384s
    // TODO: Module internal lemma
    lemma lMessagesSignedByAnHonestNodeThatDoesNotTakeTheStepInTheMessagesSentToItselfByTheHonestNodeThatTakesTheStepAreSubsetOfTheAllMessagesSentByTheNodeThatDoesNotTakeTheStep(
        s : InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )  
    requires validInstrDSState(s) 
    requires isInstrNodeHonest(s,node)
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, node);
    requires invAllSignedPayloadsSentToItselfByAnHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, node);
    requires InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
    // requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    ensures   forall n | isInstrNodeHonest(s',n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n); 
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();   
        lemmaGetSetOfSignedPayloads();

        var current := s.nodes[node];
        var next := s'.nodes[node];

        var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

        var newMessagesReceived := current.nodeState.messagesReceived + messageReceived;

        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );

        var nextForSubsteps := next.nodeState;

        assert currentForSubsteps.id == nextForSubsteps.id;
        assert next.messagesSent == current.messagesSent + multiset(messagesSentByTheNodes);        

        var newMessagesSentToItself :=  (next.nodeState.messagesReceived - newMessagesReceived - current.nodeState.messagesReceived);
        assert next.messagesSentToItself == current.messagesSentToItself + newMessagesSentToItself;
        // assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), n)

        // assume forall n | isInstrNodeHonest(s,n) && n != node ::
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(newMessagesSentToItself), n) <=
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n);

        // assume forall n | isInstrNodeHonest(s,n) && n != node ::
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n) <=
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);

        // assume forall n | isInstrNodeHonest(s,n) && n != node ::
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(newMessagesSentToItself), n)  <=
        //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);


        forall n | isInstrNodeHonest(s,n) && n != node
        ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(next.messagesSentToItself), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n); 
        {
            calc {
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(newMessagesSentToItself), n); 
                <=
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n);
                <= 
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);  
            } 

            // assume filterSignedPayloadsByAuthor(getSetOfSignedPayloads(newMessagesSentToItself), n)
            //     <=
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n)
            //     <= 
            //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);  

            // assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(newMessagesSentToItself), n) <=
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n);  

            assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(current.messagesSentToItself ), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);  

            assert  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(next.messagesSentToItself), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n); 
        }         

        // if(     
        //         // || (currentForSubsteps == nextForSubsteps && outQbftMessages == {})
        //         || UponBlockTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
        //         || UponProposal(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
        //         || UponPrepare(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
        //         || UponCommit(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
        //         || UponNewBlock(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
        // )
        // {

        //     // assert forall n | isInstrNodeHonest(s,n) && n != node ::
        //     //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
        //     //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);             
        // }         
        // else if(     
        //         || UponRoundChange(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
        //         || UponRoundTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
        //         )
        // {

        //     // assert forall n | isInstrNodeHonest(s,n) && n != current.nodeState.id ::
        //     //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) <=
        //     //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(current.nodeState.messagesReceived), n) ;


        //     // assert forall n | isInstrNodeHonest(s,n) && n != node ::
        //     //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
        //     //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);                

        // } 
        // else if(currentForSubsteps == nextForSubsteps)
        // {
        //     // assert messagesSentByTheNodes == {};

        //     // assert forall n | isInstrNodeHonest(s',n) && n != node ::
        //     //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n) <=
        //     //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);  

        //     // assert s.nodes[node].messagesSentToItself == s'.nodes[node].messagesSentToItself;  

        //     // assert forall n | isInstrNodeHonest(s',n) && n != node ::
        //     //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n) <=
        //     //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);                               
        // }     
        // else
        // {
        //     assert false;
        // }            
    }      

    // 25s
    lemma lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(
        s:InstrDSState, 
        s': InstrDSState
    )    
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires InstrDSNextSingle(s, s')
    ensures indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s')
    ensures invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s')
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();

        if s != s'
        {
            
            var node :| isNodeThatTakesStep(s, s', node);

            // lemmaNodesThatTakesAStepDoesNotChangeMessageSentByOtherNodesThatAreHonest2(s,s',node);
            lemmaGetSetOfSignedPayloads();

   
            if isInstrNodeHonest(s,node)
            {
                var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

                assert InstrNodeNextSingleStep(s.nodes[node],messageReceived,s'.nodes[node],messagesSentByTheNodes);

                

                // var inQbftMessages, outQbftMessages :|
                //     InstrNodeNextSingleStep(s.nodes[node], inQbftMessages, s'.nodes[node], outQbftMessages);

                // assume forall n | isInstrNodeHonest(s,n) && n != node ::
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), n) <=
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);
                // assume forall n | isInstrNodeHonest(s,n) && n != node ::
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n); 

                lMessagesSentByTheNodesOnHonestStepAreSubsetOfMessagesSentByAllHonestNodesThatDoNotTakeTheStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                // assume forall n | isInstrNodeHonest(s,n) ::
                //              s.nodes[n].messagesSent <= s.environment.allMessagesSent;
                         


                assert s'.environment.allMessagesSent ==  s.environment.allMessagesSent + multiset(messagesSentByTheNodes);

                assert  allMessagesSentWithoutRecipient(s'.environment) ==
                        allMessagesSentWithoutRecipient(s.environment) + 
                        fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes));

                lemmaGetSetOfSignedPayloadsONSets(
                    allMessagesSentWithoutRecipient(s'.environment),
                    allMessagesSentWithoutRecipient(s.environment),
                    fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))
                );

                assert getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)) ==
                        getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)) + 
                        getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));

                assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) +
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n);

                assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n);  

                // assert forall n | isInstrNodeHonest(s,n) && n != node ::
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) ==
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n);    

                assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n);     

                assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n);                                                          

                // assert forall n | isInstrNodeHonest(s,n) :: invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s,n);
                lemmaInvSetOfMessagesSentAndSignedByAnHonestNodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s,s',node);
                // assert invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s', node);
                // assert forall n | isInstrNodeHonest(s,n) :: invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s',n);
                // assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s');
                assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s');
            }
            else
            {
                lemmaAdversaryNextDoesNotChangeMessagesSentByHonestNodesExcludingSentToItself(s, s');
                assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s');
            }         

        }
        else
        {
            assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s');
        }
    }  

    lemma lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper(
        s: InstrDSState,
        s': InstrDSState,
        node: Address, 
        n: Address,
        A: set<set<SignedPayload>>,
        B: set<set<SignedPayload>>
    )
    requires node in s'.nodes && n in s'.nodes 
    requires s'.nodes.Keys == s.nodes.Keys
    requires forall n' | isInstrNodeHonest(s', n')  && n' != node :: s.nodes[n'].messagesSentToItself == s'.nodes[n'].messagesSentToItself; 
    requires A == (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n));
    requires B == (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n))
    ensures  A == B
    ensures B == A             
    {

    }

    lemma lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper2(
        A: set<QbftMessage>,
        B: set<QbftMessage>,
        n: Address
    )  
    requires A <= B 
    ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(A), n) <=  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(B), n)
    {

    }

    lemma lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper3Helper1(
        s': InstrDSState,
        n: Address,
        node: Address
    )   
    requires isInstrNodeHonest(s', node)
    requires isInstrNodeHonest(s', n)
    ensures  setUnion(set n' | n' in s'.nodes && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n))   
                           ==
            setUnion(
                (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n)) +
                {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n)}
                );   
    {
        var p := n' => isInstrNodeHonest(s', n');
        var q := n' => n' != node && isInstrNodeHonest(s', n');
        var m := (n':Address) requires n' in s'.nodes => filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n);

        assert p(node);
        assert !q(node);
        assert node in s'.nodes.Keys;
        assert forall x | x in s'.nodes.Keys :: m.requires(x);     


        lemmaSplitSetUnion<SignedPayload, Address>(
            s'.nodes.Keys,
            node,
            p,
            q,
            m
        );    


        var A := set x | x in s'.nodes.Keys && p(x) :: m(x); 
        var B := set x | x in s'.nodes.Keys && q(x) :: m(x);
        
        assert setUnion(A) == setUnion(B + {m(node)});  

        assert (set n' | n' in s'.nodes && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n))  == A;    
        assert (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n)) == B;
        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n) == m(node);  
    }   

    lemma lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper3Helper2(
        s': InstrDSState,
        n: Address,
        node: Address
    )   
    requires isInstrNodeHonest(s', node)
    requires isInstrNodeHonest(s', n)
    ensures  setUnion(
                (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n)) +
                {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n)}
                ) ==
                setUnion(set n' | n' in s'.nodes && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n));
    {
        lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper3Helper1(s', n, node);
    }
            

    lemma lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper3Helper3(
        s: InstrDSState,
        s': InstrDSState,
        n: Address,
        node: Address
    )   
    requires s.nodes.Keys == s'.nodes.Keys;
    requires forall n' :: isInstrNodeHonest(s, n') == isInstrNodeHonest(s', n');
    ensures  (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n)) ==
            (set n' | n' in s.nodes && n' != node && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n)) ;
    { }    

    // 177s 3.2.0
    lemma lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper3( 
        s:InstrDSState, 
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address,
        n: Address        
    )
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)    
    requires s != s'
    requires isInstrNodeHonest(s,node)
    requires InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node) 
    requires isInstrNodeHonest(s,n)    
    requires n != node;      
    ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n);     
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();        
        lemmaGetSetOfSignedPayloads();
        lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s, s');   

        var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

        assert InstrNodeNextSingleStep(s.nodes[node],messageReceived,s'.nodes[node],messagesSentByTheNodes);

        lMessagesSentByTheNodesOnHonestStepAreSubsetOfMessagesSentByAllHonestNodesThatDoNotTakeTheStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
        assert  forall n | isInstrNodeHonest(s,n) && n != node ::
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n); 

        assert s'.environment.allMessagesSent ==  s.environment.allMessagesSent + multiset(messagesSentByTheNodes);

        assert  allMessagesSentWithoutRecipient(s'.environment) ==
                allMessagesSentWithoutRecipient(s.environment) + 
                fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes));

        lemmaGetSetOfSignedPayloadsONSets(
            allMessagesSentWithoutRecipient(s'.environment),
            allMessagesSentWithoutRecipient(s.environment),
            fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))
        );

        assert getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)) ==
                getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)) + 
                getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));

        assert forall n | isInstrNodeHonest(s,n) && n != node ::
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) ==
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) +
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n);

        assert forall n | isInstrNodeHonest(s,n) && n != node ::
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) ==
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n);  

        lemmaiInvSetOfMessagesSentAndSignedByAnHonestNodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s,s',node);

        lMessagesSignedByAnHonestNodeThatDoesNotTakeTheStepInTheMessagesSentToItselfByTheHonestNodeThatTakesTheStepAreSubsetOfTheAllMessagesSentByTheNodeThatDoesNotTakeTheStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
        assert forall n | isInstrNodeHonest(s,n) && n != node ::
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n) <=
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);

        assert forall n | isInstrNodeHonest(s',n) && n != node ::
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n) <=
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n); 


        lemmaAllMesssagesSentIncSentToItselfWithoutRecipientFGFilter(s , n);
        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)),n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)),n) +
                setUnion(set n' | n' in s.nodes && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n));            
        lemmaAllMesssagesSentIncSentToItselfWithoutRecipientFGFilter(s' , n);
        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)),n) +
                setUnion(set n' | n' in s'.nodes && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n));     

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n)
                ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n) +
                setUnion(set n' | n' in s'.nodes && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n));   

        assert s.nodes[n].messagesSent == s'.nodes[n].messagesSent;

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) +
                setUnion(set n' | n' in s'.nodes && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n));  

        forall n' | isInstrNodeHonest(s', n')  && n' != node
        ensures s.nodes[n'].messagesSentToItself == s'.nodes[n'].messagesSentToItself; 
        {
            assert s.nodes[n'].messagesSent == s'.nodes[n'].messagesSent;
        }  

        assert forall n' | isInstrNodeHonest(s', n')  && n' != node :: s.nodes[n'].messagesSentToItself == s'.nodes[n'].messagesSentToItself; 

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n) 
                <=  
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);  

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) == 
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);   

        calc {
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n); 
                <=  
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);  
            ==
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n); 
            ==
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n); 
        }

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n)  
                <=
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n);  

        lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper3Helper1(
            s',
            n,
            node
        );

        assert setUnion(set n' | n' in s'.nodes && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n))   
                ==
                setUnion(
                    (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n)) +
                    {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n)}
                    );                          

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) +
                setUnion(
                    (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n)) +
                    {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n)}
                    );  

        var A := (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n));
        var B := {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n)};

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) +
                setUnion(
                    A + B
                    );

        var C := (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n));

        lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper(
            s,
            s',
            node,
            n,
            C,
            A
        );                    

        assert C  == A;
        assert A == C;

        lemmaSetUnionBasic(
            A,
            B,
            C,
            B
        );

        assert setUnion(
                    A +B
                    ) ==
                setUnion(
                    C +B
                        );     

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) +
                setUnion(
                    (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n)) +
                    {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n)}
                    ); 

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n) <= 
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n) <= 
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n);    

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n) <= 
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n);   

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n) <= 
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);  

        lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper2(
            s.nodes[node].messagesSentToItself,
            s'.nodes[node].messagesSentToItself,
            n
        );

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n) <=  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n);

        lemmaSetUnionEquation(
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n),
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n),
            C,
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n),
            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n)
        );   

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) +
                setUnion(
                    (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n)) +
                    {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n)}
                    );      

        assert s.nodes.Keys == s'.nodes.Keys;
        assert forall n' :: isInstrNodeHonest(s, n') == isInstrNodeHonest(s', n');

        lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper3Helper3(s, s', n , node);
        // assert (set n' | n' in s.nodes && n' != node && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n))  ==
        //        (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n));

        var D := (set n' | n' in s.nodes && n' != node && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n)) ;
        var D' := (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n));

        // assert D == D';
        assert D' == D;
        var E := {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n)};

        lemmaSetUnionBasic(
            D',
            E,
            D,
            E
        );

        assert setUnion(D' + E) == setUnion(D + E);

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) +
                setUnion(
                    D' + E
                    );  

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) +
                setUnion(
                    D + E
                    ); 
        // lemmaSetUnionBasic(
        //     (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n)),
        //     {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n)},
        //     set n' | n' in s.nodes && n' != node && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n),
        //     {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n)}
        // );

        // assert setUnion(
        //             (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n))+
        //             {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n)}
        //             ) ==
        //         setUnion(
        //             (set n' | n' in s.nodes && n' != node && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n)) +
        //             {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n)}
        //             );

        assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) +
                setUnion(
                    (set n' | n' in s.nodes && n' != node && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n)) +
                    {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n)}
                    );                            
                

        lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper3Helper2(
            s,
            n,
            node
        );

        assert setUnion(
                    (set n' | n' in s.nodes && n' != node && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n)) +
                    {filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n)}
                    ) ==
                    setUnion(
                    (set n' | n' in s.nodes && isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n))
                    );

        calc {
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')),n);
                ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) +
                setUnion(
                    (set n' | n' in s.nodes &&  isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n))
                    );
                == calc{
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);
                    == {assert invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s, n);}
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);
                }
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) +
                setUnion(
                    (set n' | n' in s.nodes &&  isInstrNodeHonest(s, n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n))
                    );                            
                ==  {lemmaAllMesssagesSentIncSentToItselfWithoutRecipientFGFilter(s, n);}
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n);                           
            
        }                        
        // assert (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n'].messagesSentToItself), n))  ==
        //         (set n' | n' in s'.nodes && n' != node && isInstrNodeHonest(s', n') :: filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n'].messagesSentToItself), n));

        // assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')), n) ==
        //  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n);  

        // assert s.nodes[node].messagesSent
        // assert invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s',n);                  
    }


    // 193s Fixed Inconclusive
    lemma lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(
        s:InstrDSState, 
        s': InstrDSState
    )    
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires InstrDSNextSingle(s, s')
    // ensures indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s')
    ensures invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s')
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();

        if s != s'
        {
            
            var node :| isNodeThatTakesStep(s, s', node);

            lemmaGetSetOfSignedPayloads();
            lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s, s');

   
            if isInstrNodeHonest(s,node)
            {
                var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

                assert InstrNodeNextSingleStep(s.nodes[node],messageReceived,s'.nodes[node],messagesSentByTheNodes);

                lMessagesSentByTheNodesOnHonestStepAreSubsetOfMessagesSentByAllHonestNodesThatDoNotTakeTheStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
                assert  forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n); 

                assert s'.environment.allMessagesSent ==  s.environment.allMessagesSent + multiset(messagesSentByTheNodes);

                assert  allMessagesSentWithoutRecipient(s'.environment) ==
                        allMessagesSentWithoutRecipient(s.environment) + 
                        fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes));

                lemmaGetSetOfSignedPayloadsONSets(
                    allMessagesSentWithoutRecipient(s'.environment),
                    allMessagesSentWithoutRecipient(s.environment),
                    fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))
                );

                assert getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)) ==
                        getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)) + 
                        getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));

                assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) +
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n);

                assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n);  

                lemmaiInvSetOfMessagesSentAndSignedByAnHonestNodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s,s',node);

                lMessagesSignedByAnHonestNodeThatDoesNotTakeTheStepInTheMessagesSentToItselfByTheHonestNodeThatTakesTheStepAreSubsetOfTheAllMessagesSentByTheNodeThatDoesNotTakeTheStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
                assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);

                assert forall n | isInstrNodeHonest(s',n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n); 

                forall n | isInstrNodeHonest(s,n) && n != node
                ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n);  
                {
                    lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper3(
                        s,
                        s',
                        messagesSentByTheNodes,
                        messagesReceivedByTheNodes,
                        node,
                        n
                    );
                }

                forall n | isInstrNodeHonest(s,n) && n != node
                ensures invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s', n);
                {
                    // assume invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s', n);
                    assert s.nodes[n].messagesSentToItself == s'.nodes[n].messagesSentToItself;    
                    assert s.nodes[n].messagesSent == s'.nodes[n].messagesSent;    
                    assert getAllMessagesSentByTheNode(s, n) == getAllMessagesSentByTheNode(s', n);    
                    assert invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s, n);
                    assert invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s', n);                    
                }

                // assert indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s');
                assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s');
            }
            else
            {
                lemmaAdversaryNextDoesNotChangeMessagesSentByHonestNodesIncludingSentToItself(s, s');
                assert messagesSentByHonestNodesIncludingSentToItselfDoNotChange(s, s');
                assert indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s');
                assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s');
            }         

        }
        else
        {
            assert indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s');
            assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s');
        }
    }    

    lemma lemmaInvMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodesToNotForAll(
        s: InstrDSState,
        n1: Address,
        n2: Address,
        m: SignedPayload
    )
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires && isInstrNodeHonest(s,n1) 
                && isInstrNodeHonest(s,n2) 
    requires m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n1].nodeState.messagesReceived), n2)
    ensures m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,n2))
    {  }    

    // 928s
    lemma lemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(
        s:  InstrDSState, 
        s': InstrDSState
    )    
    requires validInstrDSState(s) 
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires InstrDSNextSingle(s,s')
    ensures invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s') 
    ensures indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s')    
    {
        lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s,s');
        if s != s'
        {
            var messagesSentByTheNodes,
                messagesReceivedByTheNodes,
                node :|
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);  

            var messagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

            if isInstrNodeHonest(s,node)
            {
                lemmaSignedProposal();
                lemmaSignedPrepare();
                lemmaSignedCommit();
                lemmaSignedRoundChange(); 
                lemmaGetSetOfSignedPayloads();

                assert invNodesIdMatchesMapKey(s);

                var current := s.nodes[node];
                var next := s'.nodes[node];

                var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

                var newMessagesReceived := current.nodeState.messagesReceived + messageReceived;

                var currentForSubsteps :=
                    current.nodeState.(
                        messagesReceived := newMessagesReceived,
                        localTime := next.nodeState.localTime
                    );

                var nextForSubsteps := next.nodeState;

                forall n1, n2, m | 
                    && isInstrNodeHonest(s,n1) 
                    && isInstrNodeHonest(s,n2) 
                    && m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n1].nodeState.messagesReceived), n2)
                ensures m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',n2))
                {
                    assert getAllMessagesSentByTheNode(s,n2) <= getAllMessagesSentByTheNode(s',n2);
                    assert s.environment.allMessagesSent <= s'.environment.allMessagesSent;
                    assert getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)) <= getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment));
                    if n1 != n2
                    {
                        if n1 != node
                        {
                            // assert s.nodes[n1].nodeState.messagesReceived == s'.nodes[n1].nodeState.messagesReceived;
                            
                            // assert m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',n2)); 
                        }
                        else {
                            if m in getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived)
                            {
                                assert m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,n2));
                                assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n2].messagesSent)), n2);                                
                                assert m in getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment));
                                // // assert s.environment.allMessagesSent <= s'.environment.allMessagesSent;
                                assert m in getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment));
                                assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n2].messagesSent)), n2);
                                assert m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',n2));
                            }
                            else if(m in getSetOfSignedPayloads(messagesReceived))
                            {
                                assert m in getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment));
                                // assert s.environment.allMessagesSent <= s'.environment.allMessagesSent;
                                assert m in getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment));
                                assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n2);
                                assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n2].messagesSent)), n2);
                                assert m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',n2));                                
                            }
                            else
                            {
                                lemmaInstrNodeStateMessagesSentToItselfNotSignedByTheNodeHaveBeenReceived(current, messageReceived, next, messagesSentByTheNodes); 
                                assert false;            
                            }
                            
                        }
                    }
                    else
                    {
                        if n1 != node {
                            assert m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',n2));    
                        }
                        else
                        {
                            if m in getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived)
                            {
                                assert m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,n2));
                                assert m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',n2));
                            }
                            else if(m in getSetOfSignedPayloads(messagesReceived))
                            {
                                assert m in getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment));
                                // // assert s.environment.allMessagesSent <= s'.environment.allMessagesSent;
                                assert m in getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment));
                                assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n2);
                                assert invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s', n2);
                                assert m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n2].messagesSent)), n2);
                                assert m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',n2));                                
                            }
                            else
                            {
                                assert m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',n2));  
                            }
                        }
                    }
                }
                assert invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s');
            }  
            else
            {
                assert forall n1 |
                        && isInstrNodeHonest(s,n1) 
                    ::
                    s.nodes[n1].nodeState.messagesReceived == s'.nodes[n1].nodeState.messagesReceived;

                assert forall n2 |
                        && isInstrNodeHonest(s,n2) 
                    ::
                    getAllMessagesSentByTheNode(s,n2) == getAllMessagesSentByTheNode(s',n2);                    

                assert invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s');
            } 
        }
    }       
          
}