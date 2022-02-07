include "../../../spec/L1/types.dfy"
include "../distr_system_spec/common_functions.dfy"
include "../distr_system_spec/network.dfy"
include "../distr_system_spec/adversary.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"
include "../../../spec/L1/node.dfy"
include "../distr_system_spec/distributed_system.dfy"
include "../../common/sets.dfy"
include "instrumented_specs.dfy"
include "axioms.dfy"
include "aux_functions.dfy"
include "basic_invariants.dfy"
include "instr_dsstate_networking_common_invariants.dfy"
include "networking_invariants.dfy"
include "instr_node_state_invariants.dfy"
include "quorum.dfy"
include "general_lemmas.dfy"
include "instr_dsstate_invariants_defs.dfy"
include "instr_dsstate_invariants_2.dfy"
include "../theorems_defs.dfy"


module L1_RefinementForMutipleStep {
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_CommonFunctions
    import opened L1_Spec
    import opened L1_Adversary
    import opened HelperLemmasSets
    import opened L1_DistributedSystem
    import opened L1_InstrumentedSpecs
    import opened L1_Axioms
    import opened L1_AuxFunctionsProof
    import opened L1_AuxBasicInvariantsProof
    import opened L1_NetworkingInvariants
    import opened L1_InstrNodeStateInvariants
    import opened L1_LemmaQuorum
    import opened L1_GeneralLemmas
    import opened L1_InstrDSStateNetworkingCommonInvariants
    import opened L1_InstrDSStateInvariantsDefs
    import opened L1_InstrDSStateInvariantsNew 
    import opened L1_TheoremsDefs


    lemma lemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepHelper<T(!new)>(
        A: multiset<T>,
        o: seq<set<T>>
    )
    ensures fromMultisetToSet(A + multisetUnionOnSet(o)) == fromMultisetToSet(A + multiset(setUnionOnSeq(o)))
    {
        lemmaMultisetUnionOnSet(o);
        lemmaSetUnionOnSeq(o);
    }

    lemma lemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelper(
        s: NodeState,
        s': NodeState,
        m: set<QbftMessageWithRecipient>
    )
    requires validNodeState(s)
    requires NodeNextSubStep(s, s', m)
    ensures s.messagesReceived <= s'.messagesReceived
    {  }

    predicate instrDSStateMultisetSetMessagesSentEquivalenceHelper(
        s: InstrDSState,
        s': InstrDSState,
        n: Address
    )
    requires n in s.nodes 
    requires n in s'.nodes 
    {
        && s.nodes[n].nodeState == s'.nodes[n].nodeState
        && s.nodes[n].proposalsAccepted == s'.nodes[n].proposalsAccepted
        && s.nodes[n].messagesSentToItself == s'.nodes[n].messagesSentToItself
        && fromMultisetToSet(s.nodes[n].messagesSent) == fromMultisetToSet(s'.nodes[n].messagesSent)
    }


    predicate instrDSStateMultisetSetMessagesSentEquivalence(
        s: InstrDSState,
        s': InstrDSState
    )
    {
        && s.configuration == s'.configuration
        && s.adversary == s'.adversary
        && s.environment.nodes == s'.environment.nodes
        && s.environment.time == s'.environment.time
        && fromMultisetToSet(s.environment.allMessagesSent) == fromMultisetToSet(s'.environment.allMessagesSent)
        && s.nodes.Keys == s'.nodes.Keys
        && (
            forall n | n in s.nodes :: instrDSStateMultisetSetMessagesSentEquivalenceHelper(s, s', n)
        )
    }  

    // 98s
    lemma lemmaIndInvForConsistencyMaintainedByDSStateMultisetSetMessagesSentEquivalence(
        s: InstrDSState,
        s': InstrDSState
    )  
    requires instrDSStateMultisetSetMessagesSentEquivalence(s, s')  
    requires allIndInv(s)
    requires invBlockchainConsistency(s) 
    requires s'.environment.messagesSentYetToBeReceived <= s'.environment.allMessagesSent;
    ensures allIndInv(s')
    ensures invBlockchainConsistency(s')      
    {
        assert validInstrDSStateEx(s');
        assert invBlockchainConsistency(s');



        assert invConstantFields(s');
 
        assert invNodesIdMatchesMapKey(s');    
        assert invAdversaryMessagesReceivedHaveBeenSent(s');


        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();
        lemmaSignedHash();
        lemmaDigest();
        lemmaGetSetOfSignedPayloads();

        assert invEnvMessagesSentYetToBeReceivedIsASubsetOfAllMessagesSent(s');      

        assert indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s');

        assert allMessagesSentWithoutRecipient(s.environment) == allMessagesSentWithoutRecipient(s'.environment);
        assert getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)) == getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment));
        assert allMesssagesSentIncSentToItselfWithoutRecipient(s) == allMesssagesSentIncSentToItselfWithoutRecipient(s');
        assert getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s)) == getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s'));

        forall n |
            isInstrNodeHonest(s', n)
        ensures isInstrNodeHonest(s, n);
        ensures fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent) == fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent);
        ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) == 
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n);
        ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')), n);
        ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, n)), n) ==
                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', n)), n);         
        ensures getAllMessagesSentByTheNode(s, n) == getAllMessagesSentByTheNode(s', n);           
        {
            assert isInstrNodeHonest(s, n);
            assert fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent) == fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent);
            assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) == 
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n);
            assert  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n) ==
                     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')), n);
            assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, n)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', n)), n);
            assert getAllMessagesSentByTheNode(s, n) == getAllMessagesSentByTheNode(s', n);

        }

        forall n |
            isInstrNodeHonest(s', n)
        ensures isInstrNodeHonest(s, n);
        ensures indInvInstrNodeState(s'.nodes[n]);
        {
            assert indInvInstrNodeStateTypes(s'.nodes[n]);
            assert indInvInstrNodeStateProposalsAccepted(s'.nodes[n]);
            assert invInstrNodeStateProposalsAccepted(s'.nodes[n]);
            assert invInstrNodeStateNoConflictingPreapresSent(s'.nodes[n]);
            assert indInvInstrNodeStateNoConflictingPreapresSent(s'.nodes[n]);   
            assert invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(s'.nodes[n]);  
            assert invInstrNodeStateCommitSentOnlyIfAcceptedProposal(s'.nodes[n]);     
            assert invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyRoundChangeSent(s'.nodes[n]);
            assert invInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares(s'.nodes[n]);
            assert invInstrNodeStateIfCommitAndNextRoundChangeThenTheyMatch(s'.nodes[n]);
            assert invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(s'.nodes[n]);
            assert invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyMessageSent(s'.nodes[n]);
            assert invInstrNodeStatePrepareSentOnlyIfAcceptedProposal(s'.nodes[n]);
            assert invInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(s'.nodes[n]);
            assert validInstrState(s'.nodes[n]) ==> indInvInstrNodeStateAllProposalsAcceptedAreValid(s'.nodes[n]);
            assert validInstrStateEx(s'.nodes[n]) ==> invInstrNodeStateAllProposalsAcceptedAreValid(s'.nodes[n]);
            assert indInvProposalAcceptedHaveBeenReceived(s'.nodes[n]);
            assert invProposalAcceptedHaveBeenReceived(s'.nodes[n]);
            assert indInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(s'.nodes[n]);
            assert invRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(s'.nodes[n]);
            assert invInstrNodeStatePrepareAndCommitMatch(s'.nodes[n]);
            assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(s.nodes[n]);
            forall i | 1 <= i < |s'.nodes[n].nodeState.blockchain|
            ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(s'.nodes[n], i);
            {
                var b := s'.nodes[n].nodeState.blockchain[i];

                assert b  == s.nodes[n].nodeState.blockchain[i];
                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(s.nodes[n], i);
                var bm :| 
                    && bm in s.nodes[n].nodeState.messagesReceived
                    && bm.NewBlock?
                    && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
                    && bm.block.header.height == i 
                    && ValidNewBlock(s.nodes[n].nodeState.blockchain[..i], bm.block);  
                assert bm in s'.nodes[n].nodeState.messagesReceived;    
                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(s'.nodes[n], bm, b, i); 
                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(s'.nodes[n], i);      
            }
            assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(s'.nodes[n]);
            assert indInvInstrNodeState(s'.nodes[n]);
        }

        assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s');

        assert invIfPreparePaylodSentThenPrepareSent(s');  
        assert invIfRoundChangePaylodSentThenRoundChangeSent(s');

        assert invMessagesReceivedByHonestNodesHaveBeenSent(s');    

        assert invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s');
        assert invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s');

        assert invProposalAcceptedByHonestNodesHaveBeenSent(s');            

        assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s');
      
        
        assert indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s');
        assert invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s');        
        assert invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s');
        assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s');
        
        forall b, cs, a |
            && cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s'))
            && isInstrNodeHonest(s', a)
            && a == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
        ensures pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,a);
        {
            assert cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s));
            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s, b, a);
            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s', b, a);
        }
        
        assert invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s');    

        assert invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s');
        forall bm, n, blockchain |
                pBlockIsAValidBlockOfAnHonestBlockchain(s', bm, n, blockchain)
        ensures bm.block.header.proposer in validators(blockchain);
        {
            assert pBlockIsAValidBlockOfAnHonestBlockchain(s, bm, n, blockchain);
            assert bm.block.header.proposer in validators(blockchain);
            
        }
        assert invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s');              
    }      

    predicate pLemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelperHelper(
        simpseq: seq<InstrDSState>,
        s: InstrDSState,
        i: nat,
        node: Address
    )
    requires 1<= i <= |simpseq|
    requires node in s.nodes
    requires simpseq[i - 1].nodes.Keys == s.nodes.Keys
    {
        (forall n | n in s.nodes && n != node :: simpseq[i - 1].nodes[n] == s.nodes[n])
    }

    predicate pLemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelper(
        simpseq: seq<InstrDSState>,
        s: InstrDSState,
        o: seq<set<QbftMessageWithRecipient>>,
        i: nat,
        node: Address,
        messagesReceived: set<QbftMessage>,
        seqProposalsAccepted: seq<set<QbftMessage>>,
        ss: seq<NodeState>
    )
    requires 1<= i <= |simpseq|
    requires i  <= |o| + 1
    requires i <= |seqProposalsAccepted| + 1
    requires i  <= |ss|
    requires node in s.nodes
    {
        && simpseq[i - 1].nodes.Keys == s.nodes.Keys
        && simpseq[i - 1].adversary == s.adversary
        && simpseq[i - 1].configuration == s.configuration
        && simpseq[i - 1].environment.time == s.environment.time
        && simpseq[i - 1].environment.nodes == s.environment.nodes
        && simpseq[i - 1].environment.allMessagesSent == s.environment.allMessagesSent + multisetUnionOnSet(o[..i-1])
        && simpseq[i - 1].environment.messagesSentYetToBeReceived <= simpseq[i - 1].environment.allMessagesSent
        && pLemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelperHelper(simpseq, s, i, node)
        // && (forall n | n in s.nodes && n != node :: simpseq[i - 1].nodes[n] == s.nodes[n])   
        && simpseq[0] == s
        &&  (i > 1 ==> simpseq[i - 1].nodes[node].nodeState == ss[i-1])    
        && simpseq[i - 1].nodes[node].messagesSent == s.nodes[node].messagesSent + multisetUnionOnSet(o[..i-1])   
        && simpseq[i-1].nodes[node].messagesSentToItself == s.nodes[node].messagesSentToItself + 
                                                                        (simpseq[i-1].nodes[node].nodeState.messagesReceived - messagesReceived - s.nodes[node].nodeState.messagesReceived)
        && simpseq[i-1].nodes[node].proposalsAccepted == 
                        s.nodes[node].proposalsAccepted + setUnionOnSeq(seqProposalsAccepted[..i-1])
        && indInvForBlockchainConsistency(simpseq[i-1]) 
        && validInstrDSState(simpseq[i-1])

    }    

    // 63s 3.2.0
    lemma 
    {:fuel setUnionOnSeq<QbftMessage>,0,0}
    lemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelper(
        s: InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,        
        node: Address,
        simpseq: seq<InstrDSState>,
        i: nat,
        o: seq<set<QbftMessageWithRecipient>>,
        messagesReceived: set<QbftMessage>,
        seqProposalsAccepted: seq<set<QbftMessage>>,
        ss: seq<NodeState>
    ) returns (newsimpseq: seq<InstrDSState>)
    requires |ss| >= 2
    requires |o| == |ss| - 1
    requires
                    && (forall i | 0 <= i < |ss| - 1 ::
                        && validNodeState(ss[i])  
                        && NodeNextSubStep(ss[i], ss[i+1], o[i])
                    )         
    requires |simpseq| == i;
    requires seqProposalsAccepted == seq(
                        |ss|-1 ,
                        (i:nat) requires i + 1 < |ss| =>
                            getSingletonOfAcceptedProposals(ss[i+1])
                    )       
    requires 1 <= i <= |simpseq|
    requires i  <= |o| + 1
    requires i + 1 <= |ss|
    requires isInstrNodeHonest(s, node)   
    requires node in s'.nodes      
    requires pLemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelper(simpseq, s, o, i, node, messagesReceived, seqProposalsAccepted, ss);
    requires s.nodes[node].nodeState.messagesReceived <= simpseq[i-1].nodes[node].nodeState.messagesReceived;
    requires simpseq[0] == s
    requires i > 1 ==> messagesReceived <= simpseq[i-1].nodes[node].nodeState.messagesReceived;

    requires validInstrDSState(s)
    requires 
            var newMessagesReceived := s.nodes[node].nodeState.messagesReceived + messagesReceived;

            var currentWithNewMessagesReceived :=
                s.nodes[node].nodeState.(
                    messagesReceived := newMessagesReceived,
                    localTime := s.nodes[node].nodeState.localTime + 1
                );  
            ss[0] == currentWithNewMessagesReceived
    requires messagesReceived == set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
    requires  DSInstrNextNodeMultiple(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
    ensures |newsimpseq| == i + 1
    ensures pLemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelper.requires(newsimpseq, s, o, i+1, node, messagesReceived, seqProposalsAccepted, ss)
    ensures pLemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelper(newsimpseq, s, o, i+1, node, messagesReceived, seqProposalsAccepted, ss);
    ensures i+1 > 1 ==> messagesReceived <= newsimpseq[i].nodes[node].nodeState.messagesReceived;
    ensures s.nodes[node].nodeState.messagesReceived <= newsimpseq[i].nodes[node].nodeState.messagesReceived;
    {

        var messagesReceivedMultiset := if i == 1 then 
                                            messagesReceivedByTheNodes
                                        else
                                            multiset{};

        var mrSubstep := if i == 1 then
                            messagesReceived
                        else
                            {};

        var newMessagesSentToItself := 
                            ss[i].messagesReceived - mrSubstep - simpseq[i - 1].nodes[node].nodeState.messagesReceived; 

        


        var newInsrNodes :=
                    InstrNodeState(
                        ss[i],
                        simpseq[i-1].nodes[node].proposalsAccepted +  getSingletonOfAcceptedProposals(ss[i]),
                        simpseq[i-1].nodes[node].messagesSent + multiset(o[i-1]),
                        simpseq[i-1].nodes[node].messagesSentToItself + newMessagesSentToItself
                        // s.nodes[node].messagesSentToItself + (allMessagesReceivedSoFar - messagesReceived - allMessagesReceivedBefore)
                    );  

        assert i < |ss|;
        
        assert NodeNextSubStep(ss[i-1], ss[i], o[i-1]);
        lemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelper(ss[i-1], ss[i], o[i-1]);
        assert ss[i-1].messagesReceived <= ss[i].messagesReceived;
        assert simpseq[i-1].nodes[node].nodeState.messagesReceived <= newInsrNodes.nodeState.messagesReceived;
        assert s.nodes[node].nodeState.messagesReceived <= newInsrNodes.nodeState.messagesReceived;



        assert i > 1 ==> messagesReceived <= newInsrNodes.nodeState.messagesReceived;

        if i == 1 {
            assert messagesReceived <= newInsrNodes.nodeState.messagesReceived;
        }
        
        assert newInsrNodes.messagesSentToItself == s.nodes[node].messagesSentToItself + (newInsrNodes.nodeState.messagesReceived - messagesReceived - s.nodes[node].nodeState.messagesReceived); 

        assert 1<= |seqProposalsAccepted|;
        assert |seqProposalsAccepted| == |ss| - 1 >= i;
        assert |seqProposalsAccepted| >= i;
        assert i >= 1;

        lemmaUnionOnSetPreservesConcatenationWithTheLastElement(seqProposalsAccepted[..i]);
        assert seqProposalsAccepted[..i][..|seqProposalsAccepted[..i]|-1] == seqProposalsAccepted[..i-1];
        assert seqProposalsAccepted[..i][|seqProposalsAccepted[..i]|-1] == seqProposalsAccepted[i-1];                    

        assert setUnionOnSeq(seqProposalsAccepted[..i-1]) + seqProposalsAccepted[i-1] == setUnionOnSeq(seqProposalsAccepted[..i]);
        
        calc == {
            newInsrNodes.proposalsAccepted;
            simpseq[i-1].nodes[node].proposalsAccepted +  getSingletonOfAcceptedProposals(ss[i]);
            s.nodes[node].proposalsAccepted + setUnionOnSeq(seqProposalsAccepted[..i-1]) +  getSingletonOfAcceptedProposals(ss[i]);
            s.nodes[node].proposalsAccepted + setUnionOnSeq(seqProposalsAccepted[..i-1]) +  seqProposalsAccepted[i-1];
            s.nodes[node].proposalsAccepted + (setUnionOnSeq(seqProposalsAccepted[..i-1]) +  seqProposalsAccepted[i-1]);
            s.nodes[node].proposalsAccepted + setUnionOnSeq(seqProposalsAccepted[..i]);
        }


        var newNodes := simpseq[i-1].nodes[node := newInsrNodes];     

        var newNetwork := Network(
            simpseq[i-1].environment.nodes,
            simpseq[i-1].environment.messagesSentYetToBeReceived - messagesReceivedMultiset + multiset(o[i-1]),
            simpseq[i-1].environment.time,
            simpseq[i-1].environment.allMessagesSent + multiset(o[i-1])
        );      


        
        lemmaMultisetUnionOnSetPreservesConcatenationOfTruncatedSequenceWithItsLastElement(o, i-1);

        
        // assert newNetwork.allMessagesSent == s.environment.allMessagesSent + multisetUnionOnSet(o[..i]);
        // assert newNetwork.messagesSentYetToBeReceived <= newNetwork.allMessagesSent;

        var newInstrDSState := 
            InstrDSState(
                simpseq[i-1].configuration,
                newNetwork,
                newNodes,
                simpseq[i-1].adversary
            );

        
        newsimpseq := simpseq + [newInstrDSState]; 
        
        if i == 1
        {
            assert NodeNextSubStep(ss[0], ss[1], o[0]);
            assert NodeNextSingleStep(s.nodes[node].nodeState, messagesReceived, ss[1], o[0]);
            assert NodeNextSingleStep(newsimpseq[i-1].nodes[node].nodeState, mrSubstep, newsimpseq[i].nodes[node].nodeState, o[i-1]);   
        }
        else
        {
            assert NodeNextSubStep(ss[i-1], ss[i], o[i-1]);
            var newTime := ss[i-1].localTime;
            var inQbftMessages' := {};
            var  newMessagesReceived' := ss[i-1].messagesReceived + inQbftMessages';
            var currentWithNewMessagesReceived' :=
                ss[i-1].(
                    messagesReceived := newMessagesReceived',
                    localTime := newTime
                );
            assert currentWithNewMessagesReceived'.messagesReceived == newMessagesReceived' == ss[i-1].messagesReceived; 
            assert currentWithNewMessagesReceived'.messagesReceived == ss[i-1].messagesReceived; 
            assert currentWithNewMessagesReceived'.localTime == ss[i-1].localTime; 
            assert currentWithNewMessagesReceived' == ss[i-1];
            assert NodeNextSubStep(currentWithNewMessagesReceived', ss[i], o[i-1]);

            assert NodeNextSingleStep(ss[i-1], {}, ss[i], o[i-1]);                        
        
            assert NodeNextSingleStep(newsimpseq[i-1].nodes[node].nodeState, mrSubstep, newsimpseq[i].nodes[node].nodeState, o[i-1]);   
        }
        assert NodeNextSingleStep(newsimpseq[i-1].nodes[node].nodeState, mrSubstep, newsimpseq[i].nodes[node].nodeState, o[i-1]);
        
        
        assert mrSubstep == set mr:QbftMessageWithRecipient | mr in messagesReceivedMultiset :: mr.message;
        assert InstrNodeNextSingleStep(
            newsimpseq[i-1].nodes[node], 
            set mr:QbftMessageWithRecipient | mr in messagesReceivedMultiset :: mr.message, 
            newsimpseq[i].nodes[node], 
            o[i-1]);
        

        assert NetworkNext(
            newsimpseq[i-1].environment,
            newsimpseq[i].environment,
            o[i-1],
            messagesReceivedMultiset
        );  

        
        
        assert InstrDSNextNodeSingle(newsimpseq[i-1], newsimpseq[i], o[i-1], messagesReceivedMultiset, node);
        assert InstrDSNextSingle(newsimpseq[i-1], newsimpseq[i]);
        lemmavalidDSStateInv(newsimpseq[i-1], newsimpseq[i]);
        
        assert indInvForBlockchainConsistency(newsimpseq[i]) && validInstrDSState(newsimpseq[i]);
        
        assert pLemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelper(newsimpseq, s, o, i+1, node, messagesReceived, seqProposalsAccepted, ss);   
    }

    lemma 
    {:fuel setUnionOnSeq<QbftMessage>,0,0}
    lemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStep(
        s: InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,        
        node: Address
    ) returns (ssimp': InstrDSState)
    requires indInvForBlockchainConsistency(s)
    requires validInstrDSState(s)
    requires isInstrNodeHonest(s, node)
    requires DSInstrNextNodeMultiple(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
    requires s.environment.messagesSentYetToBeReceived <= s.environment.allMessagesSent          
    ensures  instrDSStateMultisetSetMessagesSentEquivalence(s', ssimp');  
    ensures && indInvForBlockchainConsistency(ssimp') 
                && validInstrDSState(ssimp');     
    {
        var messagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
        assert  InstrNodeNextMultiple(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes);
        var current := s.nodes[node].nodeState;
        var next := s'.nodes[node].nodeState;
        assert NodeNext(current,messagesReceived,next,messagesSentByTheNodes);

        var newMessagesReceived := current.messagesReceived + messagesReceived;

        var currentWithNewMessagesReceived :=
            current.(
                messagesReceived := newMessagesReceived,
                localTime := current.localTime + 1
            );  
        assert InstrNodeNextMultipleHelper(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes);

        var 
            ss:seq<NodeState>, o:seq<set<QbftMessageWithRecipient>>, seqProposalsAccepted :|
            && |ss| >= 2
            && |o| == |ss| - 1
            && ss[0] == currentWithNewMessagesReceived
            && ss[|ss|-1] == next
            && (forall i | 0 <= i < |ss| - 1 ::
                && validNodeState(ss[i])  
                && NodeNextSubStep(ss[i], ss[i+1], o[i])
            )          
            && (forall afterNext, messages | afterNext != ss[|ss|-1] :: 
                !(
                    && validNodeState(ss[|ss|-1])
                    && NodeNextSubStep(ss[|ss|-1], afterNext, messages)
                )
            )
            && messagesSentByTheNodes == setUnionOnSeq(o)
            && 
            seqProposalsAccepted == seq(
                |ss|-1 ,
                (i:nat) requires i + 1 < |ss| =>
                    getSingletonOfAcceptedProposals(ss[i+1])
            )   
            && s'.nodes[node].proposalsAccepted ==  s.nodes[node].proposalsAccepted + setUnionOnSeq(seqProposalsAccepted);
          
        var simpseq := [s];
        assert multisetUnionOnSet(o[..0]) == multiset{}; 
        lemmaSetUnionOnSeqEmpty(seqProposalsAccepted[..0]);
        assert setUnionOnSeq(seqProposalsAccepted[..0]) == {};
        assert messagesReceived <= currentWithNewMessagesReceived.messagesReceived;

        assert simpseq[0].nodes[node].messagesSentToItself == s.nodes[node].messagesSentToItself + 
                                                                (simpseq[0].nodes[node].nodeState.messagesReceived - messagesReceived - s.nodes[node].nodeState.messagesReceived);   

        assert  simpseq[0].nodes[node].proposalsAccepted == 
                s.nodes[node].proposalsAccepted + setUnionOnSeq(seqProposalsAccepted[..0]);   

        assert pLemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelper(simpseq, s, o, 1, node, messagesReceived, seqProposalsAccepted, ss);
        assert DSInstrNextNodeMultiple(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

        for i := 1 to  |ss| 
            invariant DSInstrNextNodeMultiple(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
            invariant |simpseq| == i;
            invariant pLemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelper(simpseq, s, o, i, node, messagesReceived, seqProposalsAccepted, ss);           
            invariant i > 1 ==> messagesReceived <= simpseq[i-1].nodes[node].nodeState.messagesReceived;
            invariant s.nodes[node].nodeState.messagesReceived <= simpseq[i-1].nodes[node].nodeState.messagesReceived;
        {
         

            simpseq:= lemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelper(
                s,
                s',
                messagesSentByTheNodes,
                messagesReceivedByTheNodes,
                node,
                simpseq,
                i,
                o,
                messagesReceived,
                seqProposalsAccepted,
                ss
            );
                
        }     

        assert |simpseq| == |ss|;
        assert pLemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelper(simpseq, s, o, |simpseq|, node, messagesReceived, seqProposalsAccepted, ss);

        assert o[..|ss|-1] == o;
        assert seqProposalsAccepted[..|ss|-1] == seqProposalsAccepted;   

        assert simpseq[|simpseq|-1].nodes.Keys == s'.nodes.Keys;
        assert simpseq[|simpseq|-1].adversary == s'.adversary;
        assert simpseq[|simpseq|-1].configuration == s'.configuration;

        assert simpseq[|simpseq|-1].environment.time == s'.environment.time;
        assert simpseq[|simpseq|-1].environment.nodes == s'.environment.nodes;

        assert s'.environment.allMessagesSent == s.environment.allMessagesSent + multiset(setUnionOnSeq(o));
        assert simpseq[|simpseq|-1].environment.allMessagesSent == s.environment.allMessagesSent + multisetUnionOnSet(o);
        lemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepHelper(s.environment.allMessagesSent, o);
        assert fromMultisetToSet(simpseq[|simpseq|-1].environment.allMessagesSent) == fromMultisetToSet(s'.environment.allMessagesSent);  

        assert simpseq[|simpseq|-1].environment.messagesSentYetToBeReceived <= simpseq[|simpseq| - 1].environment.allMessagesSent;

        assert pLemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepForLoopHelperHelperHelper(simpseq, s', |simpseq|, node);

        forall n | n in s'.nodes
        ensures instrDSStateMultisetSetMessagesSentEquivalenceHelper(s', simpseq[|simpseq|-1],  n)
        {
            if n == node 
            {
                assert simpseq[|simpseq| - 1].nodes[node].messagesSent == s.nodes[node].messagesSent + multisetUnionOnSet(o); 
                assert s'.nodes[node].messagesSent == s.nodes[node].messagesSent + multiset(setUnionOnSeq(o));
                lemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStepHelper(s.nodes[node].messagesSent, o);
                assert fromMultisetToSet(simpseq[|simpseq|-1].nodes[node].messagesSent) == fromMultisetToSet(s'.nodes[node].messagesSent ); 

                assert simpseq[|simpseq|-1].nodes[node].messagesSentToItself == s'.nodes[node].messagesSentToItself;
                assert simpseq[|simpseq|-1].nodes[node].nodeState == s'.nodes[node].nodeState; 

                assert simpseq[|simpseq|-1].nodes[node].proposalsAccepted == s.nodes[node].proposalsAccepted + setUnionOnSeq(seqProposalsAccepted);
                assert s'.nodes[node].proposalsAccepted ==  s.nodes[node].proposalsAccepted + setUnionOnSeq(seqProposalsAccepted);
                assert simpseq[|simpseq|-1].nodes[node].proposalsAccepted == s'.nodes[node].proposalsAccepted;  
                assert instrDSStateMultisetSetMessagesSentEquivalenceHelper(simpseq[|simpseq|-1], s', n);                              
            }
            else
            {
                assert s'.nodes[n] == simpseq[|simpseq|-1].nodes[n];
            }
        }
        
        assert instrDSStateMultisetSetMessagesSentEquivalence(s', simpseq[|simpseq|-1]);                       

        assert && indInvForBlockchainConsistency(simpseq[|simpseq|-1]) 
                && validInstrDSState(simpseq[|simpseq|-1]);              
        
        ssimp' := simpseq[|simpseq|-1];
    }

    lemma 
    {:fuel setUnionOnSeq<QbftMessage>,0,0}
    lemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfMultipleStep(
        s: InstrDSState,
        s': InstrDSState
    ) returns (ssimp': InstrDSState)
    requires indInvForBlockchainConsistency(s)
    requires validInstrDSState(s)
    requires InstrDSNextMultiple(s, s')
    requires s.environment.messagesSentYetToBeReceived <= s.environment.allMessagesSent
    ensures indInvForBlockchainConsistency(ssimp')
    ensures validInstrDSState(ssimp') 
    ensures instrDSStateMultisetSetMessagesSentEquivalence(s', ssimp')
    {
        if s == s'
        {

            ssimp' := s';
            assert indInvForBlockchainConsistency(ssimp');
            assert validInstrDSState(ssimp');
            assert instrDSStateMultisetSetMessagesSentEquivalence(s', ssimp');
            assert ssimp'.environment.messagesSentYetToBeReceived <= ssimp'.environment.allMessagesSent;
        }
        else
        {

            var messagesSentByTheNodes,
                    messagesReceivedByTheNodes,
                    node :|
                    DSInstrNextNodeMultiple(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
            

            if !isInstrNodeHonest(s,node)
            {
                var simpseq := [s, s'];
                assert  
                    && |simpseq| >= 2 
                    && simpseq[0] == s
                    && simpseq[|simpseq|-1] == s'
                    && validInstrDSState(simpseq[0]);

                assert InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                assert InstrDSNextSingle(simpseq[0], simpseq[1]);
                lemmavalidDSStateInv(simpseq[0], simpseq[1]);

                ssimp' := simpseq[1];
                assert indInvForBlockchainConsistency(ssimp');
                assert validInstrDSState(ssimp');
                assert instrDSStateMultisetSetMessagesSentEquivalence(s', ssimp');
                assert ssimp'.environment.messagesSentYetToBeReceived <= ssimp'.environment.allMessagesSent;                
            }   
            else
            {
                ssimp' := lemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfHonestMultipleStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);                      
            }   
        }  
    }

    lemma lemmavalidDSStateInv(
        s: InstrDSState,
        s': InstrDSState
    )
    requires validInstrDSState(s)
    requires indInvForBlockchainConsistency(s)
    requires InstrDSNextSingle(s, s')    
    ensures indInvForBlockchainConsistency(s')
    ensures validInstrDSState(s') 
    {
        reveal_indInvForBlockchainConsistency();
        lemmaInvBlockchainConsistencyWithAllInductiveInvariants(s, s');
    }       
    
    lemma lemmaInstrDSStateStabilityMultiStepHelper1(
        s: NodeState,
        s': NodeState,
        m: set<QbftMessageWithRecipient>
    )
    requires validNodeState(s)
    requires NodeNextSubStep(s, s', m)
    ensures s.blockchain <= s'.blockchain
    {  }

    lemma lemmaInstrDSStateStabilityMultiStep(
        s: InstrDSState,
        s': InstrDSState
    )
    requires validInstrDSState(s)
    requires InstrDSNextMultiple(s, s')
    ensures forall n | isInstrNodeHonest(s, n) :: s.nodes[n].nodeState.blockchain <= s'.nodes[n].nodeState.blockchain
    ensures forall n :: isInstrNodeHonest(s, n) <== isInstrNodeHonest(s', n)
    {
        if s == s'
        {
            assert s.nodes == s'.nodes;
            assert forall n | isInstrNodeHonest(s, n) :: s.nodes[n].nodeState.blockchain == s'.nodes[n].nodeState.blockchain;
        }
        else
        {

            var messagesSentByTheNodes,
                    messagesReceivedByTheNodes,
                    node :|
                    DSInstrNextNodeMultiple(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

            if !isInstrNodeHonest(s,node)
            {
                assert forall n | isInstrNodeHonest(s, n) :: s.nodes[n].nodeState.blockchain == s'.nodes[n].nodeState.blockchain;
            }
            else
            {

                var messagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
                assert  InstrNodeNextMultiple(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes);
                var current := s.nodes[node].nodeState;
                var next := s'.nodes[node].nodeState;
                assert NodeNext(current,messagesReceived,next,messagesSentByTheNodes);

                var newMessagesReceived := current.messagesReceived + messagesReceived;

                var currentWithNewMessagesReceived :=
                    current.(
                        messagesReceived := newMessagesReceived,
                        localTime := current.localTime + 1
                    );  

                var 
                    ss:seq<NodeState>, o:seq<set<QbftMessageWithRecipient>>:|
                    && |ss| >= 2
                    && |o| == |ss| - 1
                    && ss[0] == currentWithNewMessagesReceived
                    && ss[|ss|-1] == next
                    && (forall i | 0 <= i < |ss| - 1 ::
                        && validNodeState(ss[i])  
                        && NodeNextSubStep(ss[i], ss[i+1], o[i])
                    )          
                    && (forall afterNext, messages | afterNext != ss[|ss|-1] :: 
                        !(
                            && validNodeState(ss[|ss|-1])
                            && NodeNextSubStep(ss[|ss|-1], afterNext, messages)
                        )
                    )
                    && messagesSentByTheNodes == setUnionOnSeq(o);

                for i := 1 to |ss|
                invariant s.nodes[node].nodeState.blockchain <= ss[i-1].blockchain
                {
                    lemmaInstrDSStateStabilityMultiStepHelper1(ss[i-1], ss[i], o[i-1]);
                    assert ss[i-1].blockchain <= ss[i].blockchain;
                }

                assert s.nodes[node].nodeState.blockchain  <= s.nodes[node].nodeState.blockchain;
                forall n | isInstrNodeHonest(s, n)
                ensures s.nodes[n].nodeState.blockchain  <= s'.nodes[n].nodeState.blockchain;
                {
                    if n == node 
                    {
                        assert s.nodes[n].nodeState.blockchain  <= s'.nodes[n].nodeState.blockchain;
                    }
                    else
                    {
                        assert s.nodes[n].nodeState.blockchain  <= s'.nodes[n].nodeState.blockchain;   
                    }
                }
            }
        }
    }    

    predicate {:opaque} indInvForBlockchainConsistency(s: InstrDSState)
    ensures indInvForBlockchainConsistency(s) ==> validInstrDSState(s)
    {
        && allIndInv(s)
        && invBlockchainConsistency(s)
    }      

    lemma lemmaInstrDSNextMultipleIndInvForBlockchainConsistency(
        s: InstrDSState,
        s': InstrDSState
    )
    requires indInvForBlockchainConsistency(s)
    requires InstrDSNextMultiple(s, s')
    ensures indInvForBlockchainConsistency(s')
    {
        reveal_indInvForBlockchainConsistency();
        assert s.environment.messagesSentYetToBeReceived <= s.environment.allMessagesSent;
        assert s'.environment.messagesSentYetToBeReceived <= s'.environment.allMessagesSent;
        var ssimp' := lemmaGetStateSuchThatInductiveInvariantsForConsistencyAreSatisfiedAndItIsInstrDSStateMultisetSetMessagesSentEquivalentToDestinationInstrDSStateOfMultipleStep(s, s');
        assert instrDSStateMultisetSetMessagesSentEquivalence(s', ssimp');
        assert instrDSStateMultisetSetMessagesSentEquivalence(ssimp', s');
        lemmaIndInvForConsistencyMaintainedByDSStateMultisetSetMessagesSentEquivalence(ssimp', s');
        assert indInvForBlockchainConsistency(s');
    }

    lemma lemmaIndPredNonOpaqueIsTrueInInit(
        s: InstrDSState,
        configuration:Configuration
    )
    requires InstrDSInit(s, configuration)
    ensures indInvForBlockchainConsistency(s)
    {
        lemmaIndInvIsTrueInInit(s, configuration);
        reveal_indInvForBlockchainConsistency();
    }

}