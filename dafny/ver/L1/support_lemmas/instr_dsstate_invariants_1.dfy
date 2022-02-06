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
include "instr_dsstate_networking_common_invariants.dfy"
include "networking_invariants.dfy"
include "networking_invariants_lemmas.dfy"
include "networking_step_lemmas.dfy"
include "instr_node_state_invariants.dfy"
include "quorum.dfy"
include "general_lemmas.dfy"
include "instr_dsstate_invariants_defs.dfy"
include "../theorems_defs.dfy"


// TODO: Rename file and module
module EEAInstrDSStateInvariantsHeavy
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
    import opened EEANetworkingInvariants
    import opened EEAInstrNodeStateInvariants
    import opened EEALemmaQuorum
    import opened EEAGeneralLemmas
    import opened EEAInstrDSStateNetworkingCommonInvariants
    import opened EEAInstrDSStateInvariants
    import opened EEANetworkingInvariantsLemmas
    import opened EEANetworkingStepLemmas
    import opened EEATheoremsDefs


    lemma lemmaPBlockchainConsistencyUpToHeightImpliesConsistencyForHonestBlockchainOfThatHeightHelper(
        s:InstrDSState,
        h: nat,
        bc1: Blockchain,
        bc2: Blockchain,
        n1: Address,
        n2: Address
    )
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires isInstrNodeHonest(s, n1)
    requires isInstrNodeHonest(s, n2)
    requires |bc1| == |bc2| == h
    requires bc1 <= s.nodes[n1].nodeState.blockchain
    requires bc2 <= s.nodes[n2].nodeState.blockchain
    ensures consistentBlockchains(bc1, bc2)
    ensures areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1, bc2);
    ensures areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc2, bc1);
    ensures fromBlockchainToRawBlockchain(bc1) == fromBlockchainToRawBlockchain(bc2);    
    {
        assert bc1 == truncateSeq(s.nodes[n1].nodeState.blockchain, h);
        assert bc2 == truncateSeq(s.nodes[n2].nodeState.blockchain, h);
        assert consistentBlockchains(bc1, bc2);
        lemmaPrefixesOfConsistentBlockchainsAreConsistenAndIfOfTheSameLengthThenAreAlsoFromBlockchainToRawBlockchainEquivalentAndAreBlockchainsTheSameExceptForTheCommitSealsAndRound(
            bc1,
            bc2,
            bc1,
            bc2
        );
        assert areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1, bc2);
        assert areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc2, bc1);
        assert fromBlockchainToRawBlockchain(bc1) == fromBlockchainToRawBlockchain(bc2);
    }    

    lemma lemmaPBlockchainConsistencyUpToHeightImpliesConsistencyForHonestBlockchainOfThatHeight(
        s:InstrDSState,
        h: nat,
        n1: Address,
        n2: Address
    )
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires isInstrNodeHonest(s, n1)
    requires isInstrNodeHonest(s, n2)
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires |s.nodes[n2].nodeState.blockchain| >= h
    ensures 
            var bc1 := s.nodes[n1].nodeState.blockchain[..h];
            var bc2 := s.nodes[n2].nodeState.blockchain[..h];
            && consistentBlockchains(bc1, bc2)
            && areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc1, bc2)
            && areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc2, bc1)
            && fromBlockchainToRawBlockchain(bc1) == fromBlockchainToRawBlockchain(bc2)
    {
        var bc1 := s.nodes[n1].nodeState.blockchain[..h];
        var bc2 := s.nodes[n2].nodeState.blockchain[..h];
        lemmaPBlockchainConsistencyUpToHeightImpliesConsistencyForHonestBlockchainOfThatHeightHelper(
            s,
            h,
            bc1,
            bc2,
            n1,
            n2
        );

    }  

    // 2s 3.2.0
    lemma lemmaInvBlockchainConsistencyImpliesInvBlockchainConsistencyUpToHeight(
        s:InstrDSState,
        h: nat
    ) 
    requires invBlockchainConsistency(s) 
    ensures pBlockchainConsistencyUpToHeight(s, h)
    {
        forall n1,n2 |  && isInstrNodeHonest(s,n1)
                        && isInstrNodeHonest(s,n2)
        ensures var b1 := fromBlockchainToRawBlockchain(truncateSeq(s.nodes[n1].nodeState.blockchain, h));
                var b2 := fromBlockchainToRawBlockchain(truncateSeq(s.nodes[n2].nodeState.blockchain, h));
                || b1 <= b2
                || b2 <= b1
        {
            var bc1 := fromBlockchainToRawBlockchain(s.nodes[n1].nodeState.blockchain);
            var bc2 := fromBlockchainToRawBlockchain(s.nodes[n2].nodeState.blockchain);
            var b1 := fromBlockchainToRawBlockchain(truncateSeq(s.nodes[n1].nodeState.blockchain, h));
            var b2 := fromBlockchainToRawBlockchain(truncateSeq(s.nodes[n2].nodeState.blockchain, h));

            if bc1 <= bc2 
            {
                lemmaOnFromBlockchainToRawBlockchainPrefixImpliesBlockchainsTruncatedToTheSameLengthAreTheSameExceptForTheCommitSealsAndRound(s.nodes[n1].nodeState.blockchain, s.nodes[n2].nodeState.blockchain);
                assert b1 <= b2;
            }
            else
            {
                lemmaOnFromBlockchainToRawBlockchainPrefixImpliesBlockchainsTruncatedToTheSameLengthAreTheSameExceptForTheCommitSealsAndRound(s.nodes[n2].nodeState.blockchain, s.nodes[n1].nodeState.blockchain);
                assert b2 <= b1;
            }
        }

    }      

    //~ 215s 3.2.0
    lemma lemmaInvNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(
        s:InstrDSState, 
        s': InstrDSState
    )    
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires InstrDSNextSingle(s, s')
    ensures liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s')
    ensures indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s')
    ensures invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s')    
    ensures invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s')
    {
        lemmaSignedPrepare();
        lemmaGetSetOfSignedPayloads();
        lemmaIndInvInstrNodeStateLifterToInstrDSState(s,s');
        lemmaInvIfPreparePaylodSentThenPrepareSent(s, s');

 
        lemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s,s');

        assert invIfPreparePaylodSentThenPrepareSent(s');

        forall n, m1, m2 | 
                && isInstrNodeHonest(s',n)
                && m1 in s'.nodes[n].nodeState.messagesReceived
                && m2 in s'.nodes[n].nodeState.messagesReceived
                && m1.Prepare?
                && m2.Prepare?
                &&  var uPayload1 := m1.preparePayload.unsignedPayload;
                    var uPayload2 := m2.preparePayload.unsignedPayload;
                &&  uPayload1.height == uPayload2.height
                &&  uPayload1.round == uPayload2.round
                && recoverSignedPrepareAuthor(m1.preparePayload) ==  recoverSignedPrepareAuthor(m2.preparePayload)
                && isInstrNodeHonest(s,recoverSignedPrepareAuthor(m1.preparePayload))                 
        ensures var uPayload1 := m1.preparePayload.unsignedPayload;
                var uPayload2 := m2.preparePayload.unsignedPayload;
                uPayload1.digest == uPayload2.digest
        {  
            var sender := recoverSignedPrepareAuthor(m1.preparePayload);

            var spp1 := SignedPreparePayload(m1.preparePayload);
            assert spp1 in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', sender));
            assert spp1 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', sender)), sender);
            var pm1: QbftMessage :| pm1.Prepare? && pm1 in getAllMessagesSentByTheNode(s', sender) && pm1.preparePayload == m1.preparePayload;

            var spp2 := SignedPreparePayload(m2.preparePayload);
            assert spp2 in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', sender));
            assert spp2 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', sender)), sender);
            var pm2: QbftMessage :| pm2.Prepare? && pm2 in getAllMessagesSentByTheNode(s', sender) && pm2.preparePayload == m2.preparePayload;            
            // assert m1 in getAllMessagesSentByTheNode(s', recoverSignedPrepareAuthor(m1.preparePayload));        
                // lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s,s');                           

            // lemmaIndInvInstrNodeStateLifterToInstrDSState(s,s');
        }         
       
    }  

    lemma lemmaGetCommitSealUnion(s1:set<QbftMessage>, s2:set<QbftMessage>)
    ensures getCommitSeals(s1) + getCommitSeals(s2) == getCommitSeals(s1+s2)
    {

    }    

    // 2s 3.2.0
    lemma lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper0(
        s:InstrDSState, 
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address,
        cs: Signature
    )    
    requires validInstrDSState(s)  
    requires cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s'))
    requires !isInstrNodeHonest(s, node)
    requires InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node)
    ensures  || cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
             || cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));
    {
        
        assert allMesssagesSentIncSentToItselfWithoutRecipient(s') ==
                    allMesssagesSentIncSentToItselfWithoutRecipient(s) + 
                    fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)); 

        assert  cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s) + 
                        fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));

        lemmaGetCommitSealUnion(allMesssagesSentIncSentToItselfWithoutRecipient(s),
                                fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));        
    }    


    // 2s 3.2.0
    lemma lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper1(
        s:InstrDSState, 
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )    
    requires validInstrDSState(s)  
    requires !isInstrNodeHonest(s, node)
    requires InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node)
    ensures forall cs,b |  && cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)))
                        && isInstrNodeHonest(s, recoverSignedHashAuthor(hashBlockForCommitSeal(b),cs))
            ::  cs in getCommitSeals(s'.adversary.messagesReceived);
    {
        lemmaSignedHash();
        lemmaDigest();
        forall cs,b |  && cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)))
                        && isInstrNodeHonest(s, recoverSignedHashAuthor(hashBlockForCommitSeal(b),cs))
        ensures cs in getCommitSeals(s'.adversary.messagesReceived);
        {
            var csAuthor := recoverSignedHashAuthor(hashBlockForCommitSeal(b),cs);

            assert isInstrNodeHonest(s, csAuthor);
            assert isInstrNodeHonest(s', csAuthor);

            assert exists m ::  && m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))
                                && (
                                    || (
                                        && m.Commit?
                                        && m.commitPayload.unsignedPayload.commitSeal == cs
                                    )
                                    || (
                                        && m.NewBlock?
                                        && cs in m.block.header.commitSeals
                                    )
                                );

            assert  ||  (exists m ::    && m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))
                                        && m.Commit?
                                        && m.commitPayload.unsignedPayload.commitSeal == cs)

                    ||  (exists m ::    && m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))
                                        && m.NewBlock?
                                        && cs in m.block.header.commitSeals);

            var m :| && m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))
                                && (
                                    || (
                                        && m.Commit?
                                        && m.commitPayload.unsignedPayload.commitSeal == cs
                                    )
                                    || (
                                        && m.NewBlock?
                                        && cs in m.block.header.commitSeals
                                    )
                                );

            if m.Commit?
            {
                assert m.commitPayload.unsignedPayload.commitSeal == cs;
                assert
                        || (cs in getCommitSeals(s'.adversary.messagesReceived))
                        || (forall b | digest(b) == m.commitPayload.unsignedPayload.digest :: 
                                recoverSignedHashAuthor(hashBlockForCommitSeal(b),cs) in s.adversary.byz);  
                assert (recoverSignedHashAuthor(hashBlockForCommitSeal(b),cs) !in s.adversary.byz);                  
                assert cs in getCommitSeals(s'.adversary.messagesReceived);
            }
            else
            {
                assert cs in m.block.header.commitSeals;
                assert  || (cs in getCommitSeals(s'.adversary.messagesReceived))
                        || (recoverSignedHashAuthor(hashBlockForCommitSeal(m.block),cs) in s.adversary.byz);    

                assert (recoverSignedHashAuthor(hashBlockForCommitSeal(m.block),cs) !in s.adversary.byz);       
                assert cs in getCommitSeals(s'.adversary.messagesReceived);
            }

            assert cs in getCommitSeals(s'.adversary.messagesReceived);

            //         ||;
        }
        // assert cs in getCommitSeals(s'.adversary.messagesReceived);
    }    

    lemma lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper1_2(
        A: set<QbftMessage>,
        B: set<QbftMessage>,
        C: set<QbftMessage>,
        D: set<QbftMessage>,
        cs: Signature
    )
    requires A == B + C + D 
    requires B <= A 
    requires cs in getCommitSeals(A)
    requires cs !in getCommitSeals(B)
    ensures cs in getCommitSeals(C + D)
    {  }    

    lemma lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper2(
        s : InstrDSState,
        s': InstrDSState
    )
    requires validInstrDSState(s) 
    requires InstrDSNextSingle(s, s')
  
    ensures allMesssagesSentIncSentToItselfWithoutRecipient(s) <= allMesssagesSentIncSentToItselfWithoutRecipient(s');
    { }

    lemma lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper3(
        s : InstrDSState,
        s': InstrDSState,
        n : Address
    )
    requires validInstrDSState(s) 
    requires n in s.nodes
    requires InstrDSNextSingle(s, s')
    ensures getAllMessagesSentByTheNode(s, n) <= getAllMessagesSentByTheNode(s', n);
    {  }

    lemma lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper4(
        s:InstrDSState, 
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address,
        m: QbftMessage,
        sender: Address
    )
    requires validInstrDSState(s)  
    requires isInstrNodeHonest(s, node)
    requires InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node);
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s')
    requires
                var current := s.nodes[node];
                var next := s'.nodes[node];  
                var messagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
                var newMessagesReceived := current.nodeState.messagesReceived + messagesReceived;                     
                var newMessagesSentToItself :=  (next.nodeState.messagesReceived - newMessagesReceived - current.nodeState.messagesReceived);
                var allMessagesSentIncToItself  := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + newMessagesSentToItself;
                m in allMessagesSentIncToItself
    requires    m.Commit?
    requires    recoverSignature(m) == sender 
    requires    isInstrNodeHonest(s, sender)
    ensures m in allMesssagesSentIncSentToItselfWithoutRecipient(s')
    {
        lemmaSignedCommit();
        assert m in allMesssagesSentIncSentToItselfWithoutRecipient(s');
        assert m in getAllMessagesSentByTheNode(s', sender);
    }    

    lemma lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper5(
        s': InstrDSState,
        node: Address,
        sender: Address,
        cm: QbftMessage
    )
    requires isInstrNodeHonest(s', sender);
    requires isInstrNodeHonest(s', node);    
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s');
    requires cm.Commit?
    requires recoverSignature(cm) == sender 
    requires cm in s'.nodes[node].nodeState.messagesReceived
    ensures getSignedPayload(cm) in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',sender)); 
    {  }

    // 222 s 
    // TODO: Check names invariants that are used more like ind invariant. Perhaps we should not discriminate between the two anyway.
    // Then should we change the name of the lemma?
    lemma lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(
        s:InstrDSState, 
        s': InstrDSState
    )    
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeExcludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invCommitSealsInAdversaryMessagesReceivedAreSubsetOfCommitSealsSent(s)
    requires InstrDSNextSingle(s, s')
    ensures liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s')
    ensures indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s')
    ensures invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s')    
    ensures invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s')  
    ensures invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s')
    ensures invCommitSealsInAdversaryMessagesReceivedAreSubsetOfCommitSealsSent(s')
    {
        lemmaInvNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s, s');
        lemmaSignedHash();
        lemmaDigest();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedProposal();
        lemmaSignedRoundChange();
        lemmaGetSetOfSignedPayloads();

        
        // lemmaIndInvInstrNodeStateLifterToInstrDSState(s,s');
        assert invCommitSealsInAdversaryMessagesReceivedAreSubsetOfCommitSealsSent(s');

        if s != s'
        {
            var node :| isNodeThatTakesStep(s, s', node);

            var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node);  

  

            if isInstrNodeHonest(s,node)
            {
                var messagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
                
                assert s.nodes[node].nodeState.id == node;
                     
                forall b, cs, csAuthor |
                    && cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s'))
                    && csAuthor == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
                    && isInstrNodeHonest(s', csAuthor)
                ensures pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor) 
                {
                    // assume pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    if cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                    {
                        assert isInstrNodeHonest(s, csAuthor);
                        assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,b,csAuthor);
                        var   cm:QbftMessage, b', p :|  
                            && cm in getAllMessagesSentByTheNode(s, csAuthor)
                            && p in s.nodes[csAuthor].proposalsAccepted
                            && p.Proposal?
                            && p.proposedBlock == b'
                            && areBlocksTheSameExceptForTheCommitSeals(b',b)
                            && cm.Commit?
                            && cm.commitPayload.unsignedPayload.height == b.header.height
                            && cm.commitPayload.unsignedPayload.round == b.header.roundNumber
                            && cm.commitPayload.unsignedPayload.digest == digest(b'); 
                        lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper3(s, s', csAuthor);
                        assert cm in getAllMessagesSentByTheNode(s', csAuthor); 
                        assert p in s'.nodes[csAuthor].proposalsAccepted;                      
                        assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    }
                    else
                    {
                        var current := s.nodes[node];
                        var next := s'.nodes[node];   
                        var newMessagesReceived := current.nodeState.messagesReceived + messagesReceived;                     
                        var newMessagesSentToItself :=  (next.nodeState.messagesReceived - newMessagesReceived - current.nodeState.messagesReceived);
                        assert next.messagesSentToItself == current.messagesSentToItself + newMessagesSentToItself;
                        lemmaAllMesssagesSentIncSentToItselfWithoutRecipientEqualOldPlusAllMessagesSentAtCurrentHonestStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
                        assert allMesssagesSentIncSentToItselfWithoutRecipient(s') == 
                                allMesssagesSentIncSentToItselfWithoutRecipient(s) +
                                fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + 
                                newMessagesSentToItself;

                        lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper2(s, s');

                        assert allMesssagesSentIncSentToItselfWithoutRecipient(s) <= allMesssagesSentIncSentToItselfWithoutRecipient(s');

                        lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper1_2(
                            allMesssagesSentIncSentToItselfWithoutRecipient(s'),
                            allMesssagesSentIncSentToItselfWithoutRecipient(s),
                            fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)),
                            newMessagesSentToItself,
                            cs
                        );

                        // assert cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + 
                        //         newMessagesSentToItself);

                        var allMessagesSentIncToItself  := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + newMessagesSentToItself;

                        assert cs in  getCommitSeals(allMessagesSentIncToItself);

                        var m :| 
                                    && m in allMessagesSentIncToItself
                                    && (
                                        || (
                                            && m.Commit?
                                            && m.commitPayload.unsignedPayload.commitSeal == cs
                                        )
                                        || (
                                            && m.NewBlock?
                                            && cs in m.block.header.commitSeals
                                        )
                                    );   

                        if m.Commit?
                        {
                            assert validInstrState(s.nodes[node]);
                            assert indInvInstrNodeStateTypes(s.nodes[node]);
                            assert InstrNodeNextSingleStep(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes);
                            assert m in allMessagesSentIncToItself && isMsgWithSignedPayload(m);
                            lemmaAllSentAreSignedByTheNodeExNotForAll(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes, m);
                            assert recoverSignature(m) == s.nodes[node].nodeState.id;
                            assert recoverSignature(m) == node;
                            assert node == csAuthor;
                            // assert m in s'.nodes[node].nodeState.messagesReceived;
                            // lemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s, s');
                            lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper4(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node, m, csAuthor);
                            assert m in getAllMessagesSentByTheNode(s', csAuthor);
                            assert m in getAllMessagesSentByInsrNodeState(s'.nodes[node]);
                            var pm :|    
                                && pm in s'.nodes[node].proposalsAccepted
                                &&  var cuPayload := m.commitPayload.unsignedPayload;
                                    var puPayload := pm.proposalPayload.unsignedPayload;
                                &&  puPayload.height == cuPayload.height
                                &&  puPayload.round == cuPayload.round
                                &&  digest(pm.proposedBlock) == cuPayload.digest
                                &&  signHash(hashBlockForCommitSeal(pm.proposedBlock), s.nodes[node].nodeState.id) == cuPayload.commitSeal;

                            var b' := pm.proposedBlock;
                            assert hashBlockForCommitSeal(b') == hashBlockForCommitSeal(b);
                            assert areBlocksTheSameExceptForTheCommitSeals(b',b);
                            assert pm.proposalPayload.unsignedPayload.round == b'.header.roundNumber;

                            assert m in getAllMessagesSentByTheNode(s', csAuthor); 
                            assert pm in s'.nodes[csAuthor].proposalsAccepted;
                            assert pm.proposedBlock == b';
                            assert areBlocksTheSameExceptForTheCommitSeals(b',b);
                            assert m.commitPayload.unsignedPayload.round == b.header.roundNumber;
                            assert m.commitPayload.unsignedPayload.digest == digest(b'); 
                        
                            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                        }   
                        else
                        {
                            lemmaAllNewBlockSentIncItselfThereIsACommitInReceived(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes);
                            assert exists cm ::  && cm in s'.nodes[node].nodeState.messagesReceived
                                                && cm.Commit?
                                                && var uPayload := cm.commitPayload.unsignedPayload;
                                                && uPayload.commitSeal == cs
                                                && uPayload.round == m.block.header.roundNumber
                                                && uPayload.height == m.block.header.height
                                                 && recoverSignedCommitAuthor(cm.commitPayload) == csAuthor;  


                            var cm :|   && cm in s'.nodes[node].nodeState.messagesReceived
                                        && cm.Commit?
                                        && var uPayload := cm.commitPayload.unsignedPayload;
                                        && uPayload.commitSeal == cs
                                        && uPayload.round == m.block.header.roundNumber
                                        && uPayload.height == m.block.header.height
                                        && recoverSignedCommitAuthor(cm.commitPayload) == csAuthor;   



                            // lemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s, s');  
                            assert isInstrNodeHonest(s', csAuthor);
                            assert isInstrNodeHonest(s', node);
                            assert recoverSignature(cm) == csAuthor;   

                            assert invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s);
                            assert invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s');

                            lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper5(
                                // s,
                                s',
                                node,
                                csAuthor,
                                cm
                                );                            

                            // var scm :=  getSignedPayload(cm);

                            // assert scm in  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].nodeState.messagesReceived), csAuthor);

                            // lemmaInvMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodesToNotForAll(
                            //     s',
                            //     node,
                            //     csAuthor,
                            //     scm
                            // );
                            assert getSignedPayload(cm) in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',csAuthor)); 

                            lemmaSignedCommitPayloadInSetOfSignedPayloadsImplyNonSignedIsInSetOfNonSigned(cm, getAllMessagesSentByTheNode(s',csAuthor));

                            assert cm in getAllMessagesSentByTheNode(s',csAuthor);    

                    //         assert getSignedPayload(cm) in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',csAuthor));    

                            lemmaIndInvInstrNodeStateLifterToInstrDSState(s,s');
                            assert invInstrNodeStateCommitSentOnlyIfAcceptedProposal(s'.nodes[csAuthor]);
                            assert
                            exists pm ::    
                                && pm in s'.nodes[csAuthor].proposalsAccepted
                                &&  var cuPayload := cm.commitPayload.unsignedPayload;
                                    var puPayload := pm.proposalPayload.unsignedPayload;
                                &&  puPayload.height == cuPayload.height
                                &&  puPayload.round == cuPayload.round
                                &&  digest(pm.proposedBlock) == cuPayload.digest
                                &&  signHash(hashBlockForCommitSeal(pm.proposedBlock), s'.nodes[csAuthor].nodeState.id) == cuPayload.commitSeal;

                            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    //         // if cm in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[csAuthor].messagesSent)
                    //         // {
                    //         //     // assert
                    //         //     // exists b', p ::    
                    //         //     //     && cm in getAllMessagesSentByTheNode(s', csAuthor)
                    //         //     //     && p in s'.nodes[csAuthor].proposalsAccepted
                    //         //     //     && p.proposedBlock == b'
                    //         //     //     && areBlocksTheSameExceptForTheCommitSeals(b',b)
                    //         //     //     && cm.commitPayload.unsignedPayload.digest == digest(b');                                 
                    //         //     assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    //         // }   
                    //         // else
                    //         // {
                    //         //     // assert cm in s'.nodes[csAuthor].messagesSentToItself;
                    //         //     // assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    //         // }                     

                        }                                                                                          
                    }
                    
                }               
                assert invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s');
            }
            else
            {
                lemmaAdversaryNextDoesNotChangeMessagesSentByHonestNodesExcludingSentToItself(s,s');
                assert s.adversary.messagesReceived <= allMessagesSentWithoutRecipient(s.environment);
                assert s'.adversary.messagesReceived <= allMessagesSentWithoutRecipient(s'.environment);

                forall b, cs, csAuthor |
                    && cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s'))
                    && csAuthor == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
                    && isInstrNodeHonest(s', csAuthor)
                ensures pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor)
                {
                    assert isInstrNodeHonest(s,csAuthor);
                    assert isInstrNodeHonest(s',csAuthor);

                    lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper0(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node, cs);

                    assert || cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                           || cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));

                    if cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                    {
                        assert   pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s, b,csAuthor); 
                        
                        var   cm:QbftMessage, b', p :|  
                            && cm in getAllMessagesSentByTheNode(s, csAuthor)
                            && p in s.nodes[csAuthor].proposalsAccepted
                            && p.Proposal?
                            && p.proposedBlock == b'
                            && areBlocksTheSameExceptForTheCommitSeals(b',b)
                            && cm.Commit?
                            && cm.commitPayload.unsignedPayload.height == b.header.height
                            && cm.commitPayload.unsignedPayload.round == b.header.roundNumber
                            && cm.commitPayload.unsignedPayload.digest == digest(b');

                        assert   pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s', b,csAuthor); 
                    }
                    else
                    {    
                        assert cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));      
                        lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper1(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
                        assert cs in getCommitSeals(s'.adversary.messagesReceived);          
                        assert s'.adversary.messagesReceived <= fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent);
                        assert cs in  getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent));
                        assert   pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s, b,csAuthor); 
                        var   cm:QbftMessage, b', p :|  
                                && cm in getAllMessagesSentByTheNode(s, csAuthor)
                                && p in s.nodes[csAuthor].proposalsAccepted
                                && p.Proposal?
                                && p.proposedBlock == b'
                                && areBlocksTheSameExceptForTheCommitSeals(b',b)
                                && cm.Commit?
                                && cm.commitPayload.unsignedPayload.height == b.header.height
                                && cm.commitPayload.unsignedPayload.round == b.header.roundNumber
                                && cm.commitPayload.unsignedPayload.digest == digest(b');                        
                        assert   pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s', b,csAuthor);  
                    } 
                }

                assert invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s');
            }
        }
        else
        {
            assert invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s');     
        }

             
    }  

    // 1.5s 3.2.0
    lemma lemmaTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestHelper(
        s:InstrDSState,
        n: Address
    )
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires isInstrNodeHonest(s, n)
    ensures invInstrNodeStateNoConflictingPreapresSent(s.nodes[n])
    {

    }

    lemma lemmaGetPrepareMessageCorrespondingToSignedPayload(
        s: InstrDSState,
        srcp: SignedPayload,
        n: Address
    )
    returns (pm: QbftMessage)
    requires isInstrNodeHonest(s, n) 
    requires srcp.SignedPreparePayload? 
    requires srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,n)), n) 
    requires invIfPreparePaylodSentThenPrepareSent(s)
    ensures && pm in getAllMessagesSentByTheNode(s,n)
                && pm.Prepare?
                && pm.preparePayload == srcp.signedPreparePayload;
    {
        pm :|   && pm in getAllMessagesSentByTheNode(s,n)
                && pm.Prepare?
                && pm.preparePayload == srcp.signedPreparePayload;
    }    

    // 5s 3.2.0
    lemma lemmaInvTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigest(
        s:InstrDSState,
        h: nat,
        r: nat,
        QofP1: set<QbftMessage>,
        QofP2: set<QbftMessage>,
        d1: Hash,
        d2: Hash,
        n1: Address,
        n2: Address            
    )
    requires validInstrDSState(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)    
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invConstantFields(s)
    ensures invTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigest(s, h, r, QofP1, QofP2, d1, d2, n1, n2)
    {
        if  && isInstrNodeHonest(s,n1)
            && isInstrNodeHonest(s,n2)
            && |s.nodes[n1].nodeState.blockchain| >= h
            && |s.nodes[n2].nodeState.blockchain| >= h
            && pBlockchainConsistencyUpToHeight(s, h)   
            && isQuorumOfPrepares(h,r,d1,QofP1,s.nodes[n1].nodeState.messagesReceived, s.nodes[n1].nodeState.blockchain)
            && isQuorumOfPrepares(h,r,d2,QofP2,s.nodes[n2].nodeState.messagesReceived, s.nodes[n2].nodeState.blockchain)  
        {        
        // lemmaInvTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestForAll(s);
        lemmaValidatorsAreTheSameOfTheGenesisBlock();
        lemmaSignedPrepare();
        lemmaGetSetOfSignedPayloads();  
        lemmaPBlockchainConsistencyUpToHeightImpliesConsistencyForHonestBlockchainOfThatHeight(
            s, 
            h, 
            n1,
            n2
        );    
        var bc1 := s.nodes[n1].nodeState.blockchain[..h];
        var bc2 := s.nodes[n2].nodeState.blockchain[..h];     
        lemmaOnFromBlockchainToRawBlockchainIImpliesValidatorsEquality(bc1, bc2);   

        var senders1 := getSetOfSenders(QofP1);
        assert forall s | s in senders1 :: 
            exists m :: && m in QofP1 && recoverSignature(m) == s;

        var senders2 := getSetOfSenders(QofP2);
        assert forall s | s in senders2 :: 
            exists m :: && m in QofP2 && recoverSignature(m) == s;  

        lemmaSizeOfSetOfConsistentPreparesMatchesTheSizeOfTheSetOfAssociatedSignatures(QofP1, h,r,d1);
        assert |senders1| ==  |QofP1|; 

        lemmaSizeOfSetOfConsistentPreparesMatchesTheSizeOfTheSetOfAssociatedSignatures(QofP2, h,r,d2);
        assert |senders2| ==  |QofP2|;  

        assert validators(bc1) == validators(bc2);
        assert forall a | a in senders1 :: a in validators(bc1);                   
        assert forall a | a in senders2 :: a in validators(bc2);                   

        var vals := validators(s.nodes[n1].nodeState.blockchain);
        assert |s.adversary.byz| <= f(|validators(bc1)|);

        assert seqToSet(validators([s.configuration.genesisBlock])) <= s.nodes.Keys;
        assert senders1 <= s.nodes.Keys;
        assert vals == validators([s.configuration.genesisBlock]);
        assert isUniqueSequence(vals);
        lUniqueSeq(vals);

        assert |seqToSet(vals)| == |vals|;

        // assert s.adversary.byz <= s.nodes.Keys;

        lemmaQuorumIntersection(seqToSet(vals), s.adversary.byz, senders1, senders2);

        var hInInt :| hInInt in (senders1 * senders2 * (seqToSet(vals) - s.adversary.byz));
        assert isInstrNodeHonest(s,hInInt);

        var m1:QbftMessage :|  && m1 in s.nodes[n1].nodeState.messagesReceived
                                        && m1.Prepare?
                                        && recoverSignature(m1) == hInInt
                                        && var uPayload := m1.preparePayload.unsignedPayload;
                                        && uPayload.height == h
                                        && uPayload.round == r 
                                        && uPayload.digest == d1;

        var m2:QbftMessage :|  && m2 in s.nodes[n2].nodeState.messagesReceived
                                        && m2.Prepare?
                                        && recoverSignature(m2) == hInInt
                                        && var uPayload := m2.preparePayload.unsignedPayload;
                                        && uPayload.height == h
                                        && uPayload.round == r 
                                        && uPayload.digest == d2;  

        var spp1 := SignedPreparePayload(m1.preparePayload);
        lemmaOnFilterSignedPayloadsByAuthorOfGetSetOfSignedPayloadsOfASetIncludesSignedPreparePyloadOfMemberOfTheSet(
            s.nodes[n1].nodeState.messagesReceived,
            m1,
            spp1,
            hInInt
        );

        var pm1 := lemmaGetPrepareMessageCorrespondingToSignedPayload(s, spp1, hInInt);
        assert pm1.Prepare? && pm1 in getAllMessagesSentByTheNode(s, hInInt) && pm1.preparePayload == m1.preparePayload;

        var spp2 := SignedPreparePayload(m2.preparePayload);
        lemmaOnFilterSignedPayloadsByAuthorOfGetSetOfSignedPayloadsOfASetIncludesSignedPreparePyloadOfMemberOfTheSet(
            s.nodes[n2].nodeState.messagesReceived,
            m2,
            spp2,
            hInInt
        );
        var pm2 := lemmaGetPrepareMessageCorrespondingToSignedPayload(s, spp2, hInInt);
        assert pm2.Prepare? && pm2 in getAllMessagesSentByTheNode(s, hInInt) && pm2.preparePayload == m2.preparePayload;                

        lemmaTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestHelper(s, hInInt);

        assert d1 == d2;
        }
    
    }   
    
    // 1.5s 3.2.0
    lemma lemmaInvTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestForAll(
        s:InstrDSState             
    )
    requires validInstrDSState(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)    
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invConstantFields(s)
    ensures invTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestForAll(s)
    {
        axiomRawValidatorsNeverChange();
        lemmaSignedPrepare();
        lemmaGetSetOfSignedPayloads();        

        

        forall h,r, QofP1, QofP2, d1, d2,n1,n2 |
            && isInstrNodeHonest(s,n1)
            && isInstrNodeHonest(s,n2)
            && |s.nodes[n1].nodeState.blockchain| >= h
            && |s.nodes[n2].nodeState.blockchain| >= h
            && pBlockchainConsistencyUpToHeight(s, h)   
            && isQuorumOfPrepares(h,r,d1,QofP1,s.nodes[n1].nodeState.messagesReceived, s.nodes[n1].nodeState.blockchain)
            && isQuorumOfPrepares(h,r,d2,QofP2,s.nodes[n2].nodeState.messagesReceived, s.nodes[n2].nodeState.blockchain)    

        ensures
            
            d1 == d2   
        {
            lemmaInvTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigest(
                s,
                h,
                r,
                QofP1,
                QofP2,
                d1,
                d2,
                n1,
                n2  
            );
        }     
    }
    
    // 2s 3.2.0
    lemma lemmaInvTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigest(
        s:InstrDSState,
        n1: Address,
        n2: Address,
        m1: QbftMessage,
        m2: QbftMessage,
        h: nat,
        r: nat           
    )
    requires validInstrDSState(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)    
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)    
    requires invConstantFields(s)
    ensures invTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigest(s, n1, n2, m1, m2, h, r)   
    {
        if
            && isInstrNodeHonest(s,n1)  
            && isInstrNodeHonest(s,n2)
            && pBlockchainConsistencyUpToHeight(s, h)
            && m1 in getAllMessagesSentByTheNode(s, n1)
            && m2 in getAllMessagesSentByTheNode(s, n2)
            && m1.Commit?
            && m2.Commit?
            &&  var uPayload1 := m1.commitPayload.unsignedPayload;
                var uPayload2 := m2.commitPayload.unsignedPayload;
            && uPayload1.height == uPayload2.height == h 
            && uPayload1.round == uPayload2.round == r  
        {
            // lemmaInvTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestForAll(s);
            // lemmaPBlockchainConsistencyUpToHeightImpliesConsistencyForHonestBlockchainOfThatHeight(
            //     s, 
            //     h, 
            //     n1,
            //     n2
            // );    
            // var bc1 := s.nodes[n1].nodeState.blockchain[..h];
            // var bc2 := s.nodes[n2].nodeState.blockchain[..h];     
            // lemmaOnFromBlockchainToRawBlockchainIImpliesValidatorsEquality(bc1, bc2);

            var uPayload1 := m1.commitPayload.unsignedPayload;
            var uPayload2 := m2.commitPayload.unsignedPayload;

            // assert s.nodes[n1].nodeState.blockchain[..h] == s.nodes[n2].nodeState.blockchain[..h];
            // var blockchain := s.nodes[n1].nodeState.blockchain[..h];
            // // assert recoverSignature(m1) == n1;

            assert invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(s.nodes[n1]);
            assert invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(s.nodes[n2]);

            var QofP1 :| 
                && QofP1 <= validPreparesForHeightRoundAndDigest(
                            s.nodes[n1].nodeState.messagesReceived,
                            h,
                            r,
                            uPayload1.digest,
                            validators(s.nodes[n1].nodeState.blockchain[..h]))
                && |QofP1| >= quorum(|validators(s.nodes[n1].nodeState.blockchain[..h])|); 

            // assert isQuorumOfPrepares(h,r,uPayload1.digest,QofP1,s.nodes[n1].nodeState.messagesReceived, s.nodes[n1].nodeState.blockchain);    
            // assert isQuorumOfPrepares(h,r,uPayload1.digest,QofP1,s.nodes[n1].nodeState.messagesReceived, s.nodes[n1].nodeState.blockchain);    

            var QofP2 :| 
                && QofP2 <= validPreparesForHeightRoundAndDigest(
                            s.nodes[n2].nodeState.messagesReceived,
                            h,
                            r,
                            uPayload2.digest,
                            validators(s.nodes[n2].nodeState.blockchain[..h]))
                && |QofP2| >= quorum(|validators(s.nodes[n2].nodeState.blockchain[..h])|); 

            lemmaInvTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigest(s,h,r,QofP1,QofP2,uPayload1.digest, uPayload2.digest, n1,n2);
            
            assert uPayload1.digest == uPayload2.digest;
        }
    }    
       
    // 2s
    lemma lemmaInvTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigestForAll(
        s:InstrDSState             
    )
    requires validInstrDSState(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)    
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)      
    requires invConstantFields(s)
    ensures intTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigestForAll(s)   
    {
        
        // return
        // lemmaInvTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestForAll(s);
        forall n1:Address, n2:Address, m1:QbftMessage, m2:QbftMessage, h:nat, r:nat |
            pMessagesAreCommitMessagesForSameRoundSendByTwoHonestValidators(s,n1,n2,m1,m2,h,r)
        ensures m1.commitPayload.unsignedPayload.digest == m2.commitPayload.unsignedPayload.digest
        {
            lemmaInvTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigest(s,n1,n2,m1,m2,h,r);
        }

    }

    // 2s 3.2.0
    lemma lemmaOnSizeOfSetOfCommitSeals(
        h: Hash,
        css: set<Signature>
    )
    ensures |getCommitSealAuthors(h,css)| == |css|
    {
        lemmaSignedHash();

        if css == {}
        {

        }
        else
        {
            var e :| e in css;
            var subCss := css - {e};

            lemmaOnSizeOfSetOfCommitSeals(h,subCss);

            // assert forall e' | e' in subCss :: e' != e;

            assert getCommitSealAuthors(h,css) == getCommitSealAuthors(h,subCss) + {recoverSignedHashAuthor(h,e)};
        }
    }

    // 2s 3.2.0
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

    // 14s 3.2.0
    lemma lemmaInvTwoValidQuorumOfCommitSealsForSameRoundAreForTheSameBlockExceptForCommitSealsNotForAll(
        s:InstrDSState,
        b1: Block, 
        b2:Block,
        n1: Address,
        n2: Address, 
        h:nat            
    )
    requires validInstrDSState(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)     
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s) 
    ensures invTwoValidQuorumOfCommitSealsForSameRoundAreForTheSameBlockExceptForCommitSealsNotForAll(s, b1, b2, n1, n2, h) 
    {
        if  && isInstrNodeHonest(s,n1)
            && isInstrNodeHonest(s,n2)
            && |s.nodes[n1].nodeState.blockchain| >= h
            && |s.nodes[n2].nodeState.blockchain| >= h
            && pBlockchainConsistencyUpToHeight(s, h)
            && b1.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && b2.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b1)
            && ValidNewBlock(s.nodes[n2].nodeState.blockchain[..h],b2)
            && b1.header.roundNumber == b2.header.roundNumber
        {
            lemmaInvTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestForAll(s);
            lemmaInvTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigestForAll(s);
            lemmaValidatorsAreTheSameOfTheGenesisBlock();
            lemmaDigest();
            assert b1.header.height == h;
            // lemmaPBlockchainConsistencyUpToHeightImpliesConsistencyForHonestBlockchainOfThatHeight(
            //     s, 
            //     h, 
            //     n1,
            //     n2
            // );  

            // lemmaOnFromBlockchainToRawBlockchainIImpliesValidatorsEquality(
            //     s.nodes[n1].nodeState.blockchain[..h],
            //     s.nodes[n2].nodeState.blockchain[..h]
            // );

            var blockchain := s.nodes[n1].nodeState.blockchain[..h];

            var block1 := b1;
            var block2 := b2;

            var bhash1 := hashBlockForCommitSeal(block1);
            var bhash2 := hashBlockForCommitSeal(block2);

            var css1 := block1.header.commitSeals;
            var css2 := block2.header.commitSeals;

            var cssAuth1 := getCommitSealAuthors(bhash1, css1);
            lemmaOnSizeOfSetOfCommitSeals(bhash1, css1);

            var cssAuth2 := getCommitSealAuthors(bhash2, css2);
            lemmaOnSizeOfSetOfCommitSeals(bhash2, css2);

            var vals := validators(blockchain);
                lUniqueSeq(vals);

            assert |cssAuth1| >= quorum(|vals|);
            assert |cssAuth2| >= quorum(|vals|);

            assert vals == validators([s.configuration.genesisBlock]);

            assert |s.adversary.byz| <= f(|vals|);

            lemmaThereExistsAnHonestInQuorum(seqToSet(vals), s.adversary.byz, cssAuth1);
            lemmaThereExistsAnHonestInQuorum(seqToSet(vals), s.adversary.byz, cssAuth2);

            var hSender1 :|
                && hSender1 in cssAuth1
                && isInstrNodeHonest(s, hSender1);

            var hSender2 :|
                && hSender2 in cssAuth2
                && isInstrNodeHonest(s, hSender2);  

            var cs1 :|  && cs1 in css1
                        && recoverSignedHashAuthor(bhash1, cs1) == hSender1;  

            var cs2 :|  && cs2 in css2
                        && recoverSignedHashAuthor(bhash2, cs2) == hSender2;                                                  

            assert cs1 in getCommitSeals((allMesssagesSentIncSentToItselfWithoutRecipient(s)));
            assert isInstrNodeHonest(s, hSender1);

            assert cs2 in getCommitSeals((allMesssagesSentIncSentToItselfWithoutRecipient(s)));
            assert isInstrNodeHonest(s, hSender2);   

            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block1,hSender1);
            

            var cm1:QbftMessage, b1', p1 :|    
                && cm1 in getAllMessagesSentByTheNode(s, hSender1)
                && p1 in s.nodes[hSender1].proposalsAccepted
                && p1.proposedBlock == b1'
                && areBlocksTheSameExceptForTheCommitSeals(b1',block1)
                && cm1.Commit?
                && cm1.commitPayload.unsignedPayload.height == block1.header.height
                && cm1.commitPayload.unsignedPayload.round == block1.header.roundNumber
                && cm1.commitPayload.unsignedPayload.digest == digest(b1');  

            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block2,hSender2);                       

            var cm2:QbftMessage, b2', p2 :|    
                && cm2 in getAllMessagesSentByTheNode(s, hSender2)
                && p2 in s.nodes[hSender2].proposalsAccepted
                && p2.proposedBlock == b2'
                && areBlocksTheSameExceptForTheCommitSeals(b2',block2)
                && cm2.Commit?
                && cm2.commitPayload.unsignedPayload.height == block2.header.height
                && cm2.commitPayload.unsignedPayload.round == block2.header.roundNumber
                && cm2.commitPayload.unsignedPayload.digest == digest(b2'); 


            assert block1.header.height == h == block2.header.height;
            assert cm1.commitPayload.unsignedPayload.height == cm2.commitPayload.unsignedPayload.height;
            assert cm1.commitPayload.unsignedPayload.round == cm2.commitPayload.unsignedPayload.round;

            assert
            && isInstrNodeHonest(s,hSender1)
            && isInstrNodeHonest(s,hSender2)
            && cm1 in getAllMessagesSentByTheNode(s, hSender1)
            && cm2 in getAllMessagesSentByTheNode(s, hSender2)
            && cm1.Commit?
            && cm2.Commit?
            &&  var uPayload1 := cm1.commitPayload.unsignedPayload;
                var uPayload2 := cm2.commitPayload.unsignedPayload;
            && uPayload1.height == uPayload2.height == block1.header.height 
            && uPayload1.round == uPayload2.round == block1.header.roundNumber;


            assert cm1.commitPayload.unsignedPayload.digest == cm2.commitPayload.unsignedPayload.digest by
            {
                lemmaInvTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigest(s, hSender1, hSender2, cm1, cm2, block1.header.height, block1.header.roundNumber);
            }

            assert b1' == b2';

            // lemmaQuorumIntersection(seqToSet(vals), s.adversary.byz, cssAuth1, cssAuth2);

            // var hInInt :| hInInt in (senders1 * senders2 * (seqToSet(vals) - s.adversary.byz));
            // assert isInstrNodeHonest(s,hInInt);

            assert areBlocksTheSameExceptForTheCommitSeals(b1, b2);
        }
    }

    lemma lemmaValidBlockAndBlockIncludedInValidPropsosalForNextRoundAreTheSameExceptForCommitSealsAndRoundHelper(
        s: InstrDSState,
        b: Block,
        cs: Signature,
        a: Address
    )
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires    && cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                && isInstrNodeHonest(s, a)
                && a == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
    ensures pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s, b, a)
    {

    }

    // 2s 3.2.0
    lemma lemmaGetCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(
        s: InstrDSState, b:Block, cs:Signature,csAuthor: Address
    )
    returns (cm:QbftMessage, b':Block, p:QbftMessage)
    requires isInstrNodeHonest(s, csAuthor)
    requires pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s, b, csAuthor)
    ensures 
            && cm in getAllMessagesSentByTheNode(s, csAuthor)
            && p.Proposal?
            && p in s.nodes[csAuthor].proposalsAccepted
            && p.proposedBlock == b'
            && areBlocksTheSameExceptForTheCommitSeals(b',b)
            && cm.Commit?
            && cm.commitPayload.unsignedPayload.height == b.header.height
            && cm.commitPayload.unsignedPayload.round == b.header.roundNumber
            && cm.commitPayload.unsignedPayload.digest == digest(b')     
    {
        cm, b', p :|
            && cm in getAllMessagesSentByTheNode(s, csAuthor)
            && p.Proposal?
            && p in s.nodes[csAuthor].proposalsAccepted
            && p.proposedBlock == b'
            && areBlocksTheSameExceptForTheCommitSeals(b',b)
            && cm.Commit?
            && cm.commitPayload.unsignedPayload.height == b.header.height
            && cm.commitPayload.unsignedPayload.round == b.header.roundNumber
            && cm.commitPayload.unsignedPayload.digest == digest(b');
    }    

    lemma lemmaValidBlockAndBlockIncludedInValidPropsosalForNextRoundAreTheSameExceptForCommitSealsAndRoundHelper1(
        s: InstrDSState,
        n: Address,
        cm: QbftMessage,
        rm: QbftMessage
    )
    requires isInstrNodeHonest(s, n)
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires 
                var messagesSent := getAllMessagesSentByInsrNodeState(s.nodes[n]);
                && cm in messagesSent
                && cm.Commit?
                && rm in messagesSent
                && rm.RoundChange?
                &&
                var urPayload := rm.roundChangePayload.unsignedPayload;
                var ucPayload := cm.commitPayload.unsignedPayload;
                && urPayload.height == ucPayload.height
                && urPayload.round == ucPayload.round + 1
    ensures 
                var urPayload := rm.roundChangePayload.unsignedPayload;
                var ucPayload := cm.commitPayload.unsignedPayload;
                && urPayload.preparedRound.Optional?
                && urPayload.preparedValue.Optional?
                && urPayload.preparedRound.value == ucPayload.round
                && urPayload.preparedValue.value == ucPayload.digest    
    {}

    lemma lemmaValidBlockAndBlockIncludedInValidPropsosalForNextRoundAreTheSameExceptForCommitSealsAndRoundHelper2(
        s: InstrDSState,
        m: SignedPayload,
        n: Address
    )
    requires isInstrNodeHonest(s, n)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n)
    ensures  m in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, n)), n);
    ensures m in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, n));
    {

    }
    
    // 42s 3.2.0
    lemma lemmaInvValidBlockAndBlockIncludedInValidPropsosalJustificationForNextRoundAreTheSameExceptForCommitSeals(
        s: InstrDSState,
        b: Block, 
        h:nat, 
        n1: Address, 
        rcs: set<SignedRoundChange>,
        ps: set<SignedPrepare>, 
        b': Block,
        rl: Address,
        vb: Block -> bool
    )
    requires validInstrDSState(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s)
    ensures invValidBlockAndBlockIncludedInValidPropsosalJustificationForNextRoundAreTheSameExceptForCommitSeals(s, b, h, n1, rcs, ps, b', rl, vb)            
    {
        if  && isInstrNodeHonest(s,n1)
            // && isInstrNodeHonest(s,n2)
            // && s.nodes[n1].nodeState.blockchain <= s.nodes[n2].nodeState.blockchain
            && |s.nodes[n1].nodeState.blockchain| >= h
            && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b)
            && rcs <= extractSignedRoundChangesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ps <= extractSignedPreparesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && isProposalJustification(
                rcs,
                ps,
                {b'},
                h,
                b.header.roundNumber+1,
                b',
                vb,
                rl,
                validators(s.nodes[n1].nodeState.blockchain[..h])
            )   
        {
            // lemmaInvTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestForAll(s);
            // lemmaInvTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigestForAll(s);
            axiomRawValidatorsNeverChange();
            lemmaDigest();
            lemmaSignedRoundChange();
            lemmaSignedPrepare();
            lemmaGetSetOfSignedPayloads();


            var V := validators(s.nodes[n1].nodeState.blockchain[..h]);
            assert V == validators([s.configuration.genesisBlock]);
            assert isUniqueSequence(V);
            var Vset := seqToSet(V);
            var block1 := b;
            var bhash1 := hashBlockForCommitSeal(block1);
            var css1 := block1.header.commitSeals;
            var cssAuth1 := getCommitSealAuthors(bhash1, css1);
            lemmaOnSizeOfSetOfCommitSeals(bhash1, css1);
            assert |cssAuth1| == |css1|;
            var rcSenders := getSetOfRoundChangeSenders(rcs);
            assert |rcSenders| >= quorum(|V|);
            assert |css1| >= quorum(|V|);
            lUniqueSeq(V);
            assert |Vset| == |V|;
            lemmaQuorumIntersection(Vset, s.adversary.byz, rcSenders, cssAuth1);
            var hInInt :| hInInt in (rcSenders * cssAuth1 * (Vset - s.adversary.byz));
            assert isInstrNodeHonest(s,hInInt);
            assert hInInt in rcSenders && hInInt in cssAuth1;
            // var hrc :| hrc in rcs && recoverSignedRoundChangeAuthor(hrc) == hInInt;
            // var hrcPayload := hrc.unsignedPayload;
            // assert hrcPayload.round == bm.block.header.roundNumber+1;
            var cs1 :|  && cs1 in css1
                    && recoverSignedHashAuthor(bhash1, cs1) == hInInt; 
            assert cs1 in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s)); 
            assert isInstrNodeHonest(s, hInInt);
            // assert hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(block1), cs1);
            // var b1 :| hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(b1), cs1);
            

            // assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeStateTypes)(s);
            // assert invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s);
            // assert  && cs1 in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            //         && isInstrNodeHonest(s, hInInt)
            //         && hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(block1), cs1);
            // // deducePHelper(s,block1,cs1,hInInt);
            lemmaValidBlockAndBlockIncludedInValidPropsosalForNextRoundAreTheSameExceptForCommitSealsAndRoundHelper(s, block1, cs1, hInInt);
            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block1,hInInt);

            var cm1, b1', p1 := lemmaGetCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block1,cs1,hInInt);


            // // // // assert hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
            assert    
                && cm1 in getAllMessagesSentByTheNode(s, hInInt)
                && p1 in s.nodes[hInInt].proposalsAccepted
                && p1.Proposal?
                && p1.proposedBlock == b1'
                && areBlocksTheSameExceptForTheCommitSeals(p1.proposedBlock,block1)
                && cm1.Commit?
                && cm1.commitPayload.unsignedPayload.height == block1.header.height
                && cm1.commitPayload.unsignedPayload.round == block1.header.roundNumber
                && cm1.commitPayload.unsignedPayload.digest == digest(b1');   

            var hsrc :| hsrc in rcs && recoverSignedRoundChangeAuthor(hsrc) == hInInt;
            var hsrcPayload := hsrc.unsignedPayload;

            lemmaExtractSignedRoundChangeEx(allMesssagesSentIncSentToItselfWithoutRecipient(s), hsrc, hInInt);
            assert SignedRoundChangePayload(hsrc) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), hInInt);
            // assert SignedRoundChangePayload(hsrc) in getSetOfSignedPayloads(allMessagesSentBy(allMessagesSentWithoutRecipient(s.environment),hInInt));
            // assert SignedRoundChangePayload(hsrc) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hInInt)),hInInt);
            // assert SignedRoundChangePayload(hsrc) in getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt].messagesSent));
            // // var hrc :| hrc in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt].messagesSent) &&
            // //             hrc.RoundChange? &&
            // //             hrc.roundChangePayload == hsrc;

            // // // assert hrc in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt].messagesSent);

            assert SignedRoundChangePayload(hsrc) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,hInInt)), hInInt);

            // var hrc := ldklfjaklfja(hsrc, getAllMessagesSentByTheNode(s,hInInt), hInInt);

            var hrc :|  hrc in getAllMessagesSentByTheNode(s, hInInt) &&  hrc.RoundChange? && hrc.roundChangePayload == hsrc;
            // assert false;
            // assert hrc in getAllMessagesSentByTheNode(s, hInInt);

            // assert invInstrNodeStateIfCommitAndNextRoundChangeThenTheyMatch(s.nodes[hInInt]);

            // var ms := fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt].messagesSent) + s.nodes[hInInt].messagesSentToItself;
            // assert hrc in ms;
            // assert 
            var ucPayload := cm1.commitPayload.unsignedPayload;
            assert hsrcPayload.height == ucPayload.height;
            assert hsrcPayload.round == ucPayload.round + 1;

            lemmaValidBlockAndBlockIncludedInValidPropsosalForNextRoundAreTheSameExceptForCommitSealsAndRoundHelper1(s, hInInt, cm1, hrc);

            assert hsrcPayload.preparedRound.Optional?;
            assert hsrcPayload.preparedValue.Optional?;  
            assert hsrcPayload.preparedRound.value == ucPayload.round;    
            assert hsrcPayload.preparedValue.value == ucPayload.digest;   
            assert hsrcPayload.round == b.header.roundNumber+1 == ucPayload.round + 1;
            assert b'.header.roundNumber ==  b.header.roundNumber+1; 

            

            var rcm :| 
                    && rcm in rcs 
                    && isHighestPrepared(rcm,rcs)

                    // NOTE: The following tweak is required due to the addition of the round number to the block
                    // header This is how this is curently done in IBFT2, there could be more elegant ways to
                    // achieve the same.
                    && var proposedBlockWithOldRound := 
                            replaceRoundInBlock(
                                b',
                                optionGet(rcm.unsignedPayload.preparedRound)
                            );                        
                    && optionGet(rcm.unsignedPayload.preparedValue) == digest(proposedBlockWithOldRound)
                    && (forall pm | pm in ps :: 
                                        validSignedPrepareForHeightRoundAndDigest(
                                            pm,
                                            h,
                                            optionGet(rcm.unsignedPayload.preparedRound),
                                            optionGet(rcm.unsignedPayload.preparedValue),
                                            V
                                        ));    

            assert rcm.unsignedPayload.height == h;
            assert rcm.unsignedPayload.preparedRound.value == ucPayload.round;   
            assert |ps| >= quorum(|V|); 

            assert isInstrNodeHonest(s, hInInt); 
            assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s);
            assert indInvInstrNodeState(s.nodes[hInInt]);

            assert invInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares(s.nodes[hInInt]);

            var QofP := lemmaGetQofPFromRoundChange(s.nodes[hInInt], hrc);

            assert V == validators(s.nodes[hInInt].nodeState.blockchain[..h]);
            // var QofP :| 
            assert
                    && QofP <= validPreparesForHeightRoundAndDigest(
                                s.nodes[hInInt].nodeState.messagesReceived,
                                hsrcPayload.height,
                                hsrcPayload.preparedRound.value,
                                hsrcPayload.preparedValue.value,
                                V)
                    && |QofP| >= quorum(|V|);  

            var qofpSenders := getSetOfSenders(QofP);
            lemmaSizeOfSetOfConsistentPreparesMatchesTheSizeOfTheSetOfAssociatedSignatures(QofP, h,hsrcPayload.preparedRound.value,hsrcPayload.preparedValue.value);
            assert |qofpSenders| ==  |QofP|; 

            var psSenders := getSetOfSignedPrepareSenders(ps);
            lemmaSizeOfSetOfConsistentSignedPreparesMatchesTheSizeOfTheSetOfAssociatedSignatures(ps, h, rcm.unsignedPayload.preparedRound.value, rcm.unsignedPayload.preparedValue.value);
            assert |psSenders| ==  |ps|; 

            lemmaQuorumIntersection(Vset, s.adversary.byz, qofpSenders, psSenders);
            var hInInt2 :| hInInt2 in (qofpSenders * psSenders * (Vset - s.adversary.byz));

            var pm1:QbftMessage :|  
                                            && pm1 in s.nodes[hInInt].nodeState.messagesReceived
                                            && pm1.Prepare?
                                            && recoverSignature(pm1) == hInInt2
                                            && var uPayload := pm1.preparePayload.unsignedPayload;
                                            && uPayload.height == h
                                            && uPayload.round == hsrcPayload.preparedRound.value 
                                            && uPayload.digest == hsrcPayload.preparedValue.value;     

            var spp1 := SignedPreparePayload(pm1.preparePayload);
            lemmaOnFilterSignedPayloadsByAuthorOfGetSetOfSignedPayloadsOfASetIncludesSignedPreparePyloadOfMemberOfTheSet(
                s.nodes[hInInt].nodeState.messagesReceived,
                pm1,
                spp1,
                hInInt2
            );
            assert spp1 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[hInInt].nodeState.messagesReceived), hInInt2);
            assert spp1 in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hInInt2));
            // // assert spp1 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hInInt2)), hInInt2);
            // // var pm1': QbftMessage :| pm1'.Prepare? && pm1' in getAllMessagesSentByTheNode(s, hInInt2) && pm1'.preparePayload == pm1.preparePayload;    

            var pm1' := lemmaGetPrepareMessageCorrespondingToSignedPayload(s,spp1,  hInInt2);                                            

            // // assert pm1 in  fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt2].messagesSent) +
            // //             s.nodes[hInInt2].messagesSentToItself;    

            var pm2:SignedPrepare :|  
                                    && pm2 in ps
                                    && recoverSignedPrepareAuthor(pm2) == hInInt2
                                    && var uPayload := pm2.unsignedPayload;
                                    && uPayload.height == h
                                    && uPayload.round == rcm.unsignedPayload.preparedRound.value 
                                    && uPayload.digest == rcm.unsignedPayload.preparedValue.value;   

            // // assert isInstrNodeHonest(s,hInInt2);

            var spp2 := SignedPreparePayload(pm2);
            lemmaExtractSignedPreparesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s), pm2, hInInt2);
            // assert spp2 in getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s));
            assert spp2 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), hInInt2);
            // assert spp2 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)),hInInt2);
            // assert spp2 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt2].messagesSent)), hInInt2);


            // assert spp2 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hInInt2)), hInInt2) by {
            //     lemmaMapFromMultisetQbftMessagesWithRecipientToSetOfMessagesGetAllMessagesSentByTheNode(
            //         s,
            //         spp2,
            //         hInInt2
            //     );
            // }
            lemmaValidBlockAndBlockIncludedInValidPropsosalForNextRoundAreTheSameExceptForCommitSealsAndRoundHelper2(s, spp2, hInInt2);
            assert spp2 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hInInt2)), hInInt2);
            // // assert spp2 in getSetOfSignedPayloads(allMessagesSentBy(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt2].messagesSent),hInInt2));
            // // assert spp2 in getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt2].messagesSent));   

            // // assert spp2 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,hInInt2)), hInInt2) ;

            
            // // // assert spp2 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[hInInt].nodeState.messagesReceived), hInInt2);
            // // // assert spp1 in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hInInt2));
            // // // assert spp1 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hInInt2)), hInInt2);
            // // // var pm1': QbftMessage :| pm1'.Prepare? && pm1' in getAllMessagesSentByTheNode(s, hInInt2) && pm1'.preparePayload == pm1.preparePayload;    

            var pm2' := lemmaGetPrepareMessageCorrespondingToSignedPayload(s,spp2,  hInInt2);                     

            assert invInstrNodeStateNoConflictingPreapresSent(s.nodes[hInInt2]);

            assert rcm.unsignedPayload.preparedValue.value == hsrcPayload.preparedValue.value;    

            assert rcm.unsignedPayload.preparedRound.value == ucPayload.round == block1.header.roundNumber; 

            var proposedBlockWithOldRound := 
                            replaceRoundInBlock(
                                b',
                                block1.header.roundNumber
                            );      

            

            assert hsrcPayload.preparedValue.value == digest(proposedBlockWithOldRound);  
            assert ucPayload.digest == digest(proposedBlockWithOldRound);
            assert ucPayload.digest  == digest(b1');
            assert areBlocksTheSameExceptForTheCommitSeals(b1',block1);
            assert areBlocksTheSameExceptForTheCommitSeals(proposedBlockWithOldRound,block1);

            assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
            assert b'.header.roundNumber == b.header.roundNumber + 1;


            // // assert isQuorumOfPrepares(h, rcm.unsignedPayload.preparedRound.value, rcm.unsignedPayload.preparedValue.value, ps, s.nodes[n1].nodeState.blockchain[..h]);     
            // // assert areBlocksTheSameExceptForTheCommitSeals(p1.proposedBlock,block1);     
            // // assume areBlocksTheSameExceptForTheCommitSeals(bm.block, b');
        }
    }

    // 4s 3.2.0
    lemma lemmaInvValidBlockAndBlockIncludedInValidPropsosalForNextRoundAreTheSameExceptForCommitSeals(
        s: InstrDSState,
        h: nat,
        n1: Address
    )
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s)
    requires isInstrNodeHonest(s,n1)
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])        
    ensures invValidBlockAndBlockIncludedInValidPropsosalForNextRoundAreTheSameExceptForCommitSeals(s, h, n1)
    {
        forall 
            b: Block, 
            // b: Block, 
            // h:nat, 
            pm
        ensures
            (
                && isInstrNodeHonest(s,n1)
                // && isInstrNodeHonest(s,n2)
                // && s.nodes[n1].nodeState.blockchain <= s.nodes[n2].nodeState.blockchain
                // && |s.nodes[n1].nodeState.blockchain| >= h
                && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b)
                && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
                && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                && pm.proposalPayload.unsignedPayload.round == b.header.roundNumber+1               
            ) ==> 
            (
                && areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm.proposedBlock)   
                && pm.proposedBlock.header.roundNumber == b.header.roundNumber + 1
            ) 
        {
            if(
                // && isInstrNodeHonest(s,n2)
                // && s.nodes[n1].nodeState.blockchain <= s.nodes[n2].nodeState.blockchain
                // && |s.nodes[n1].nodeState.blockchain| >= h
                && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b)
                && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
                && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                && pm.proposalPayload.unsignedPayload.round == b.header.roundNumber+1               
            )
            {
                assert pm.proposalJustification <= extractSignedRoundChangesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s));
                assert pm.roundChangeJustification <= extractSignedPreparesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s));
                var current := s.nodes[n1].nodeState;
                var vb := b => validateNonPreparedBlock(b,current.blockchain[..h],pm.proposalPayload.unsignedPayload.round);
                var rl := proposer(pm.proposalPayload.unsignedPayload.round,current.blockchain[..h]);
                // var h := |current.blockchain|;
                // assert current.blockchain == current.blockchain[..h];
                assert ValidNewBlock(current.blockchain[..h], b);
                assert isProposalJustification(
                    pm.proposalJustification ,
                    pm.roundChangeJustification,
                    {pm.proposedBlock},
                    h,
                    b.header.roundNumber+1,
                    pm.proposedBlock,
                    vb,
                    rl,
                    validators(current.blockchain[..h])
                );

                

                assert
                && areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm.proposedBlock)   
                && pm.proposedBlock.header.roundNumber == b.header.roundNumber + 1 by
                {
                    lemmaInvValidBlockAndBlockIncludedInValidPropsosalJustificationForNextRoundAreTheSameExceptForCommitSeals(
                        s,
                        b,
                        h,
                        n1,
                        pm.proposalJustification,
                        pm.roundChangeJustification,
                        pm.proposedBlock,
                        rl,
                        vb
                    );
                }
            }
        }
    }    
    
    lemma lemmaIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidBlockForTheSameRoundIsAlsoConsistentWithThatBlockHelper1(
        s: InstrDSState,
        n: Address,
        cm: QbftMessage
    ) returns (pm': QbftMessage)
    requires isInstrNodeHonest(s, n)
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires    && cm in getAllMessagesSentByInsrNodeState(s.nodes[n])
                && cm.Commit?
                && cm.commitPayload.unsignedPayload.height > 0
    ensures 
            && pm'.Proposal?
            && pm' in s.nodes[n].proposalsAccepted
            && pm' in s.nodes[n].nodeState.messagesReceived
            &&  var cuPayload := cm.commitPayload.unsignedPayload;  
                var puPayload := pm'.proposalPayload.unsignedPayload;
            &&  puPayload.height == cuPayload.height
            &&  puPayload.round == cuPayload.round
            &&  digest(pm'.proposedBlock) == cuPayload.digest
            &&  signHash(hashBlockForCommitSeal(pm'.proposedBlock), s.nodes[n].nodeState.id) == cuPayload.commitSeal 
            && puPayload.height <= |s.nodes[n].nodeState.blockchain|  
            && proposerPrecondition(s.nodes[n].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height])
            && isValidProposalJustification(pm', s.nodes[n].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);          
    {
        pm' :| 
            && pm' in s.nodes[n].proposalsAccepted
            &&  var cuPayload := cm.commitPayload.unsignedPayload;  
                var puPayload := pm'.proposalPayload.unsignedPayload;
            &&  puPayload.height == cuPayload.height
            &&  puPayload.round == cuPayload.round
            &&  digest(pm'.proposedBlock) == cuPayload.digest
            &&  signHash(hashBlockForCommitSeal(pm'.proposedBlock), s.nodes[n].nodeState.id) == cuPayload.commitSeal;          
    } 

    lemma lemmaIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidBlockForTheSameRoundIsAlsoConsistentWithThatBlockHelper2(
        s: InstrDSState,
        h: nat,
        n1: Address,
        n2: Address,
        pm': QbftMessage
    ) 
    requires validInstrDSStateEx(s)   
    requires isInstrNodeHonest(s, n1)
    requires isInstrNodeHonest(s, n2)
    requires |s.nodes[n1].nodeState.blockchain| >= h > 0
    requires |s.nodes[n2].nodeState.blockchain| >= h > 0
    requires isValidProposalJustification(pm', s.nodes[n1].nodeState.blockchain[..h]);
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    ensures  isValidProposalJustification(pm', s.nodes[n2].nodeState.blockchain[..h]); 
    {
        lemmaPBlockchainConsistencyUpToHeightImpliesConsistencyForHonestBlockchainOfThatHeight(
            s, 
            h, 
            n1,
            n2
        );  

        lemmaValidatorsAreTheSameOfTheGenesisBlock();

        var bc1 := s.nodes[n1].nodeState.blockchain[..h];

        assert |bc1| >1 ==> isUniqueSequence(validators(bc1[..|bc1|-1])) by
        {
            if |s.nodes[n1].nodeState.blockchain[..h]| > 1 
            {
                assert validators(s.nodes[n1].nodeState.blockchain[..h-1]) == validators([s.configuration.genesisBlock]);
                assert isUniqueSequence(validators(s.nodes[n1].nodeState.blockchain[..h-1]) );
                assert s.nodes[n1].nodeState.blockchain[..h-1] == s.nodes[n1].nodeState.blockchain[..h][..h-1];
                assert |s.nodes[n1].nodeState.blockchain[..h]| == h;
            }
            assert bc1 == s.nodes[n1].nodeState.blockchain[..h];
        }
        // assert |s.nodes[hSender1].nodeState.blockchain[..h]| == h;
        assert proposerPrecondition(bc1);
        assert proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h]);
        assert isValidProposalJustification(pm', bc1);        
        lemmaOnFromBlockchainToRawBlockchainEquivalencePreservesValidProposalJustification(bc1, s.nodes[n2].nodeState.blockchain[..h], pm'); 
        assert  isValidProposalJustification(pm', s.nodes[n2].nodeState.blockchain[..h]);         
    }

    // 22s 3.2.0
    lemma lemmaInvIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidBlockForTheSameRoundIsAlsoConsistentWithThatBlock(
        s: InstrDSState,
        h: nat,
        r: nat,
        n1: Address,
        b: Block
    )
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires invProposalAcceptedByHonestNodesHaveBeenSent(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s)
    requires 
                && isInstrNodeHonest(s,n1)
    requires    |s.nodes[n1].nodeState.blockchain| >= h
    requires    proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h]) 
    ensures invIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidBlockForTheSameRoundIsAlsoConsistentWithThatBlock(s, h, r, n1, b)                  
    {
        if  
            (
                forall pm ::
                    (
                        && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                        && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
                        && pm.proposalPayload.unsignedPayload.round == r
                    )  ==>
                    (
                        && areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm.proposedBlock)   
                    )
            )
        {
            // assert invForEveryCommitSealsSignedByAnHonestNodeExcludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s);
            // lemmaInvTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestForAll(s);
            // lemmaInvTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigestForAll(s);
            lemmaValidatorsAreTheSameOfTheGenesisBlock();
            lemmaDigest();

            forall b':Block | 
                        && b'.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                        && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b')
                        && b'.header.roundNumber == r
            ensures  areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
            {
                var blockchain := s.nodes[n1].nodeState.blockchain[..h];
                // var h := |blockchain|;
                // assert bm.block.header.height == h;

                var block1 := b';
                var bhash1 := hashBlockForCommitSeal(block1);
                var css1 := block1.header.commitSeals;
                var cssAuth1 := getCommitSealAuthors(bhash1, css1);
                lemmaOnSizeOfSetOfCommitSeals(bhash1, css1);

                var vals := validators(blockchain);
                lUniqueSeq(vals);  
                assert |cssAuth1| >= quorum(|vals|); 

                assert vals == validators([s.configuration.genesisBlock]);

                assert |s.adversary.byz| <= f(|vals|);

                lemmaThereExistsAnHonestInQuorum(seqToSet(vals), s.adversary.byz, cssAuth1);

                var hSender1 :|
                                && hSender1 in cssAuth1
                                && isInstrNodeHonest(s, hSender1);

                var cs1 :|  && cs1 in css1
                            && recoverSignedHashAuthor(bhash1, cs1) == hSender1;  

                assert cs1 in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s));
                
                // // assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeStateTypes)(s);
                lemmaValidBlockAndBlockIncludedInValidPropsosalForNextRoundAreTheSameExceptForCommitSealsAndRoundHelper(s, block1, cs1, hSender1);
                assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block1,hSender1);
                // // // // by {
                // // // //     assume invForEveryCommitSealsSignedByAnHonestNodeExcludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s);
                // // // //     assume cs1 in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent));
                // // // //     assume isInstrNodeHonest(s, hSender1);
                // // // //     assume recoverSignedHashAuthor(hashBlockForCommitSeal(block1), cs1) == hSender1;
                // // // // }

                var cm1, b1', p1 := lemmaGetCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block1,cs1,hSender1);

                assert   
                    && cm1 in getAllMessagesSentByTheNode(s, hSender1)
                    && p1 in s.nodes[hSender1].proposalsAccepted
                    && p1.proposedBlock == b1'
                    && areBlocksTheSameExceptForTheCommitSeals(b1',block1)
                    && cm1.Commit?
                    && cm1.commitPayload.unsignedPayload.height == block1.header.height
                    && cm1.commitPayload.unsignedPayload.round == block1.header.roundNumber
                    && cm1.commitPayload.unsignedPayload.digest == digest(b1');

                
                var cuPayload := cm1.commitPayload.unsignedPayload;

                assert cuPayload.height == |blockchain|;

                // assert indInvInstrNodeState(s.nodes[hSender1]);
                // assert invInstrNodeStateCommitSentOnlyIfAcceptedProposal(s.nodes[hSender1]);

                var pm' := lemmaIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidBlockForTheSameRoundIsAlsoConsistentWithThatBlockHelper1(s, hSender1, cm1);

                // var pm' :| 
                //     && pm' in s.nodes[hSender1].proposalsAccepted
                //     &&  
                //         var puPayload := pm'.proposalPayload.unsignedPayload;
                //     &&  puPayload.height == cuPayload.height
                //     &&  puPayload.round == cuPayload.round
                //     &&  digest(pm'.proposedBlock) == cuPayload.digest
                //     &&  signHash(hashBlockForCommitSeal(pm'.proposedBlock), s.nodes[hSender1].nodeState.id) == cuPayload.commitSeal;  


                // assert forall pm'' |    && pm'' in s.nodes[hSender1].proposalsAccepted
                //                         &&  var uPayload1 := pm'.proposalPayload.unsignedPayload;
                //                             var uPayload2 := pm''.proposalPayload.unsignedPayload;
                //                         && uPayload1.height == uPayload2.height
                //                         && uPayload1.round == uPayload2.round
                //                     ::
                //                         pm'.proposedBlock == pm''.proposedBlock; 

                assert pm'.proposalPayload.unsignedPayload.height <= |s.nodes[hSender1].nodeState.blockchain[..h]|;
                assert pm' in s.nodes[hSender1].nodeState.messagesReceived;
                // assert pm'.proposalPayload.unsignedPayload.round == cuPayload.round == b'.header.roundNumber == r;

                // calc == {
                //     pm'.proposalPayload.unsignedPayload.round;
                //     cuPayload.round; 
                //     b'.header.roundNumber;
                //     r;
                // }
                // assert pm'.proposalPayload.unsignedPayload.round == r;

                // assert pm'.proposalPayload.unsignedPayload.height == |s.nodes[hSender1].nodeState.blockchain|;

                assert isValidProposalJustification(pm', s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);
                assert pm'.proposalPayload.unsignedPayload.height == h;
                assert isValidProposalJustification(pm', s.nodes[hSender1].nodeState.blockchain[..h]);
                lemmaIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidBlockForTheSameRoundIsAlsoConsistentWithThatBlockHelper2(
                    s,
                    h,
                    hSender1,
                    n1,
                    pm'
                );
                // lemmaPBlockchainConsistencyUpToHeightImpliesConsistencyForHonestBlockchainOfThatHeight(
                //     s, 
                //     h, 
                //     hSender1,
                //     n1
                // );  

                // var bc1 := s.nodes[hSender1].nodeState.blockchain[..h];

                // assert |bc1| >1 ==> isUniqueSequence(validators(bc1[..|bc1|-1])) by
                // {
                //     if |s.nodes[hSender1].nodeState.blockchain[..h]| > 1 
                //     {
                //         assert validators(s.nodes[hSender1].nodeState.blockchain[..h-1]) == validators([s.configuration.genesisBlock]);
                //         assert isUniqueSequence(validators(s.nodes[hSender1].nodeState.blockchain[..h-1]) );
                //         assert s.nodes[hSender1].nodeState.blockchain[..h-1] == s.nodes[hSender1].nodeState.blockchain[..h][..h-1];
                //         assert |s.nodes[hSender1].nodeState.blockchain[..h]| == h;
                //     }
                //     assert bc1 == s.nodes[hSender1].nodeState.blockchain[..h];
                // }
                // // assert |s.nodes[hSender1].nodeState.blockchain[..h]| == h;
                // assert proposerPrecondition(bc1);
                // assert proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h]);
                // assert isValidProposalJustification(pm', bc1);
                // lemmaOnFromBlockchainToRawBlockchainEquivalencePreservesValidProposalJustification(bc1, s.nodes[n1].nodeState.blockchain[..h], pm');          
                // assert s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height] == s.nodes[n1].nodeState.blockchain[..h];
                assert  isValidProposalJustification(pm', s.nodes[n1].nodeState.blockchain[..h]);
                assert pm'.proposalPayload.unsignedPayload.round == r;
                assert pm' in s.nodes[hSender1].nodeState.messagesReceived;
                assert pm' in allMesssagesSentIncSentToItselfWithoutRecipient(s);
                // assert pm' in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent);
                assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm'.proposedBlock);
                assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');

                // if(validInstrDSStateEx(s))
                // {
                    
                // } 

            }
        }
    }   

    lemma lemmaIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidQuorumOfPreparesForTheSameRoundIsAlsoConsistentWithThatBlockHelper1(
        s: InstrDSState,
        n: Address,
        p: QbftMessage
    ) returns (pm': QbftMessage)
    requires isInstrNodeHonest(s, n)
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires    && p in getAllMessagesSentByInsrNodeState(s.nodes[n])
                && p.Prepare?
                && p.preparePayload.unsignedPayload.height > 0
    // requires |s.nodes[n].nodeState.blockchain| > 0
    ensures 
            && pm'.Proposal?
            && pm' in s.nodes[n].proposalsAccepted
            && pm' in s.nodes[n].nodeState.messagesReceived
            &&  var cuPayload := p.preparePayload.unsignedPayload;  
                var puPayload := pm'.proposalPayload.unsignedPayload;
            &&  puPayload.height == cuPayload.height
            &&  puPayload.round == cuPayload.round
            &&  digest(pm'.proposedBlock) == cuPayload.digest
            && puPayload.height <= |s.nodes[n].nodeState.blockchain|  
            && proposerPrecondition(s.nodes[n].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height])
            && isValidProposalJustification(pm', s.nodes[n].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);          
    {
        pm' :| 
            && pm' in s.nodes[n].proposalsAccepted
            &&  var cuPayload := p.preparePayload.unsignedPayload;  
                var puPayload := pm'.proposalPayload.unsignedPayload;
            &&  puPayload.height == cuPayload.height
            &&  puPayload.round == cuPayload.round
            &&  digest(pm'.proposedBlock) == cuPayload.digest;       
    }   

    // 23s 3.2.0
    lemma lemmaInvIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidQuorumOfPreparesForTheSameRoundIsAlsoConsistentWithThatBlock(
        s: InstrDSState,
        r: nat,
        h: nat,
        n1: Address,
        b: Block
    )
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires invProposalAcceptedByHonestNodesHaveBeenSent(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    // requires invForEveryCommitSealsSignedByAnHonestNodeExcludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s)
    requires 
                && isInstrNodeHonest(s,n1)
    requires    |s.nodes[n1].nodeState.blockchain| >= h
    requires    proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])
    ensures invIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidQuorumOfPreparesForTheSameRoundIsAlsoConsistentWithThatBlock(s, r, h, n1, b)                               
    {
        if  forall pm ::
            (
                && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
                && pm.proposalPayload.unsignedPayload.round == r
            )  ==>
            (
                && areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm.proposedBlock)   
            )
        {
            lemmaValidatorsAreTheSameOfTheGenesisBlock();
            lemmaDigest();

            var blockchain := s.nodes[n1].nodeState.blockchain[..h];
            var V := validators(blockchain);

            forall ps:set<SignedPrepare>, b':Block |
                            && ps <= extractSignedPreparesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                            && |ps| >= quorum(|V|)
                            &&  (forall prep | prep in ps :: 
                                                validSignedPrepareForHeightRoundAndDigest(
                                                    prep,
                                                    h,
                                                    r,
                                                    digest(b'),
                                                    V
                                                ))
            ensures areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
            {
                lUniqueSeq(V);  

                var d := digest(b');

                assert V == validators([s.configuration.genesisBlock]);

                assert |s.adversary.byz| <= f(|V|);

                var psSenders := getSetOfSignedPrepareSenders(ps);
                lemmaSizeOfSetOfConsistentSignedPreparesMatchesTheSizeOfTheSetOfAssociatedSignatures(ps, h, r, d);
                assert |psSenders| ==  |ps|;     

                lemmaThereExistsAnHonestInQuorum(seqToSet(V), s.adversary.byz, psSenders);     

                var hSender1 :|
                                && hSender1 in psSenders
                                && isInstrNodeHonest(s, hSender1);  

                var sprep :| && sprep in ps   
                            && recoverSignedPrepareAuthor(sprep) == hSender1;   


                var spp1 := SignedPreparePayload(sprep);    
                assert spp1 in getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s));
                assert spp1 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), hSender1);
                // assert spp1 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)),hInInt2);
                assert spp1 in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hSender1));

                var prep := lemmaGetPrepareMessageCorrespondingToSignedPayload(s,spp1,  hSender1);

                assert prep in getAllMessagesSentByInsrNodeState(s.nodes[hSender1]);  

                var pm' := lemmaIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidQuorumOfPreparesForTheSameRoundIsAlsoConsistentWithThatBlockHelper1(s, hSender1, prep);   

                // var pm' :| 
                //     && pm' in s.nodes[hSender1].proposalsAccepted
                //     &&  
                //         var cuPayload := prep.preparePayload.unsignedPayload;
                //         var puPayload := pm'.proposalPayload.unsignedPayload;
                //     &&  puPayload.height == cuPayload.height
                //     &&  puPayload.round == cuPayload.round
                //     &&  digest(pm'.proposedBlock) == cuPayload.digest;


                // assert forall pm'' |    && pm'' in s.nodes[hSender1].proposalsAccepted
                //                         &&  var uPayload1 := pm'.proposalPayload.unsignedPayload;
                //                             var uPayload2 := pm''.proposalPayload.unsignedPayload;
                //                         && uPayload1.height == uPayload2.height
                //                         && uPayload1.round == uPayload2.round
                //                     ::
                //                         pm'.proposedBlock == pm''.proposedBlock; 

                assert isValidProposalJustification(pm', s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);
                assert pm'.proposalPayload.unsignedPayload.height == h;
                assert isValidProposalJustification(pm', s.nodes[hSender1].nodeState.blockchain[..h]);    
                lemmaIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidBlockForTheSameRoundIsAlsoConsistentWithThatBlockHelper2(
                    s,
                    h,
                    hSender1,
                    n1,
                    pm'
                ); 
                assert  isValidProposalJustification(pm', s.nodes[n1].nodeState.blockchain[..h]);
                    

                // assert isValidProposalJustification(pm', s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);
                // assert s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height] == s.nodes[n1].nodeState.blockchain[..h];
                // assert  isValidProposalJustification(pm', s.nodes[n1].nodeState.blockchain[..h]);
                assert pm'.proposalPayload.unsignedPayload.round == r;
                assert pm' in s.nodes[hSender1].nodeState.messagesReceived;
                assert pm' in allMesssagesSentIncSentToItselfWithoutRecipient(s);
                // assert pm' in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent);
                assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm'.proposedBlock);
                assert digest(pm'.proposedBlock) == d;
                assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
            }
        }
    }    

    // 24s 3.2.0
    lemma lemmaInvIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockAnyValidQuorumOfPreparesForTheSameRoundIsForABlockWithProposerInTheSetOfValidators(
        s: InstrDSState,
        r: nat,
        h: nat,
        n1: Address
    )
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires invProposalAcceptedByHonestNodesHaveBeenSent(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s)
    requires 
                && isInstrNodeHonest(s,n1)
    requires    |s.nodes[n1].nodeState.blockchain| >= h
    requires    proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])
    ensures invIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockAnyValidQuorumOfPreparesForTheSameRoundIsForABlockWithProposerInTheSetOfValidators(s, r, h, n1)                           
    {
        if  forall pm ::
                (
                    && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                    && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
                    && pm.proposalPayload.unsignedPayload.round == r
                )  ==>
                (
                    && pm.proposedBlock.header.proposer in validators(s.nodes[n1].nodeState.blockchain[..h])
                )
        {
            lemmaValidatorsAreTheSameOfTheGenesisBlock();
            lemmaDigest();

            var blockchain := s.nodes[n1].nodeState.blockchain[..h];
            var V := validators(blockchain);

            forall ps:set<SignedPrepare>, b':Block |
                            && ps <= extractSignedPreparesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                            && |ps| >= quorum(|V|)
                            &&  (forall prep | prep in ps :: 
                                                validSignedPrepareForHeightRoundAndDigest(
                                                    prep,
                                                    h,
                                                    r,
                                                    digest(b'),
                                                    V
                                                ))
            ensures b'.header.proposer in validators(s.nodes[n1].nodeState.blockchain[..h])  
            {
                lUniqueSeq(V);  

                var d := digest(b');

                assert V == validators([s.configuration.genesisBlock]);

                assert |s.adversary.byz| <= f(|V|);

                var psSenders := getSetOfSignedPrepareSenders(ps);
                lemmaSizeOfSetOfConsistentSignedPreparesMatchesTheSizeOfTheSetOfAssociatedSignatures(ps, h, r, d);
                assert |psSenders| ==  |ps|;     

                lemmaThereExistsAnHonestInQuorum(seqToSet(V), s.adversary.byz, psSenders);     

                var hSender1 :|
                                && hSender1 in psSenders
                                && isInstrNodeHonest(s, hSender1);  

                var sprep :| && sprep in ps   
                            && recoverSignedPrepareAuthor(sprep) == hSender1;   


                var spp1 := SignedPreparePayload(sprep);    
                assert spp1 in getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s));
                assert spp1 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), hSender1);
                // assert spp1 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)),hInInt2);
                assert spp1 in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hSender1));

                var prep := lemmaGetPrepareMessageCorrespondingToSignedPayload(s,spp1,  hSender1);

                assert prep in getAllMessagesSentByInsrNodeState(s.nodes[hSender1]);  

                var pm' := lemmaIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidQuorumOfPreparesForTheSameRoundIsAlsoConsistentWithThatBlockHelper1(s, hSender1, prep);   

                // var pm' :| 
                //     && pm' in s.nodes[hSender1].proposalsAccepted
                //     &&  
                //         var cuPayload := prep.preparePayload.unsignedPayload;
                //         var puPayload := pm'.proposalPayload.unsignedPayload;
                //     &&  puPayload.height == cuPayload.height
                //     &&  puPayload.round == cuPayload.round
                //     &&  digest(pm'.proposedBlock) == cuPayload.digest;


                // assert forall pm'' |    && pm'' in s.nodes[hSender1].proposalsAccepted
                //                         &&  var uPayload1 := pm'.proposalPayload.unsignedPayload;
                //                             var uPayload2 := pm''.proposalPayload.unsignedPayload;
                //                         && uPayload1.height == uPayload2.height
                //                         && uPayload1.round == uPayload2.round
                //                     ::
                //                         pm'.proposedBlock == pm''.proposedBlock; 

                assert isValidProposalJustification(pm', s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);
                assert pm'.proposalPayload.unsignedPayload.height == h;
                assert isValidProposalJustification(pm', s.nodes[hSender1].nodeState.blockchain[..h]);    
                lemmaIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidBlockForTheSameRoundIsAlsoConsistentWithThatBlockHelper2(
                    s,
                    h,
                    hSender1,
                    n1,
                    pm'
                ); 
                assert  isValidProposalJustification(pm', s.nodes[n1].nodeState.blockchain[..h]);
                    

                // assert isValidProposalJustification(pm', s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);
                // assert s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height] == s.nodes[n1].nodeState.blockchain[..h];
                // assert  isValidProposalJustification(pm', s.nodes[n1].nodeState.blockchain[..h]);
                assert pm'.proposalPayload.unsignedPayload.round == r;
                assert pm' in s.nodes[hSender1].nodeState.messagesReceived;
                assert pm' in allMesssagesSentIncSentToItselfWithoutRecipient(s);
                // assert pm' in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent);
                // assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm'.proposedBlock);
                assert digest(pm'.proposedBlock) == d;
                assert b'.header.proposer in validators(s.nodes[n1].nodeState.blockchain[..h]) ;
            }
        }
    }       

    lemma lemmaAnyValidQuorumOfPreparesForTheSameRoundAsAValidBlockIsForABlockConsistentWithTheValidBlockHelper1(
        s: InstrDSState,
        n: Address
    )
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires isInstrNodeHonest(s, n)
    ensures invInstrNodeStatePrepareAndCommitMatch(s.nodes[n])
    {}

    // 39s 3.2.0
    lemma lemmaInvAnyValidQuorumOfPreparesForTheSameRoundAsAValidBlockIsForABlockConsistentWithTheValidBlock(
        s: InstrDSState,
        // r: nat,
        h: nat,
        n1: Address,
        b: Block
    )
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires invProposalAcceptedByHonestNodesHaveBeenSent(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s)
    requires 
                && isInstrNodeHonest(s,n1)
    requires    |s.nodes[n1].nodeState.blockchain| >= h
    requires    proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])    
    ensures invAnyValidQuorumOfPreparesForTheSameRoundAsAValidBlockIsForABlockConsistentWithTheValidBlock(s, h, n1, b)       
    {
        if  && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h], b)
        {
            // assert invForEveryCommitSealsSignedByAnHonestNodeExcludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s);
            // lemmaInvTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestForAll(s);
            // lemmaInvTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigestForAll(s);
            lemmaValidatorsAreTheSameOfTheGenesisBlock();
            lemmaDigest();

            var blockchain := s.nodes[n1].nodeState.blockchain[..h];
            var V := validators(blockchain);

            // forall bm | 
            //             && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
            //             && validNewBlockMessage(s.nodes[n1].nodeState.blockchain,bm)
            //             && bm.block.header.roundNumber == r
            forall ps:set<SignedPrepare>, b':Block |
                            && ps <= extractSignedPreparesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                            && |ps| >= quorum(|V|)
                            &&  (forall prep | prep in ps :: 
                                                validSignedPrepareForHeightRoundAndDigest(
                                                    prep,
                                                    h,
                                                    b.header.roundNumber,
                                                    digest(b'),
                                                    V
                                                ))
            ensures areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
            // ensures  areBlocksTheSameExceptForTheCommitSealsAndRound(b, bm.block);
            {
                var blockchain := s.nodes[n1].nodeState.blockchain[..h];

                assert b.header.height == h;

                var block1 := b;
                var bhash1 := hashBlockForCommitSeal(block1);
                var css1 := block1.header.commitSeals;
                var cssAuth1 := getCommitSealAuthors(bhash1, css1);
                lemmaOnSizeOfSetOfCommitSeals(bhash1, css1);

                var vals := validators(blockchain);
                lUniqueSeq(V);  
                assert |cssAuth1| >= quorum(|vals|); 

                var d := digest(b');

                assert V == validators([s.configuration.genesisBlock]);

                assert |s.adversary.byz| <= f(|V|);

                var psSenders := getSetOfSignedPrepareSenders(ps);
                lemmaSizeOfSetOfConsistentSignedPreparesMatchesTheSizeOfTheSetOfAssociatedSignatures(ps, h, b.header.roundNumber, d);
                assert |psSenders| ==  |ps|;  

                // lemmaThereExistsAnHonestInQuorum(seqToSet(vals), s.adversary.byz, cssAuth1);

                var Vset := seqToSet(V);
                lemmaQuorumIntersection(Vset, s.adversary.byz, cssAuth1, psSenders);

                var hSender1 :| hSender1 in (psSenders * cssAuth1 * (Vset - s.adversary.byz));


                // var hSender1 :|
                //                 && hSender1 in cssAuth1
                //                 && isInstrNodeHonest(s, hSender1);

                var cs1 :|  && cs1 in css1
                            && recoverSignedHashAuthor(bhash1, cs1) == hSender1;  

                assert cs1 in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s));
                
                // // // // // assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeStateTypes)(s);
                assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block1,hSender1);
                // // // // // // // by {
                // // // // // // //     assume invForEveryCommitSealsSignedByAnHonestNodeExcludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s);
                // // // // // // //     assume cs1 in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent));
                // // // // // // //     assume isInstrNodeHonest(s, hSender1);
                // // // // // // //     assume recoverSignedHashAuthor(hashBlockForCommitSeal(block1), cs1) == hSender1;
                // // // // // // // }

                var cm1, b1', p1 := lemmaGetCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block1,cs1,hSender1);

                assert   
                    && cm1 in getAllMessagesSentByTheNode(s, hSender1)
                    && p1 in s.nodes[hSender1].proposalsAccepted
                    && p1.proposedBlock == b1'
                    && areBlocksTheSameExceptForTheCommitSeals(b1',block1)
                    && cm1.Commit?
                    && cm1.commitPayload.unsignedPayload.height == block1.header.height
                    && cm1.commitPayload.unsignedPayload.round == block1.header.roundNumber
                    && cm1.commitPayload.unsignedPayload.digest == digest(b1');

                assert cm1 in getAllMessagesSentByInsrNodeState(s.nodes[hSender1]);  

                
                // // var cuPayload := cm1.commitPayload.unsignedPayload;

                // // assert cuPayload.height == |blockchain|;

                // // assert indInvInstrNodeState(s.nodes[hSender1]);
                // // assert invInstrNodeStateCommitSentOnlyIfAcceptedProposal(s.nodes[hSender1]);

    

                // lemmaThereExistsAnHonestInQuorum(seqToSet(V), s.adversary.byz, psSenders);     

                // var hSender1 :|
                //                 && hSender1 in psSenders
                //                 && isInstrNodeHonest(s, hSender1);  

                var sprep :| && sprep in ps   
                            && recoverSignedPrepareAuthor(sprep) == hSender1;   


                var spp1 := SignedPreparePayload(sprep);    
                assert spp1 in getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s));
                assert spp1 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), hSender1);
                // assert spp1 in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)),hInInt2);
                assert spp1 in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hSender1));

                var prep := lemmaGetPrepareMessageCorrespondingToSignedPayload(s,spp1,  hSender1);

                assert prep in getAllMessagesSentByInsrNodeState(s.nodes[hSender1]);     
                assert prep.preparePayload.unsignedPayload.height == cm1.commitPayload.unsignedPayload.height;
                assert prep.preparePayload.unsignedPayload.round == cm1.commitPayload.unsignedPayload.round;

                // // assert invInstrNodeStatePrepareAndCommitMatch(s.nodes[hSender1]);  
                lemmaAnyValidQuorumOfPreparesForTheSameRoundAsAValidBlockIsForABlockConsistentWithTheValidBlockHelper1(s, hSender1);
                assert prep.preparePayload.unsignedPayload.digest == cm1.commitPayload.unsignedPayload.digest;

                // assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s);
                // assert liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStatePrepareSentOnlyIfAcceptedProposal)(s);
                // assert invInstrNodeStatePrepareSentOnlyIfAcceptedProposal(s.nodes[hSender1]);           


                // var pm' :| 
                //     && pm' in s.nodes[hSender1].proposalsAccepted
                //     &&  
                //         var cuPayload := prep.preparePayload.unsignedPayload;
                //         var puPayload := pm'.proposalPayload.unsignedPayload;
                //     &&  puPayload.height == cuPayload.height
                //     &&  puPayload.round == cuPayload.round
                //     &&  digest(pm'.proposedBlock) == cuPayload.digest;
                //     // &&  signHash(hashBlockForCommitSeal(pm'.proposedBlock), s.nodes[hSender1].nodeState.id) == cuPayload.commitSeal;  


                // assert forall pm'' |    && pm'' in s.nodes[hSender1].proposalsAccepted
                //                         &&  var uPayload1 := pm'.proposalPayload.unsignedPayload;
                //                             var uPayload2 := pm''.proposalPayload.unsignedPayload;
                //                         && uPayload1.height == uPayload2.height
                //                         && uPayload1.round == uPayload2.round
                //                     ::
                //                         pm'.proposedBlock == pm''.proposedBlock; 

                // // assert pm'.proposalPayload.unsignedPayload.height <= |s.nodes[hSender1].nodeState.blockchain|;
                // // assert pm'.proposalPayload.unsignedPayload.height == |s.nodes[hSender1].nodeState.blockchain|;

                // assert isValidProposalJustification(pm', s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);
                // assert s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height] == s.nodes[n1].nodeState.blockchain[..h];
                // assert  isValidProposalJustification(pm', s.nodes[n1].nodeState.blockchain[..h]);
                // assert pm'.proposalPayload.unsignedPayload.round == r;
                // assert pm' in s.nodes[hSender1].nodeState.messagesReceived;
                // assert pm' in allMesssagesSentIncSentToItselfWithoutRecipient(s);
                // assert pm' in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent);
                // assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm'.proposedBlock);
                // assert digest(pm'.proposedBlock) == d;
                assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');

                // // assert forall b':Block |
                // //             digest(b) == d 
                // //         ::
                // //         areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');


                // // assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, bm.block);

                // // if(validInstrDSStateEx(s))
                // // {
                    
                // // } 

            }
        }
    }        


    lemma lemmaEQuorumOfCommitSealsHelper1(
        s: InstrDSState,
        n: Address
    )
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires isInstrNodeHonest(s, n)
    ensures invRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(s.nodes[n]);
    {}

    // 10s 3.2.0
    lemma lemmaInvTheHighestRoundChangeInAValidProposalForRoundHigherThanThatOfAValidBlockHasRoundAtLeastAsHighAsThatOfTheValidBlock(
        s: InstrDSState,
        b: Block,
        r: nat,
        h:nat, 
        pm: QbftMessage,
        n1: Address,
        rcm: SignedRoundChange
    )
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s)  
    requires isInstrNodeHonest(s,n1)  
    requires    |s.nodes[n1].nodeState.blockchain| >= h
    requires    proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])  
    ensures invTheHighestRoundChangeInAValidProposalForRoundHigherThanThatOfAValidBlockHasRoundAtLeastAsHighAsThatOfTheValidBlock(s, b, r, h, pm, n1, rcm)  
    {
        if  && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b)
            && b.header.roundNumber == r    
            && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
            && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
            && pm.proposalPayload.unsignedPayload.round > r
            && rcm in pm.proposalJustification
            && isHighestPrepared(rcm,pm.proposalJustification)
        {
            lemmaValidatorsAreTheSameOfTheGenesisBlock();
            lemmaDigest();
            lemmaSignedRoundChange();
            lemmaSignedPrepare();
            lemmaGetSetOfSignedPayloads();

            assert pm.proposalJustification <= extractSignedRoundChangesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s));

            var V := validators(s.nodes[n1].nodeState.blockchain[..h]);
            assert V == validators([s.configuration.genesisBlock]);
            assert isUniqueSequence(V);
            var Vset := seqToSet(V);
            var block1 := b;
            var bhash1 := hashBlockForCommitSeal(block1);
            var css1 := block1.header.commitSeals;
            var cssAuth1 := getCommitSealAuthors(bhash1, css1);
            lemmaOnSizeOfSetOfCommitSeals(bhash1, css1);
            assert |cssAuth1| == |css1|;
            var rcSenders := getSetOfRoundChangeSenders(pm.proposalJustification);
            assert |rcSenders| >= quorum(|V|);
            assert |css1| >= quorum(|V|);
            lUniqueSeq(V);
            assert |Vset| == |V|;
            lemmaQuorumIntersection(Vset, s.adversary.byz, rcSenders, cssAuth1);
            var hInInt :| hInInt in (rcSenders * cssAuth1 * (Vset - s.adversary.byz));
            assert isInstrNodeHonest(s,hInInt);
            assert hInInt in rcSenders && hInInt in cssAuth1;
            // var hrc :| hrc in rcs && recoverSignedRoundChangeAuthor(hrc) == hInInt;
            // var hrcPayload := hrc.unsignedPayload;
            // assert hrcPayload.round == bm.block.header.roundNumber+1;
            var cs1 :|  && cs1 in css1
                    && recoverSignedHashAuthor(bhash1, cs1) == hInInt; 
            assert cs1 in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s)); 
            assert isInstrNodeHonest(s, hInInt);
            // assert hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(block1), cs1);
            // var b1 :| hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(b1), cs1);
            

            // assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeStateTypes)(s);
            // assert invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s);
            assert  && cs1 in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                    && isInstrNodeHonest(s, hInInt)
                    && hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(block1), cs1);
            // deducePHelper(s,block1,cs1,hInInt);
            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block1,hInInt);

            var cm1, b1', p1 := lemmaGetCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block1,cs1,hInInt);


            // // // // assert hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
            assert    
                && cm1 in getAllMessagesSentByTheNode(s, hInInt)
                && p1 in s.nodes[hInInt].proposalsAccepted
                && p1.Proposal?
                && p1.proposedBlock == b1'
                && areBlocksTheSameExceptForTheCommitSeals(p1.proposedBlock,block1)
                && cm1.Commit?
                && cm1.commitPayload.unsignedPayload.height == block1.header.height
                && cm1.commitPayload.unsignedPayload.round == block1.header.roundNumber
                && cm1.commitPayload.unsignedPayload.digest == digest(b1');   

            var hsrc :| hsrc in pm.proposalJustification && recoverSignedRoundChangeAuthor(hsrc) == hInInt;
            assert hsrc.unsignedPayload.round == pm.proposalPayload.unsignedPayload.round;
            var hsrcPayload := hsrc.unsignedPayload;

            lemmaExtractSignedRoundChangeEx(allMesssagesSentIncSentToItselfWithoutRecipient(s), hsrc, hInInt);
            assert SignedRoundChangePayload(hsrc) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), hInInt);
            // assert SignedRoundChangePayload(hsrc) in getSetOfSignedPayloads(allMessagesSentBy(allMessagesSentWithoutRecipient(s.environment),hInInt));
            // assert SignedRoundChangePayload(hsrc) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hInInt)),hInInt);
            // assert SignedRoundChangePayload(hsrc) in getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt].messagesSent));
            // // var hrc :| hrc in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt].messagesSent) &&
            // //             hrc.RoundChange? &&
            // //             hrc.roundChangePayload == hsrc;

            // // // // assert hrc in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt].messagesSent);

            assert SignedRoundChangePayload(hsrc) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,hInInt)), hInInt);

            // var hrc := ldklfjaklfja(hsrc, getAllMessagesSentByTheNode(s,hInInt), hInInt);

            var hrc :|  hrc in getAllMessagesSentByTheNode(s, hInInt) &&  hrc.RoundChange? && hrc.roundChangePayload == hsrc;   

            assert hrc.roundChangePayload.unsignedPayload.height == cm1.commitPayload.unsignedPayload.height;
            assert hrc.roundChangePayload.unsignedPayload.round > cm1.commitPayload.unsignedPayload.round;
            assert cm1 in getAllMessagesSentByInsrNodeState(s.nodes[hInInt]);
            assert hrc in getAllMessagesSentByInsrNodeState(s.nodes[hInInt]);
        
            lemmaEQuorumOfCommitSealsHelper1(s, hInInt);
            // // assert invRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(s.nodes[hInInt]);
            var ucPayload := cm1.commitPayload.unsignedPayload;
            assert hsrcPayload.preparedRound.Optional?;

            // // assert hsrcPayload.preparedValue.Optional?;  
            assert hsrcPayload.preparedRound.value >= ucPayload.round; 

            assert rcm.unsignedPayload.preparedRound.Optional?;    
            assert rcm.unsignedPayload.preparedRound.value >= r;
        }
    }

    // 7s 3.2.0
    lemma lemmaInvAValidProposalForRoundHigherThanThatOfAValidBlockContainsAtLeastOneRoundChangeMessageWithNoNullPreparedRoundAndValue(
        s: InstrDSState,
        b: Block,
        r: nat,
        h:nat, 
        pm: QbftMessage,
        n1: Address
    )
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s)  
    requires isInstrNodeHonest(s,n1)  
    requires    |s.nodes[n1].nodeState.blockchain| >= h
    requires    proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])    
    ensures invAValidProposalForRoundHigherThanThatOfAValidBlockContainsAtLeastOneRoundChangeMessageWithNoNullPreparedRoundAndValue(s, b, r, h, pm, n1)
    {
        if  && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b)
            && b.header.roundNumber == r    
            && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
            && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
            && pm.proposalPayload.unsignedPayload.round > r
        {
            lemmaValidatorsAreTheSameOfTheGenesisBlock();
            lemmaDigest();
            lemmaSignedRoundChange();
            lemmaSignedPrepare();
            lemmaGetSetOfSignedPayloads();

            assert pm.proposalJustification <= extractSignedRoundChangesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s));

            var V := validators(s.nodes[n1].nodeState.blockchain[..h]);
            assert V == validators([s.configuration.genesisBlock]);
            assert isUniqueSequence(V);
            var Vset := seqToSet(V);
            var block1 := b;
            var bhash1 := hashBlockForCommitSeal(block1);
            var css1 := block1.header.commitSeals;
            var cssAuth1 := getCommitSealAuthors(bhash1, css1);
            lemmaOnSizeOfSetOfCommitSeals(bhash1, css1);
            assert |cssAuth1| == |css1|;
            var rcSenders := getSetOfRoundChangeSenders(pm.proposalJustification);
            assert |rcSenders| >= quorum(|V|);
            assert |css1| >= quorum(|V|);
            lUniqueSeq(V);
            assert |Vset| == |V|;
            lemmaQuorumIntersection(Vset, s.adversary.byz, rcSenders, cssAuth1);
            var hInInt :| hInInt in (rcSenders * cssAuth1 * (Vset - s.adversary.byz));
            assert isInstrNodeHonest(s,hInInt);
            assert hInInt in rcSenders && hInInt in cssAuth1;
            // var hrc :| hrc in rcs && recoverSignedRoundChangeAuthor(hrc) == hInInt;
            // var hrcPayload := hrc.unsignedPayload;
            // assert hrcPayload.round == bm.block.header.roundNumber+1;
            var cs1 :|  && cs1 in css1
                    && recoverSignedHashAuthor(bhash1, cs1) == hInInt; 
            assert cs1 in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s)); 
            assert isInstrNodeHonest(s, hInInt);
            // assert hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(block1), cs1);
            // var b1 :| hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(b1), cs1);
            

            // assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeStateTypes)(s);
            // assert invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s);
            assert  && cs1 in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                    && isInstrNodeHonest(s, hInInt)
                    && hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(block1), cs1);
            // deducePHelper(s,block1,cs1,hInInt);
            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block1,hInInt);

            var cm1, b1', p1 := lemmaGetCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,block1,cs1,hInInt);


            // // // // assert hInInt == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
            assert    
                && cm1 in getAllMessagesSentByTheNode(s, hInInt)
                && p1 in s.nodes[hInInt].proposalsAccepted
                && p1.Proposal?
                && p1.proposedBlock == b1'
                && areBlocksTheSameExceptForTheCommitSeals(p1.proposedBlock,block1)
                && cm1.Commit?
                && cm1.commitPayload.unsignedPayload.height == block1.header.height
                && cm1.commitPayload.unsignedPayload.round == block1.header.roundNumber
                && cm1.commitPayload.unsignedPayload.digest == digest(b1');   

            var hsrc :| hsrc in pm.proposalJustification && recoverSignedRoundChangeAuthor(hsrc) == hInInt;
            assert hsrc.unsignedPayload.round == pm.proposalPayload.unsignedPayload.round;
            var hsrcPayload := hsrc.unsignedPayload;

            lemmaExtractSignedRoundChangeEx(allMesssagesSentIncSentToItselfWithoutRecipient(s), hsrc, hInInt);
            assert SignedRoundChangePayload(hsrc) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), hInInt);
            // assert SignedRoundChangePayload(hsrc) in getSetOfSignedPayloads(allMessagesSentBy(allMessagesSentWithoutRecipient(s.environment),hInInt));
            // assert SignedRoundChangePayload(hsrc) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, hInInt)),hInInt);
            // assert SignedRoundChangePayload(hsrc) in getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt].messagesSent));
            // // var hrc :| hrc in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt].messagesSent) &&
            // //             hrc.RoundChange? &&
            // //             hrc.roundChangePayload == hsrc;

            // // // assert hrc in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[hInInt].messagesSent);

            assert SignedRoundChangePayload(hsrc) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,hInInt)), hInInt);

            // var hrc := ldklfjaklfja(hsrc, getAllMessagesSentByTheNode(s,hInInt), hInInt);

            var hrc :|  hrc in getAllMessagesSentByTheNode(s, hInInt) &&  hrc.RoundChange? && hrc.roundChangePayload == hsrc;   

            assert hrc.roundChangePayload.unsignedPayload.height == cm1.commitPayload.unsignedPayload.height;
            assert hrc.roundChangePayload.unsignedPayload.round > cm1.commitPayload.unsignedPayload.round;
            assert cm1 in getAllMessagesSentByInsrNodeState(s.nodes[hInInt]);
            assert hrc in getAllMessagesSentByInsrNodeState(s.nodes[hInInt]);
        
            // // // assert invRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(s.nodes[hInInt]);
            lemmaEQuorumOfCommitSealsHelper1(s, hInInt);
            var ucPayload := cm1.commitPayload.unsignedPayload;
            assert hsrcPayload.preparedRound.Optional?;

            assert   !((forall m | m in pm.proposalJustification :: && !optionIsPresent(m.unsignedPayload.preparedRound)
                                                        && !optionIsPresent(m.unsignedPayload.preparedValue)));

            // // // assert hsrcPayload.preparedValue.Optional?;  
            // assert hsrcPayload.preparedRound.value >= ucPayload.round; 

            // assert rcm.unsignedPayload.preparedRound.Optional?;    
            // assert rcm.unsignedPayload.preparedRound.value >= r;
        }
    }     

    // 3s 3.2.0
    lemma lemmaInvAnyValidProposalMessageWithRoundHigherThanThatOfAValidBlockIsForABlockConsistentWithTheValidBlock(
        s: InstrDSState,
        h: nat,
        r: nat,
        r2: nat,
        n1: Address,
        b: Block
    )
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires invProposalAcceptedByHonestNodesHaveBeenSent(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s)
    requires isInstrNodeHonest(s,n1)
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])     
    ensures invAnyValidProposalMessageWithRoundHigherThanThatOfAValidBlockIsForABlockConsistentWithTheValidBlock(s, h, r, r2, n1, b) 
    {
        if  && r2 >= r
            && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h], b)
            && b.header.roundNumber == r
        {
            if r2 == r
            {
                assert pAnyValidProposalMessageForTheProvidedRoundRangeIsForABlockConsistentWithTheProvidedBlock(r2, s, s.nodes[n1].nodeState.blockchain[..h], r, b); 
            }
            else  if r2 == r + 1
            {
                lemmaInvValidBlockAndBlockIncludedInValidPropsosalForNextRoundAreTheSameExceptForCommitSeals(s, h , n1);
                // assert lemmaCCp2(r2, s, s.nodes[n1].nodeState.blockchain[..h], r, bm); 
                assert  pAnyValidProposalMessageForTheProvidedRoundIsForABlockConsistentWithTheProvidedBlock(s, r2, s.nodes[n1].nodeState.blockchain[..h], b);
                assert pAnyValidProposalMessageForTheProvidedRoundRangeIsForABlockConsistentWithTheProvidedBlock(r2, s, s.nodes[n1].nodeState.blockchain[..h], r, b); 
            }
            else
            {
                lemmaInvAnyValidProposalMessageWithRoundHigherThanThatOfAValidBlockIsForABlockConsistentWithTheValidBlock(s, h, r, r2-1, n1, b);

                assert pAnyValidProposalMessageForTheProvidedRoundRangeIsForABlockConsistentWithTheProvidedBlock(r2-1, s, s.nodes[n1].nodeState.blockchain[..h], r, b);

                forall pm: QbftMessage |
                            && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
                            && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                            && pm.proposalPayload.unsignedPayload.round == r2
                ensures && areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm.proposedBlock)   
                    && pm.proposedBlock.header.roundNumber == r2
                {
                    
                    axiomRawValidatorsNeverChange();
                    lemmaDigest();
                    lemmaSignedRoundChange();
                    lemmaSignedPrepare();
                    lemmaGetSetOfSignedPayloads();                

                    assert pm.proposalJustification <= extractSignedRoundChangesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s));

                    lemmaInvAValidProposalForRoundHigherThanThatOfAValidBlockContainsAtLeastOneRoundChangeMessageWithNoNullPreparedRoundAndValue(s, b, r, h, pm, n1);

                    var validators := validators(s.nodes[n1].nodeState.blockchain[..h]);

                    var rcm :|  && rcm in pm.proposalJustification
                                && isHighestPrepared(rcm,pm.proposalJustification)
                                && (forall prep | prep in pm.roundChangeJustification :: 
                                                    validSignedPrepareForHeightRoundAndDigest(
                                                        prep,
                                                        h,
                                                        optionGet(rcm.unsignedPayload.preparedRound),
                                                        optionGet(rcm.unsignedPayload.preparedValue),
                                                        validators
                                                    ));    

                    var proposedBlockWithOldRound := 
                                    replaceRoundInBlock(
                                        pm.proposedBlock,
                                        optionGet(rcm.unsignedPayload.preparedRound));    

                    assert  optionGet(rcm.unsignedPayload.preparedValue) == digest(proposedBlockWithOldRound);



                    lemmaInvTheHighestRoundChangeInAValidProposalForRoundHigherThanThatOfAValidBlockHasRoundAtLeastAsHighAsThatOfTheValidBlock(s, b, r, h, pm, n1, rcm);

                    assert rcm.unsignedPayload.preparedRound.Optional?
                    && rcm.unsignedPayload.preparedRound.value >= r;

                    assert rcm.unsignedPayload.preparedRound.value < r2;

                    assert inclusiveRange(r, rcm.unsignedPayload.preparedRound.value, r2-1);

                    if rcm.unsignedPayload.preparedRound.value > r 
                    {
                        assert pAnyValidProposalMessageForTheProvidedRoundIsForABlockConsistentWithTheProvidedBlock(s, rcm.unsignedPayload.preparedRound.value, s.nodes[n1].nodeState.blockchain[..h], b);

                        lemmaInvIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidQuorumOfPreparesForTheSameRoundIsAlsoConsistentWithThatBlock(s, rcm.unsignedPayload.preparedRound.value, h, n1, b);

                        assert pm.roundChangeJustification <= extractSignedPreparesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s));

                        assert |pm.roundChangeJustification| >= quorum(|validators|);

                        assert (forall prep | prep in pm.roundChangeJustification :: 
                                                    validSignedPrepareForHeightRoundAndDigest(
                                                        prep,
                                                        h,
                                                        rcm.unsignedPayload.preparedRound.value,
                                                        digest(proposedBlockWithOldRound),
                                                        validators
                                                    ));

                        assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, proposedBlockWithOldRound);

                        assert areBlocksTheSameExceptForTheCommitSealsAndRound(proposedBlockWithOldRound, pm.proposedBlock);

                        assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm.proposedBlock);
                    }
                    else
                    {
                        assert (forall prep | prep in pm.roundChangeJustification :: 
                                                    validSignedPrepareForHeightRoundAndDigest(
                                                        prep,
                                                        h,
                                                        r,
                                                        digest(proposedBlockWithOldRound),
                                                        validators
                                                    ));  

                        lemmaInvAnyValidQuorumOfPreparesForTheSameRoundAsAValidBlockIsForABlockConsistentWithTheValidBlock(s, h, n1, b);    
                        assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, proposedBlockWithOldRound);

                        assert areBlocksTheSameExceptForTheCommitSealsAndRound(proposedBlockWithOldRound, pm.proposedBlock);

                        assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm.proposedBlock);                
                    }



                        // assert && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, pm.proposedBlock)   
                        // && pm.proposedBlock.header.roundNumber == r2;
                    // var r' :| r <= r' < r2;
                    // assert p(s, r', s.nodes[n1].nodeState.blockchain[..h], bm);
                    // assume areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, bm'.block);
                }            
                assert  pAnyValidProposalMessageForTheProvidedRoundIsForABlockConsistentWithTheProvidedBlock(s, r2, s.nodes[n1].nodeState.blockchain[..h], b);

                assert pAnyValidProposalMessageForTheProvidedRoundRangeIsForABlockConsistentWithTheProvidedBlock(r2, s, s.nodes[n1].nodeState.blockchain[..h], r, b);

            }
        }
    }    

    // 3s 3.2.0
    lemma lemmaInvAnyValidBlockForRoundAtLeastAsHighAsThatOfAValidBlockIsConsistentWithTheValidBlock(
        s: InstrDSState,
        b: Block,
        r: nat,
        r2: nat,
        h:nat, 
        n1: Address
    )
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires invProposalAcceptedByHonestNodesHaveBeenSent(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s) 
    requires isInstrNodeHonest(s,n1)  
    requires    |s.nodes[n1].nodeState.blockchain| >= h
    requires    proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])    
    ensures invAnyValidBlockForRoundAtLeastAsHighAsThatOfAValidBlockIsConsistentWithTheValidBlock(s, b, r, r2, h, n1)
    {
        if  && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b)
            && b.header.roundNumber == r    
            && r2 >= r
        {
            // axiomRawValidatorsNeverChange();
            // lemmaDigest();
            // lemmaSignedRoundChange();
            // lemmaSignedPrepare();
            // lemmaGetSetOfSignedPayloads();
            lemmaInvAnyValidProposalMessageWithRoundHigherThanThatOfAValidBlockIsForABlockConsistentWithTheValidBlock(s, h, r, r2, n1, b);
            forall b':Block | 
                        &&  b'.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                        && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b') 
                        &&  r <= b'.header.roundNumber <= r2  
            ensures areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
            {
                var r' := b'.header.roundNumber;
                if r' == r 
                {
                    lemmaInvTwoValidQuorumOfCommitSealsForSameRoundAreForTheSameBlockExceptForCommitSealsNotForAll(
                        s,
                        b,
                        b',
                        n1,
                        n1,
                        h
                        );
                    assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
                }
                else {
                    assert inclusiveRange(r+1, r', r2);
                    assert pAnyValidProposalMessageForTheProvidedRoundIsForABlockConsistentWithTheProvidedBlock(s, r', s.nodes[n1].nodeState.blockchain[..h], b);
                    lemmaInvIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidBlockForTheSameRoundIsAlsoConsistentWithThatBlock(s, h, r', n1, b);
                    assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
                }
            } 
        }
    }      

    lemma lemmaInvAnyTwoValidNewBlockMessagesForTheSameHeightAreConsistent(
        s: InstrDSState,
        bm: QbftMessage,
        bm': QbftMessage,
        h:nat, 
        n1: Address
    ) 
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires invProposalAcceptedByHonestNodesHaveBeenSent(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s) 
    requires isInstrNodeHonest(s,n1)  
    requires    |s.nodes[n1].nodeState.blockchain| >= h
    requires    proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])    
    ensures invAnyTwoValidNewBlockMessagesForTheSameHeightAreConsistent(s, bm, bm', h, n1)
    {
        if  && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
            && validNewBlockMessage(s.nodes[n1].nodeState.blockchain[..h],bm)
            && bm' in allMesssagesSentIncSentToItselfWithoutRecipient(s)
            && validNewBlockMessage(s.nodes[n1].nodeState.blockchain[..h],bm')
        {
            lemmaInvAnyTwoValidNewBlockMessagesWithCommitSealsIncludedInAllCommitSealsSentForTheSameHeightAreConsistent(
                s,
                bm.block,
                bm'.block,
                h,
                n1
            );
        }
    }   
    
    // 2s 3.2.0
    lemma lemmaInvAnyTwoValidNewBlockMessagesWithCommitSealsIncludedInAllCommitSealsSentForTheSameHeightAreConsistent(
        s: InstrDSState,
        b: Block,
        b': Block,
        h:nat, 
        n1: Address
    ) 
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires invProposalAcceptedByHonestNodesHaveBeenSent(s)
    requires pBlockchainConsistencyUpToHeight(s, h)
    requires invConstantFields(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)  
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s) 
    requires isInstrNodeHonest(s,n1)  
    requires    |s.nodes[n1].nodeState.blockchain| >= h
    requires    proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h]) 
    ensures invAnyTwoValidNewBlockMessagesWithCommitSealsIncludedInAllCommitSealsSentForTheSameHeightAreConsistent(s, b, b', h, n1)   
    {
        if  && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b)
            && b'.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b')
        {
            if b.header.roundNumber <= b'.header.roundNumber
            {
                lemmaInvAnyValidBlockForRoundAtLeastAsHighAsThatOfAValidBlockIsConsistentWithTheValidBlock(s, b, b.header.roundNumber, b'.header.roundNumber, h, n1);
                assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
            }
            else
            {
                lemmaInvAnyValidBlockForRoundAtLeastAsHighAsThatOfAValidBlockIsConsistentWithTheValidBlock(s, b', b'.header.roundNumber, b.header.roundNumber, h, n1);
                assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
            }
        }
    }     

    lemma lemmaInvIfRoundChangePaylodSentThenRoundChangeSentSingleNodeHelper1(
        S: set<QbftMessage>,
        S2: set<QbftMessage>,
        S3: set<QbftMessage>,
        S4: set<QbftMessage>,
        srcp: SignedPayload,
        node: Address
    )
    requires forall m | m in S :: m.Proposal? 
    requires forall m | m in S :: 
                    m.proposalJustification <= extractSignedRoundChangesEx(S2)
    requires && srcp.SignedRoundChangePayload? 
                        && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S), node) 
    requires S2 == S3 + S4  
    ensures    srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S2), node);     
    ensures     || srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S3), node)
                || srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S4), node);                 
    {
        lemmaGetSetOfSignedPayloads();
        lemmaSignedRoundChange();
        assert srcp in getSetOfSignedPayloads(S2);
        assert srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S2), node);
        assert  || srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S3), node)
                || srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S4), node);     
    }      

    // 230 sec Resolved Inconclusive
    lemma lemmaInvIfRoundChangePaylodSentThenRoundChangeSentSingleNode(
        s:InstrDSState, 
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )    
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires isInstrNodeHonest(s,node)
    requires InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)     
    ensures invIfRoundChangePaylodSentThenRoundChangeSentSingleNode(s', node)
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();   
        lemmaGetSetOfSignedPayloads();

        var sForSubsteps, newMessagesReceived, newMessagesSentToItself := 
            lemmaFromDSInstrNextNodeNodeNextSubStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);        

        var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

        // assert
        //     forall srcp: SignedPayload | 
        //         && srcp.SignedRoundChangePayload? 
        //         && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(messagesReceivedByTheNodes)), node) 
        //         ::
        //         srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[node].messagesSent)), node); 


        var currentForSubsteps := sForSubsteps.nodes[node].nodeState;
        //     current.nodeState.(
        //         messagesReceived := newMessagesReceived,
        //         localTime := next.nodeState.localTime
        //     );

        var nextForSubsteps := s'.nodes[node].nodeState;

        var newSentMessages := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) +
                newMessagesSentToItself;        

        assert getAllMessagesSentByTheNode(s',node) ==
                getAllMessagesSentByTheNode(s,node) +
                newSentMessages;

        if(     
                // || (currentForSubsteps == nextForSubsteps && outQbftMessages == {})
                || UponBlockTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponProposal(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponPrepare(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponCommit(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponNewBlock(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
        )
        {
            // 247s 3.2.0 This branch alone
            assert invIfRoundChangePaylodSentThenRoundChangeSentSingleNode(s', node);
            
        }         
        else if(     
                || UponRoundChange(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponRoundTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                )
        {


            assert
                forall srcp: SignedPayload | 
                    && srcp.SignedRoundChangePayload? 
                    && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(messagesReceivedByTheNodes)), node) 
                    ::
                    && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[node].messagesSent)), node);
                    // && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,node)), node); 

            assert
                forall srcp: SignedPayload | 
                    && srcp.SignedRoundChangePayload? 
                    && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), node) 
                    ::
                    && srcp in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,node))
                    && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,node)), node); 

            assert getAllMessagesSentByTheNode(s,node) <= getAllMessagesSentByTheNode(s',node);
            var dMessages := getAllMessagesSentByTheNode(s',node) - getAllMessagesSentByTheNode(s,node);

            assert sForSubsteps.nodes[node].nodeState.messagesReceived == s.nodes[node].nodeState.messagesReceived + fromMultisetQbftMessagesWithRecipientToSetOfMessages(messagesReceivedByTheNodes);

            // forall srcp: SignedPayload | 
            //         && srcp.SignedPreparePayload? 
            //         && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(dMessages), node)    
            // // ensures srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,node)), node);  
            // {

            // } 


            // assume forall rcs | rcs in extractSignedRoundChangesEx(fromMultisetQbftMessagesWithRecipientToSetOfMessages(messagesReceivedByTheNodes)) && recoverSignedRoundChangeAuthor(rcs) == node::
            //     SignedRoundChangePayload(rcs) in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[node].messagesSent)), node); 

            // assert getAllMessagesSentByTheNode(s,node) <= getAllMessagesSentByTheNode(s',node);
            // var dMessages := getAllMessagesSentByTheNode(s',node) - getAllMessagesSentByTheNode(s,node);

            // // assert |dMessages| <= 1;

            // // assert 
            // //     || (forall m | m in dMessages :: m.Proposal?)
            // //     || (forall m | m in dMessages :: m.RoundChange?);

            if (forall m | m in dMessages :: m.Proposal?)
            {
                assert forall m | m in dMessages :: 
                    m.proposalJustification <= extractSignedRoundChangesEx(currentForSubsteps.messagesReceived);

                forall srcp: SignedPayload | 
                        && srcp.SignedRoundChangePayload? 
                        && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(dMessages), node)    
                ensures srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,node)), node);         
                {
                    lemmaInvIfRoundChangePaylodSentThenRoundChangeSentSingleNodeHelper1(
                        dMessages, 
                        sForSubsteps.nodes[node].nodeState.messagesReceived, 
                        s.nodes[node].nodeState.messagesReceived ,
                        fromMultisetQbftMessagesWithRecipientToSetOfMessages(messagesReceivedByTheNodes),
                        srcp, 
                        node);
                    // assert srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(sForSubsteps.nodes[node].nodeState.messagesReceived), node);
                    assert 
                        || srcp in  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), node)
                        || srcp in  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(messagesReceivedByTheNodes)), node); 

                    assert
                    // //     || srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[node].messagesSent)), node)
                        || srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,node)), node);         
                }                
                

                assert invIfRoundChangePaylodSentThenRoundChangeSentSingleNode(s', node);                

            }
            else 
            if (forall m | m in dMessages :: m.RoundChange?)
            {
                // assert m in getAllMessagesSentByTheNode(s',node);
                forall srcp: SignedPayload | 
                        && srcp.SignedRoundChangePayload? 
                        && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(dMessages), node)  
                ensures 
                    exists rcm :: 
                                    && rcm in dMessages
                                    && rcm.RoundChange?
                                    && rcm.roundChangePayload == srcp.signedRoundChangePayload;                        
                {
                    assert  exists rcm :: 
                                && rcm in dMessages
                                && rcm.RoundChange?
                                && rcm.roundChangePayload == srcp.signedRoundChangePayload;
                //     assert 
                //         || srcp in  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), node)
                //         || srcp in  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(messagesReceivedByTheNodes)), node);                     
                } 
                assert invIfRoundChangePaylodSentThenRoundChangeSentSingleNode(s', node);
            }
            else
            {
                assert false;
            }               
        } 
        else if(currentForSubsteps == nextForSubsteps)
        {
            assert messagesSentByTheNodes == {};

            assert invIfRoundChangePaylodSentThenRoundChangeSentSingleNode(s', node);          
        }     
        else
        {
            // assert false;
        }                          
    }

    lemma lemmaInvIfRoundChangePaylodSentThenRoundChangeSent(
        s:InstrDSState, 
        s': InstrDSState
    )    
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invIfRoundChangePaylodSentThenRoundChangeSent(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires InstrDSNextSingle(s, s')     
    ensures invIfRoundChangePaylodSentThenRoundChangeSent(s')
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

   
            if isInstrNodeHonest(s,node)
            {
                var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

                assert messagesReceivedByTheNodes <= s.environment.allMessagesSent;

                assert forall n | 
                    && isInstrNodeHonest(s', n) 
                    && n != node
                    ::
                    getAllMessagesSentByTheNode(s,n) == getAllMessagesSentByTheNode(s',n);

                assert forall n | 
                    && isInstrNodeHonest(s', n) 
                    && n != node
                    ::
                    invIfRoundChangePaylodSentThenRoundChangeSentSingleNode(s', n);                    

                lemmaInvIfRoundChangePaylodSentThenRoundChangeSentSingleNode(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                assert invIfRoundChangePaylodSentThenRoundChangeSent(s');

            }
            else
            {
                assert invIfRoundChangePaylodSentThenRoundChangeSent(s');
            }
        }
    }   

    lemma lemmaInvIfPreparePaylodSentThenPrepareSentSingleNodeHelper1(
        S: set<QbftMessage>,
        S2: set<QbftMessage>,
        S3: set<QbftMessage>,
        S4: set<QbftMessage>,
        srcp: SignedPayload,
        node: Address
    )
    requires forall m | m in S :: m.Proposal? || m.RoundChange?
    requires forall m | m in S :: 
                    m.roundChangeJustification <= extractSignedPreparesEx(S2);
    requires && srcp.SignedPreparePayload? 
                        && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S), node) 
    requires S2 == S3 + S4  
    ensures    srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S2), node);     
    ensures     || srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S3), node)
                || srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S4), node);                 
    {
        lemmaGetSetOfSignedPayloads();
        lemmaSignedPrepare();
        assert srcp in getSetOfSignedPayloads(S2);
        assert srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S2), node);
        assert  || srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S3), node)
                || srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(S4), node);     
    }

    // 162s Resolved Inconclusive
    lemma lemmaInvIfPreparePaylodSentThenPrepareSentSingleNode(
        s:InstrDSState, 
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )    
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires isInstrNodeHonest(s,node)
    requires InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)     
    ensures invIfPreparePaylodSentThenPrepareSentSingleNode(s', node)   
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();   
        lemmaGetSetOfSignedPayloads();

        var sForSubsteps, newMessagesReceived, newMessagesSentToItself := 
            lemmaFromDSInstrNextNodeNodeNextSubStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

        var currentForSubsteps := sForSubsteps.nodes[node].nodeState;

        var nextForSubsteps := s'.nodes[node].nodeState;

        var newSentMessages := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) +
                newMessagesSentToItself;        

        assert getAllMessagesSentByTheNode(s',node) ==
                getAllMessagesSentByTheNode(s,node) +
                newSentMessages;



        if(     
                // || (currentForSubsteps == nextForSubsteps && outQbftMessages == {})
                || UponProposal(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponBlockTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponPrepare(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponCommit(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponNewBlock(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
        )
        {
            // 62s 3.2.0 This branch alone

            assert invIfPreparePaylodSentThenPrepareSentSingleNode(s', node);
            
        }         
        else if(     
            
                || UponRoundChange(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponRoundTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                  
                )
        {
            assert
                forall srcp: SignedPayload | 
                    && srcp.SignedPreparePayload? 
                    && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(messagesReceivedByTheNodes)), node) 
                    ::
                    && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[node].messagesSent)), node);

            assert
                forall srcp: SignedPayload | 
                    && srcp.SignedPreparePayload? 
                    && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), node) 
                    ::
                    && srcp in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,node))
                    && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,node)), node); 

            assert getAllMessagesSentByTheNode(s,node) <= getAllMessagesSentByTheNode(s',node);
            var dMessages := getAllMessagesSentByTheNode(s',node) - getAllMessagesSentByTheNode(s,node);

            assert sForSubsteps.nodes[node].nodeState.messagesReceived == s.nodes[node].nodeState.messagesReceived + fromMultisetQbftMessagesWithRecipientToSetOfMessages(messagesReceivedByTheNodes);

            assert 
                || (forall m | m in dMessages :: m.Proposal? || m.RoundChange?);


            assert forall m | m in dMessages :: 
                m.roundChangeJustification <= extractSignedPreparesEx(currentForSubsteps.messagesReceived);

            forall srcp: SignedPayload | 
                    && srcp.SignedPreparePayload? 
                    && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(dMessages), node)    
            ensures srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,node)), node);         
            {
                lemmaInvIfPreparePaylodSentThenPrepareSentSingleNodeHelper1(
                    dMessages, 
                    sForSubsteps.nodes[node].nodeState.messagesReceived, 
                    s.nodes[node].nodeState.messagesReceived ,
                    fromMultisetQbftMessagesWithRecipientToSetOfMessages(messagesReceivedByTheNodes),
                    srcp, 
                    node);
                    
                assert 
                    || srcp in  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), node)
                    || srcp in  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(messagesReceivedByTheNodes)), node); 

                assert
                    || srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,node)), node);         
            }                
                
            assert invIfPreparePaylodSentThenPrepareSentSingleNode(s', node);             
        } 
        else if(currentForSubsteps == nextForSubsteps)
        {
            assert messagesSentByTheNodes == {};

            assert invIfPreparePaylodSentThenPrepareSentSingleNode(s', node);          
        }     
        else
        {
            // assert false;
        }                          
    } 

    lemma lemmaInvIfPreparePaylodSentThenPrepareSent(
        s:InstrDSState, 
        s': InstrDSState
    )    
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires InstrDSNextSingle(s, s')     
    ensures invIfPreparePaylodSentThenPrepareSent(s')
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

   
            if isInstrNodeHonest(s,node)
            {
                var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

                assert messagesReceivedByTheNodes <= s.environment.allMessagesSent;

                assert forall n | 
                    && isInstrNodeHonest(s', n) 
                    && n != node
                    ::
                    getAllMessagesSentByTheNode(s,n) == getAllMessagesSentByTheNode(s',n);

                assert forall n | 
                    && isInstrNodeHonest(s', n) 
                    && n != node
                    ::
                    invIfPreparePaylodSentThenPrepareSentSingleNode(s', n);                    

                lemmaInvIfPreparePaylodSentThenPrepareSentSingleNode(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                assert invIfPreparePaylodSentThenPrepareSent(s');

            }
            else
            {
                assert invIfPreparePaylodSentThenPrepareSent(s');
            }
        }
    } 

    lemma lemmaInvProposalAcceptedByHonestNodesHaveBeenSentHelper(
        s:InstrDSState, 
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )    
    requires validInstrDSState(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)    
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invMessagesReceivedByHonestNodesHaveBeenSent(s)
    requires invProposalAcceptedByHonestNodesHaveBeenSent(s)
    requires isInstrNodeHonest(s,node)
    requires InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)     
    ensures invProposalAcceptedByANodesHaveBeenSent(s', node)   
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();   
        lemmaGetSetOfSignedPayloads();

        var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

        var current := s.nodes[node];
        var next := s'.nodes[node];

        var newMessagesReceived := current.nodeState.messagesReceived + messageReceived;    

        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );

        assert invProposalAcceptedByANodesHaveBeenSent(s, node);

        var nextForSubsteps := next.nodeState;

        assert NodeNextSubStep(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes);

        if(     
                // || (currentForSubsteps == nextForSubsteps && outQbftMessages == {})
                || UponProposal(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)

        )
        {
            assert invProposalAcceptedByANodesHaveBeenSent(s', node);
            // assert invIfPreparePaylodSentThenPrepareSentSingleNode(s', node);
            
        }         
        else if(   
                || UponBlockTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)

                || UponCommit(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponPrepare(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)

                || UponNewBlock(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)              
                || UponRoundChange(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                || UponRoundTimeout(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes)
                )
        {
            assert invProposalAcceptedByANodesHaveBeenSent(s', node);

        } 
        else if(currentForSubsteps == nextForSubsteps && messagesSentByTheNodes == {})
        {
            // assert outQbftMessages == {};
            assert s.nodes[node].proposalsAccepted == s'.nodes[node].proposalsAccepted;
            assert invProposalAcceptedByANodesHaveBeenSent(s', node);
        }     
        else
        {
            assert invProposalAcceptedByANodesHaveBeenSent(s', node);
            // assert false;
        }                          
    }     

    lemma lemmaInvProposalAcceptedByHonestNodesHaveBeenSent(
        s:  InstrDSState, 
        s': InstrDSState
    )
    requires validInstrDSState(s)
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)   
    requires invMessagesReceivedByHonestNodesHaveBeenSent(s) 
    requires invProposalAcceptedByHonestNodesHaveBeenSent(s)
    requires InstrDSNextSingle(s,s') 
    ensures invProposalAcceptedByHonestNodesHaveBeenSent(s')
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
                lemmaInvProposalAcceptedByHonestNodesHaveBeenSentHelper(s, s', messagesSentByTheNodes,messagesReceivedByTheNodes, node);
                // assert forall n | isInstrNodeHonest(s, n) && n != node :: s.nodes[n].proposalsAccepted == s'.nodes[n].proposalsAccepted;
                // assert invProposalAcceptedByHonestNodesHaveBeenSent(s');

                assert forall n | isInstrNodeHonest(s, n) && n != node :: s.nodes[n].proposalsAccepted == s'.nodes[n].proposalsAccepted;
                assert forall n | isInstrNodeHonest(s, n) && n != node :: invProposalAcceptedByANodesHaveBeenSent(s', n);      
                assert invProposalAcceptedByHonestNodesHaveBeenSent(s');          

            }
            else
            {
                assert forall n | isInstrNodeHonest(s, n) :: s.nodes[n].proposalsAccepted == s'.nodes[n].proposalsAccepted;
                assert forall n | isInstrNodeHonest(s, n) :: invProposalAcceptedByANodesHaveBeenSent(s', n);
                assert invProposalAcceptedByHonestNodesHaveBeenSent(s');
            }
        }
        else
        {
            assert invProposalAcceptedByHonestNodesHaveBeenSent(s');
        }
                
    }      

    // TODO: Rename
    lemma lemmaIndInvForConsistency(
        s: InstrDSState,
        s': InstrDSState
    )
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invBlockchainConsistency(s)
    requires InstrDSNextSingle(s,s')  
    ensures indInvForConsistency(s')
    {
        lemmaIndInvInstrNodeStateLifterToInstrDSState(s, s');
        lemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s, s');
        lemmaInvAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, s');
        lemmaInvNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s, s');
        lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s, s');
        lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s, s');
        lemmaInvallSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s, s');
        lemmaInvProposalAcceptedByHonestNodesHaveBeenSent(s, s');
        lemmaInvIfPreparePaylodSentThenPrepareSent(s, s');
        lemmaInvIfRoundChangePaylodSentThenRoundChangeSent(s, s');
        lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s, s');
        lemmaMessagesReceivedByHonestNodesHaveBeenSent(s, s');

    }
}