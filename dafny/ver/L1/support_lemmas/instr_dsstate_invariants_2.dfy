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
include "instr_dsstate_invariants_defs.dfy"
include "instr_dsstate_invariants_1.dfy"
include "networking_invariants.dfy"
include "networking_step_lemmas.dfy"
include "instr_node_state_invariants.dfy"
include "quorum.dfy" 
include "general_lemmas.dfy"
include "../theorems_defs.dfy"


module EEAInstrDSStateInvariantsNew
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
    import opened EEAInstrDSStateInvariantsHeavy
    import opened EEANetworkingInvariantsLemmas 
    import opened EEATheoremsDefs


    // 6s 3.2.0
    lemma lemmaInvTheProposerInAnyValidProposalUpToTheGivenRoundIsInTheSetOfValidators(
        s: InstrDSState,
        h: nat,
        r2: nat,
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
    requires isInstrNodeHonest(s,n1)
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires h > 0
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])     
    ensures invTheProposerInAnyValidProposalUpToTheGivenRoundIsInTheSetOfValidators(r2, s, s.nodes[n1].nodeState.blockchain[..h]); 
    {
        if r2 == 0
        {
            assert invTheProposerInAnyValidProposalUpToTheGivenRoundIsInTheSetOfValidators(r2, s, s.nodes[n1].nodeState.blockchain[..h]); 
        }
        else
        {
            lemmaInvTheProposerInAnyValidProposalUpToTheGivenRoundIsInTheSetOfValidators(s, h, r2-1, n1);
            assert invTheProposerInAnyValidProposalUpToTheGivenRoundIsInTheSetOfValidators(r2-1, s, s.nodes[n1].nodeState.blockchain[..h]); 

            forall 
                pm
                    |
                (
                    && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
                    && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                    && pm.proposalPayload.unsignedPayload.round == r2              
                )
            ensures 
                (
                    && pm.proposedBlock.header.proposer in validators(s.nodes[n1].nodeState.blockchain[..h])
                )
            {

                if (forall m | m in pm.proposalJustification :: 
                                    && !optionIsPresent(m.unsignedPayload.preparedRound)
                                    && !optionIsPresent(m.unsignedPayload.preparedValue))
                {
                    assert && pm.proposedBlock.header.proposer in validators(s.nodes[n1].nodeState.blockchain[..h]);
                }
                else
                {
                    axiomRawValidatorsNeverChange();
                    lemmaDigest();
                    lemmaSignedRoundChange();
                    lemmaSignedPrepare();
                    lemmaGetSetOfSignedPayloads();    

                    assert pm.proposalJustification <= extractSignedRoundChangesEx(allMesssagesSentIncSentToItselfWithoutRecipient(s));
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
                    assert rcm.unsignedPayload.preparedRound.Optional?;
                    assert 0 <= rcm.unsignedPayload.preparedRound.value < r2;
                    assert inclusiveRange(0, rcm.unsignedPayload.preparedRound.value, r2-1);

                    assert pTheProposerInAnyValidProposalForTheGivenRoundIsInTheSetOfValidators(s, rcm.unsignedPayload.preparedRound.value, s.nodes[n1].nodeState.blockchain[..h]);

                    lemmaInvIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockAnyValidQuorumOfPreparesForTheSameRoundIsForABlockWithProposerInTheSetOfValidators(s, rcm.unsignedPayload.preparedRound.value, h, n1);                    
                    // assert pm.proposedBlock.header.proposer

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

                    assert proposedBlockWithOldRound.header.proposer in validators;

                    assert pm.proposedBlock.header.proposer in validators;


                }
                

                assert && pm.proposedBlock.header.proposer in validators(s.nodes[n1].nodeState.blockchain[..h]);
            }

            assert pTheProposerInAnyValidProposalForTheGivenRoundIsInTheSetOfValidators(s, r2, s.nodes[n1].nodeState.blockchain[..h]);
            assert invTheProposerInAnyValidProposalUpToTheGivenRoundIsInTheSetOfValidators(r2-1, s, s.nodes[n1].nodeState.blockchain[..h]); 
        }
    }

    // 2s 3.2.0
    lemma lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper1(
        s: InstrDSState,
        s': InstrDSState,
        n: Address
    )
    requires validInstrDSStateEx(s)  
    requires InstrDSNextSingle(s,s') 
    requires isInstrNodeHonest(s, n) 
    ensures s.nodes[n].nodeState.blockchain <= s'.nodes[n].nodeState.blockchain;
    ensures |s.nodes[n].nodeState.blockchain| <= |s'.nodes[n].nodeState.blockchain| <= |s.nodes[n].nodeState.blockchain| + 1;
    {
        assert s.nodes[n].nodeState.blockchain <= s'.nodes[n].nodeState.blockchain;
    } 


    // 1s 3.2.0
    lemma lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper2(
        s: InstrDSState,
        s': InstrDSState,
        bm: QbftMessage,
        blockchain: Blockchain  
    ) returns (cm1: QbftMessage, b1': Block, p1: QbftMessage, hSender1: Address)
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invBlockchainConsistency(s)
    requires InstrDSNextSingle(s, s')
    requires validNewBlockMessage(blockchain, bm)
    requires    
                var newSentMessages := allMesssagesSentIncSentToItselfWithoutRecipient(s') - allMesssagesSentIncSentToItselfWithoutRecipient(s);
                && bm in newSentMessages    
    ensures 
            && isInstrNodeHonest(s, hSender1) 
            && cm1 in getAllMessagesSentByTheNode(s', hSender1)
            && p1.Proposal?
            && p1 in s'.nodes[hSender1].proposalsAccepted
            && p1.proposedBlock == b1'
            && areBlocksTheSameExceptForTheCommitSeals(b1',bm.block)
            && cm1.Commit?
            && cm1.commitPayload.unsignedPayload.height == bm.block.header.height
            && cm1.commitPayload.unsignedPayload.round == bm.block.header.roundNumber
            && cm1.commitPayload.unsignedPayload.digest == digest(b1');                     
    {
        axiomRawValidatorsNeverChange();
        lemmaIndInvForConsistency(s, s');
        lemmaDigest();        
        // assert isInstrNodeHonest(s, n);
        // assert s.nodes[n].nodeState.blockchain == s'.nodes[n].nodeState.blockchain;
        var V := validators(blockchain);
        assert V == validators([s.configuration.genesisBlock]);
        assert isUniqueSequence(V);
        var Vset := seqToSet(V);
        lUniqueSeq(V);
        var block1 := bm.block;  
        var bhash1 := hashBlockForCommitSeal(block1);
        var css1 := block1.header.commitSeals;
        var cssAuth1 := getCommitSealAuthors(bhash1, css1);
        lemmaOnSizeOfSetOfCommitSeals(bhash1, css1);
        assert |cssAuth1| == |css1|;   
        lemmaThereExistsAnHonestInQuorum(Vset, s.adversary.byz, cssAuth1);      
        hSender1 :|
            && hSender1 in cssAuth1
            && isInstrNodeHonest(s, hSender1); 

        var cs1 :|  && cs1 in css1
            && recoverSignedHashAuthor(bhash1, cs1) == hSender1;  

        assert cs1 in getCommitSeals((allMesssagesSentIncSentToItselfWithoutRecipient(s')));
        assert isInstrNodeHonest(s', hSender1);

        assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',block1,hSender1);  
        
        cm1, b1', p1 :|    
            && cm1 in getAllMessagesSentByTheNode(s', hSender1)
            && p1 in s'.nodes[hSender1].proposalsAccepted
            && p1.proposedBlock == b1'
            && areBlocksTheSameExceptForTheCommitSeals(b1',block1)
            && cm1.Commit?
            && cm1.commitPayload.unsignedPayload.height == block1.header.height
            && cm1.commitPayload.unsignedPayload.round == block1.header.roundNumber
            && cm1.commitPayload.unsignedPayload.digest == digest(b1');   
    }  

    // 11s 3.2.0
    lemma lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper3(
        s: InstrDSState,
        s': InstrDSState,
        bm: QbftMessage,
        blockchain: Blockchain  
    ) returns (pm': QbftMessage, hSender1: Address, b1': Block)
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invBlockchainConsistency(s)
    requires InstrDSNextSingle(s, s')
    requires validNewBlockMessage(blockchain, bm)
    requires    
                var newSentMessages := allMesssagesSentIncSentToItselfWithoutRecipient(s') - allMesssagesSentIncSentToItselfWithoutRecipient(s);
                && bm in newSentMessages
    ensures 
                        && isInstrNodeHonest(s, hSender1)
                        && pm'.Proposal?
                        && pm' in s.nodes[hSender1].proposalsAccepted
                        &&  
                            var puPayload := pm'.proposalPayload.unsignedPayload;
                        &&  puPayload.height == bm.block.header.height
                        &&  puPayload.round == bm.block.header.roundNumber
                        &&  digest(pm'.proposedBlock) == digest(b1')   
                        && areBlocksTheSameExceptForTheCommitSeals(b1',bm.block)
    {
            axiomRawValidatorsNeverChange();
            lemmaIndInvForConsistency(s, s');
            lemmaDigest();

            var node :| isNodeThatTakesStep(s, s', node);

            var cm1: QbftMessage, p1: QbftMessage;
            cm1, b1', p1, hSender1 := lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper2(s, s', bm, blockchain);  
            pm' :| true;        

            var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node);     

            var cuPayload := cm1.commitPayload.unsignedPayload;                              

            if isInstrNodeHonest(s,node)
            {        
                var sForSubsteps, newMessagesReceived, newMessagesSentToItself := lemmaFromDSInstrNextNodeNodeNextSubStep(
                    s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node
                );

                if node != hSender1
                {
                    assert cm1 in getAllMessagesSentByTheNode(s, hSender1);

                    var cuPayload := cm1.commitPayload.unsignedPayload;

                    pm' :| 
                        && pm' in s.nodes[hSender1].proposalsAccepted
                        &&  
                            var puPayload := pm'.proposalPayload.unsignedPayload;
                        &&  puPayload.height == cuPayload.height
                        &&  puPayload.round == cuPayload.round
                        &&  digest(pm'.proposedBlock) == cuPayload.digest
                        &&  signHash(hashBlockForCommitSeal(pm'.proposedBlock), s.nodes[hSender1].nodeState.id) == cuPayload.commitSeal
                        &&  areBlocksTheSameExceptForTheCommitSeals(b1',bm.block);  
                }
                else {
                        lemmaSignedCommit();
                        lemmaSignedHash();
                        var allMessagesSentByTheNodeAtThisStep := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + newMessagesSentToItself;
                        if cm1 in allMessagesSentByTheNodeAtThisStep
                        {
                            var currentForSubsteps := sForSubsteps.nodes[node].nodeState;
                            var nextForSubsteps := s'.nodes[node].nodeState;
                            assert NodeNextSubStep(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes); 

                            assert cm1.Commit?;

                            lemmaNodeNextSubstepIfCommitIsSentThenUponPrepareStep(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes, cm1);

                            assert UponPrepare(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes);
                            var cuPayload := cm1.commitPayload.unsignedPayload;

                            assert digest(optionGet(currentForSubsteps.proposalAcceptedForCurrentRound).proposedBlock) == cuPayload.digest;
                            assert s.nodes[node].nodeState.proposalAcceptedForCurrentRound.value in  s.nodes[node].proposalsAccepted;
                            assert s.nodes[node].nodeState.proposalAcceptedForCurrentRound.value.proposalPayload.unsignedPayload.round == cuPayload.round;
                            assert s.nodes[node].nodeState.proposalAcceptedForCurrentRound.value.proposalPayload.unsignedPayload.height == cuPayload.height;

                            pm' := optionGet(currentForSubsteps.proposalAcceptedForCurrentRound);

                            assert
                            // var pm' :| 
                                && pm' in s.nodes[node].proposalsAccepted
                                &&  
                                    var puPayload := pm'.proposalPayload.unsignedPayload;
                                &&  puPayload.height == cuPayload.height
                                &&  puPayload.round == cuPayload.round
                                &&  digest(pm'.proposedBlock) == cuPayload.digest
                                && areBlocksTheSameExceptForTheCommitSeals(b1',bm.block);
                        }
                        else
                        {
                            assert cm1 in getAllMessagesSentByTheNode(s, hSender1);

                            pm' :| 
                                && pm' in s.nodes[hSender1].proposalsAccepted
                                &&  
                                    var puPayload := pm'.proposalPayload.unsignedPayload;
                                &&  puPayload.height == cuPayload.height
                                &&  puPayload.round == cuPayload.round
                                &&  digest(pm'.proposedBlock) == cuPayload.digest
                                &&  signHash(hashBlockForCommitSeal(pm'.proposedBlock), s.nodes[hSender1].nodeState.id) == cuPayload.commitSeal
                                &&  areBlocksTheSameExceptForTheCommitSeals(b1',bm.block);                           
                        }
                }

            }
            else
            {
                pm' :| 
                    && pm' in s.nodes[hSender1].proposalsAccepted
                    &&  
                        var puPayload := pm'.proposalPayload.unsignedPayload;
                    &&  puPayload.height == cuPayload.height
                    &&  puPayload.round == cuPayload.round
                    &&  digest(pm'.proposedBlock) == cuPayload.digest
                    &&  signHash(hashBlockForCommitSeal(pm'.proposedBlock), s.nodes[hSender1].nodeState.id) == cuPayload.commitSeal
                    &&  areBlocksTheSameExceptForTheCommitSeals(b1',bm.block);     
            }                           
    }

    // 2s 3.2.0
    lemma lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper4(
        s: InstrDSState,
        s': InstrDSState,
        bm: QbftMessage,
        blockchain: Blockchain
    ) returns (n:Address)
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invBlockchainConsistency(s)
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires InstrDSNextSingle(s,s') 
    requires s != s'
    requires        && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s')
                    && validNewBlockMessage(blockchain, bm)   
                    && bm.block.header.height > 0
    ensures && isInstrNodeHonest(s', n) 
            && |s'.nodes[n].nodeState.blockchain| >= |blockchain|
    {
        axiomRawValidatorsNeverChange();
        n :| true;
        if bm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
        {
            n :| true;
            n :| 
                && isInstrNodeHonest(s, n) 
                && |s.nodes[n].nodeState.blockchain| >= |blockchain|;
            
            assert isInstrNodeHonest(s', n);
            lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper1(s, s', n);
            assert |s'.nodes[n].nodeState.blockchain| >= |blockchain|;
        }
        else
        {
            var pm', hSender1, b1' := lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper3(s, s', bm, blockchain);
            assert
                && isInstrNodeHonest(s, hSender1)
                && pm'.Proposal?
                && pm' in s.nodes[hSender1].proposalsAccepted
                &&  
                    var puPayload := pm'.proposalPayload.unsignedPayload;
                &&  puPayload.height == bm.block.header.height
                &&  puPayload.round == bm.block.header.roundNumber
                &&  digest(pm'.proposedBlock) == digest(b1')   
                && areBlocksTheSameExceptForTheCommitSeals(b1',bm.block);  
            assert |s.nodes[hSender1].nodeState.blockchain| >= pm'.proposalPayload.unsignedPayload.height;   
            assert invInstrNodeStateAllProposalsAcceptedAreValid(s.nodes[hSender1]);   
            var sHSender1 := s.nodes[hSender1];
            assert invInstrNodeStateAllProposalsAcceptedAreValid(sHSender1);   
            assert pm' in sHSender1.proposalsAccepted;   
            lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper5(sHSender1, pm'); 
            // assert isValidProposalJustification(pm', sHSender1.nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);
            // assert |s.nodes[hSender1].nodeState.blockchain| >= |blockchain|;
            lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper1(s, s', hSender1);
            assert |s'.nodes[hSender1].nodeState.blockchain| >= |blockchain|;
            assert isInstrNodeHonest(s', hSender1);
            n := hSender1;
        }
    }           

    // 2s 3.2.0
    lemma lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper5(
        s: InstrNodeState,
        pm: QbftMessage
    )
    requires validInstrStateEx(s)
    requires indInvInstrNodeStateTypes(s)
    requires invInstrNodeStateAllProposalsAcceptedAreValid(s); 
    requires pm in  s.proposalsAccepted
    requires pm.proposalPayload.unsignedPayload.height > 0 
    ensures pm.proposalPayload.unsignedPayload.height <= |s.nodeState.blockchain|
    ensures isValidProposalJustification(pm, s.nodeState.blockchain[..pm.proposalPayload.unsignedPayload.height])
    {  }

    // 2s 3.2.0
    lemma lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(
        s: InstrDSState,
        s': InstrDSState
    )
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invBlockchainConsistency(s)
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires InstrDSNextSingle(s,s')  
    ensures invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s')
    {
        axiomRawValidatorsNeverChange();

        if s != s'
        {
            forall bm, blockchain |
                && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s')
                && validNewBlockMessage(blockchain, bm)
                && |blockchain| > 0
            ensures exists n :: 
                    && isInstrNodeHonest(s', n) 
                    && |s'.nodes[n].nodeState.blockchain| >= |blockchain|
            {
                var n:=lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper4(s, s', bm, blockchain);
            }
        }
    }

    // 6s
    lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper2(
        s: InstrDSState,
        s': InstrDSState,
        bm: QbftMessage,
        n: Address,
        blockchain: Blockchain    
    ) returns (cm1: QbftMessage, b1': Block, p1: QbftMessage, hSender1: Address)
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invBlockchainConsistency(s)
    requires InstrDSNextSingle(s, s')
    requires isInstrNodeHonest(s',n)
    requires blockchain <= s'.nodes[n].nodeState.blockchain
    requires validNewBlockMessage(blockchain, bm)
    requires    
                var newSentMessages := allMesssagesSentIncSentToItselfWithoutRecipient(s'); // - allMesssagesSentIncSentToItselfWithoutRecipient(s);
                && bm in newSentMessages    
    ensures 
            && isInstrNodeHonest(s, hSender1) 
            && cm1 in getAllMessagesSentByTheNode(s', hSender1)
            && p1.Proposal?
            && p1 in s'.nodes[hSender1].proposalsAccepted
            && p1.proposedBlock == b1'
            && areBlocksTheSameExceptForTheCommitSeals(b1',bm.block)
            && cm1.Commit?
            && cm1.commitPayload.unsignedPayload.height == bm.block.header.height
            && cm1.commitPayload.unsignedPayload.round == bm.block.header.roundNumber
            && cm1.commitPayload.unsignedPayload.digest == digest(b1');                     
    {
        axiomRawValidatorsNeverChange();
        lemmaIndInvForConsistency(s, s');
        lemmaDigest();        
        assert isInstrNodeHonest(s, n);
        // assert s.nodes[n].nodeState.blockchain == s'.nodes[n].nodeState.blockchain;
        var V := validators(blockchain);
        assert V == validators([s.configuration.genesisBlock]);
        assert isUniqueSequence(V);
        var Vset := seqToSet(V);
        lUniqueSeq(V);
        var block1 := bm.block;  
        var bhash1 := hashBlockForCommitSeal(block1);
        var css1 := block1.header.commitSeals;
        var cssAuth1 := getCommitSealAuthors(bhash1, css1);
        lemmaOnSizeOfSetOfCommitSeals(bhash1, css1);
        assert |cssAuth1| == |css1|;   
        lemmaThereExistsAnHonestInQuorum(Vset, s.adversary.byz, cssAuth1);      
        hSender1 :|
            && hSender1 in cssAuth1
            && isInstrNodeHonest(s, hSender1); 

        var cs1 :|  && cs1 in css1
            && recoverSignedHashAuthor(bhash1, cs1) == hSender1;  

        assert cs1 in getCommitSeals((allMesssagesSentIncSentToItselfWithoutRecipient(s')));
        assert isInstrNodeHonest(s', hSender1);

        assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',block1,hSender1);  
        
        cm1, b1', p1 :|    
            && cm1 in getAllMessagesSentByTheNode(s', hSender1)
            && p1 in s'.nodes[hSender1].proposalsAccepted
            && p1.proposedBlock == b1'
            && areBlocksTheSameExceptForTheCommitSeals(b1',block1)
            && cm1.Commit?
            && cm1.commitPayload.unsignedPayload.height == block1.header.height
            && cm1.commitPayload.unsignedPayload.round == block1.header.roundNumber
            && cm1.commitPayload.unsignedPayload.digest == digest(b1');   
    }

    // 34s 3.2.0
    lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(
        s: InstrDSState,
        s': InstrDSState,
        // node: Address  
        bm: QbftMessage,
        n: Address,
        blockchain: Blockchain    
    ) returns (pm': QbftMessage, hSender1: Address, b1': Block)
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invBlockchainConsistency(s)
    requires InstrDSNextSingle(s, s')
    requires isInstrNodeHonest(s',n)
    requires blockchain <= s'.nodes[n].nodeState.blockchain

    requires validNewBlockMessage(blockchain, bm)
    requires    
                var newSentMessages := allMesssagesSentIncSentToItselfWithoutRecipient(s') - allMesssagesSentIncSentToItselfWithoutRecipient(s);
                && bm in newSentMessages
    ensures 
                        && isInstrNodeHonest(s, hSender1)
                        && pm'.Proposal?
                        && pm' in s.nodes[hSender1].proposalsAccepted
                        &&  
                            var puPayload := pm'.proposalPayload.unsignedPayload;
                        &&  puPayload.height == bm.block.header.height
                        &&  puPayload.round == bm.block.header.roundNumber
                        &&  digest(pm'.proposedBlock) == digest(b1')   
                        && areBlocksTheSameExceptForTheCommitSeals(b1',bm.block)
    {
            axiomRawValidatorsNeverChange();
            lemmaIndInvForConsistency(s, s');
            lemmaDigest();

            var node :| isNodeThatTakesStep(s, s', node);

            var cm1: QbftMessage, p1: QbftMessage;
            cm1, b1', p1, hSender1 := lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper2(s, s', bm, n, blockchain);  
            pm' :| true;        

            var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node);     

            var cuPayload := cm1.commitPayload.unsignedPayload;                              

            if isInstrNodeHonest(s,node)
            {        
                var sForSubsteps, newMessagesReceived, newMessagesSentToItself := lemmaFromDSInstrNextNodeNodeNextSubStep(
                    s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node
                );

                if node != hSender1
                {
                    assert cm1 in getAllMessagesSentByTheNode(s, hSender1);

                    var cuPayload := cm1.commitPayload.unsignedPayload;
                    assert cuPayload.height <= |s'.nodes[n].nodeState.blockchain|;


                    pm' :| 
                        && pm' in s.nodes[hSender1].proposalsAccepted
                        &&  
                            var puPayload := pm'.proposalPayload.unsignedPayload;
                        &&  puPayload.height == cuPayload.height
                        &&  puPayload.round == cuPayload.round
                        &&  digest(pm'.proposedBlock) == cuPayload.digest
                        &&  signHash(hashBlockForCommitSeal(pm'.proposedBlock), s.nodes[hSender1].nodeState.id) == cuPayload.commitSeal
                        &&  areBlocksTheSameExceptForTheCommitSeals(b1',bm.block);  
                }
                else {
                        lemmaSignedCommit();
                        lemmaSignedHash();
                        var allMessagesSentByTheNodeAtThisStep := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + newMessagesSentToItself;
                        if cm1 in allMessagesSentByTheNodeAtThisStep
                        {
                            var currentForSubsteps := sForSubsteps.nodes[node].nodeState;
                            var nextForSubsteps := s'.nodes[node].nodeState;
                            assert NodeNextSubStep(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes); 

                            assert cm1.Commit?;

                            lemmaNodeNextSubstepIfCommitIsSentThenUponPrepareStep(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes, cm1);

                            assert UponPrepare(currentForSubsteps, nextForSubsteps, messagesSentByTheNodes);
                            var cuPayload := cm1.commitPayload.unsignedPayload;

                            assert digest(optionGet(currentForSubsteps.proposalAcceptedForCurrentRound).proposedBlock) == cuPayload.digest;
                            assert s.nodes[node].nodeState.proposalAcceptedForCurrentRound.value in  s.nodes[node].proposalsAccepted;
                            assert s.nodes[node].nodeState.proposalAcceptedForCurrentRound.value.proposalPayload.unsignedPayload.round == cuPayload.round;
                            assert s.nodes[node].nodeState.proposalAcceptedForCurrentRound.value.proposalPayload.unsignedPayload.height == cuPayload.height;

                            pm' := optionGet(currentForSubsteps.proposalAcceptedForCurrentRound);

                            assert
                            // var pm' :| 
                                && pm' in s.nodes[node].proposalsAccepted
                                &&  
                                    var puPayload := pm'.proposalPayload.unsignedPayload;
                                &&  puPayload.height == cuPayload.height
                                &&  puPayload.round == cuPayload.round
                                &&  digest(pm'.proposedBlock) == cuPayload.digest
                                && areBlocksTheSameExceptForTheCommitSeals(b1',bm.block);
                        }
                        else
                        {
                            assert cm1 in getAllMessagesSentByTheNode(s, hSender1);

                            pm' :| 
                                && pm' in s.nodes[hSender1].proposalsAccepted
                                &&  
                                    var puPayload := pm'.proposalPayload.unsignedPayload;
                                &&  puPayload.height == cuPayload.height
                                &&  puPayload.round == cuPayload.round
                                &&  digest(pm'.proposedBlock) == cuPayload.digest
                                &&  signHash(hashBlockForCommitSeal(pm'.proposedBlock), s.nodes[hSender1].nodeState.id) == cuPayload.commitSeal
                                &&  areBlocksTheSameExceptForTheCommitSeals(b1',bm.block);                           
                        }
                }

            }
            else
            {
                assert cuPayload.height <= |s'.nodes[n].nodeState.blockchain|;


                pm' :| 
                    && pm' in s.nodes[hSender1].proposalsAccepted
                    &&  
                        var puPayload := pm'.proposalPayload.unsignedPayload;
                    &&  puPayload.height == cuPayload.height
                    &&  puPayload.round == cuPayload.round
                    &&  digest(pm'.proposedBlock) == cuPayload.digest
                    &&  signHash(hashBlockForCommitSeal(pm'.proposedBlock), s.nodes[hSender1].nodeState.id) == cuPayload.commitSeal
                    &&  areBlocksTheSameExceptForTheCommitSeals(b1',bm.block);     
            }                           
    }

    // 2s 3.2.0
    lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper4(
        blockchain: Blockchain,
        b: Block,
        i: nat 
    )
    requires |blockchain| > i 
    requires b == blockchain[i]
    ensures blockchain[..(i+1)] == blockchain[..i] + [b]
    {  }

    predicate pLemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(
        bc: Blockchain,
        bc': Blockchain,
        b: Block
    )
    {
        bc == bc' + [b]
    }    

    // 5s 3.2.0
    lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper5(
        s: InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        n: Address          
    ) returns (b: Block, b':Block)
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)
    requires invBlockchainConsistency(s)
    requires InstrDSNextSingle(s, s')   
    requires  InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,n);    
    requires isInstrNodeHonest(s, n)
    requires 
            var sForSubsteps := getStartStateForNodeNextSubstep(
                s, s', messagesReceivedByTheNodes, n
            );
            UponCommit(sForSubsteps.nodes[n].nodeState, s'.nodes[n].nodeState, messagesSentByTheNodes)   
    requires s.nodes[n].nodeState.blockchain !=  s'.nodes[n].nodeState.blockchain
    ensures  ValidNewBlock(s.nodes[n].nodeState.blockchain, b');
    ensures  b'.header.commitSeals <= getCommitSeals((allMesssagesSentIncSentToItselfWithoutRecipient(s)));
    ensures pLemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(s'.nodes[n].nodeState.blockchain, s.nodes[n].nodeState.blockchain, b)
    ensures areBlocksTheSameExceptForTheCommitSealsAndRound(b, b')
    {
        var sForSubsteps := getStartStateForNodeNextSubstep(
                s, s', messagesReceivedByTheNodes, n
            );
        var current := sForSubsteps.nodes[n];
        var next := s'.nodes[n];
        b := next.nodeState.blockchain[|next.nodeState.blockchain|-1];
        assert current.nodeState.blockchain +  [b] == next.nodeState.blockchain;

        assert current.nodeState.blockchain != next.nodeState.blockchain;

        var currentForSubsteps := current.nodeState;

        var allValidCommitsForCurrentHeightAndRound := 
            validCommitsForHeightRoundAndDigest(
                currentForSubsteps.messagesReceived,
                |currentForSubsteps.blockchain|,
                currentForSubsteps.round,
                currentForSubsteps.proposalAcceptedForCurrentRound.value.proposedBlock,
                validators(currentForSubsteps.blockchain));     

        var proposedBlock:Block := currentForSubsteps.proposalAcceptedForCurrentRound.value.proposedBlock;

        assert b == proposedBlock;



        lemmaSignedCommit();
        lemmaSignedHash();

        assert exists bm, QofC:set<QbftMessage> ::
            && QofC <= allValidCommitsForCurrentHeightAndRound
            && |QofC| == quorum(|validators(currentForSubsteps.blockchain)|)
            && bm in next.nodeState.messagesReceived 
            && bm.NewBlock?
            // && areAllMessagesCommits(QofC)
            && bm.block == proposedBlock.(
                                header := proposedBlock.header.(
                                    commitSeals := getCommitSealsFromCommitMessages(QofC)
                                )
                            );

        var QofC:set<QbftMessage>, bm:QbftMessage :|
            && QofC <= allValidCommitsForCurrentHeightAndRound
            && |QofC| == quorum(|validators(currentForSubsteps.blockchain)|)
            // && next.nodeState.messageesReceived == currentForSubsteps.messagesReceived + {bm}
            && bm.NewBlock?
            // && areBlocksTheSameExceptForTheCommitSeals(proposedBlock, bm.block)
            // && areAllMessagesCommits(QofC)
            && bm.block == proposedBlock.(
                                header := proposedBlock.header.(
                                    commitSeals := getCommitSealsFromCommitMessages(QofC)
                                )
                            )
            ;    
        // assert QofC <= currentForSubsteps.messagesReceived;
        // var newMessagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

        // assert currentForSubsteps.messagesReceived == s.nodes[n].nodeState.messagesReceived + newMessagesReceived;
        // // assert newMessagesReceived <= allMesssagesSentIncSentToItselfWithoutRecipient(s);
        // assert s.nodes[n].nodeState.messagesReceived <= allMesssagesSentIncSentToItselfWithoutRecipient(s);
        // assert s.environment.messagesSentYetToBeReceived <= s.environment.allMessagesSent;
        // assert messagesReceivedByTheNodes <= s.environment.allMessagesSent;
        // // assert currentForSubsteps.messagesReceived <= allMesssagesSentIncSentToItselfWithoutRecipient(s);
        assert QofC <= allMesssagesSentIncSentToItselfWithoutRecipient(s);

        var css := getCommitSealsFromSetOfCommitMessages(QofC);
        assert css <= getCommitSeals((allMesssagesSentIncSentToItselfWithoutRecipient(s)));
        assert (forall s | s in css :: recoverSignedHashAuthor(hashBlockForCommitSeal(b),s) in validators(currentForSubsteps.blockchain));
        assert b.header.height == |currentForSubsteps.blockchain|;
        lllfdafadllCommitSimp(
            currentForSubsteps.round,
            currentForSubsteps.proposalAcceptedForCurrentRound.value.proposedBlock,
            QofC,
            currentForSubsteps.messagesReceived,
            currentForSubsteps.blockchain
        );
        assert 
                |css| >= quorum(|validators(currentForSubsteps.blockchain)|);
        assert ValidNewBlock(currentForSubsteps.blockchain, bm.block);
        b' := bm.block;
        // assert areBlocksTheSameExceptForTheCommitSeals(proposedBlock, bm.block);   
    }

    // 2s 3.2.0
    lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper6Helper<T>(
        s: seq<T>,
        b: T,
        i: nat
    )
    requires |s| > i 
    requires b == s[i]
    ensures s[..i] + [b] == s[..i+1]
    {  }

    // 25s 3.2.0
    lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper6(
        s: InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        n: Address,
        bm: QbftMessage          
    ) returns (b': Block, b'': Block, n': Address)
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)
    requires invMessagesReceivedByHonestNodesAreInAllMesssagesSentIncSentToItselfWithoutRecipient(s)
    requires invBlockchainConsistency(s)
    requires InstrDSNextSingle(s, s')   
    requires  InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,n);    
    requires isInstrNodeHonest(s, n)
    requires        && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                    && validNewBlockMessage(s'.nodes[n].nodeState.blockchain,bm)
    ensures isInstrNodeHonest(s, n')
    requires s.nodes[n].nodeState.blockchain !=  s'.nodes[n].nodeState.blockchain
    ensures |s.nodes[n'].nodeState.blockchain| >= |s'.nodes[n].nodeState.blockchain| > |s.nodes[n].nodeState.blockchain|
    ensures |s'.nodes[n].nodeState.blockchain| > 0
    ensures pLemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(s.nodes[n'].nodeState.blockchain[..|s'.nodes[n].nodeState.blockchain|], s.nodes[n'].nodeState.blockchain[..|s.nodes[n].nodeState.blockchain|], b');
    ensures b''.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s));
    ensures  areBlocksTheSameExceptForTheCommitSealsAndRound(b'', b')
    ensures ValidNewBlock(s.nodes[n'].nodeState.blockchain[..|s.nodes[n].nodeState.blockchain|], b'');
 
    
    {
        var sForSubsteps, newMessagesReceived, newMessagesSentToItself := lemmaFromDSInstrNextNodeNodeNextSubStep(
            s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n
        );

        // // // var currentForSubsteps := sForSubsteps.nodes[n].nodeState;
        // // // var nextForSubsteps := s'.nodes[n].nodeState;
        assert NodeNextSubStep(sForSubsteps.nodes[n].nodeState, s'.nodes[n].nodeState, messagesSentByTheNodes);  
        lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper1(s, s', n);       
        assert |s'.nodes[n].nodeState.blockchain| > 0 ;

        var b:= s'.nodes[n].nodeState.blockchain[|s'.nodes[n].nodeState.blockchain|-1];

        n' :|
            && isInstrNodeHonest(s, n') 
            && |s.nodes[n'].nodeState.blockchain| >= |s'.nodes[n].nodeState.blockchain|;


        // // assert s.nodes[n'].nodeState.blockchain[..|s'.nodes[n].nodeState.blockchain|] == s'.nodes[n].nodeState.blockchain;


        var i := |s'.nodes[n].nodeState.blockchain|-1;
        assert i == |s.nodes[n].nodeState.blockchain|;
        b' := s.nodes[n'].nodeState.blockchain[i]; 
        lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper6Helper(s.nodes[n'].nodeState.blockchain, b', i);  
        assert s.nodes[n'].nodeState.blockchain[..i] + [b'] ==  s.nodes[n'].nodeState.blockchain[..(i+1)];
        assert s.nodes[n'].nodeState.blockchain[..|s'.nodes[n].nodeState.blockchain|-1] + [b'] == s.nodes[n'].nodeState.blockchain[..|s'.nodes[n].nodeState.blockchain|];

        assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(s.nodes[n']);
        assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(s.nodes[n'], i);
        var bm' :|
            && bm' in s.nodes[n'].nodeState.messagesReceived
            && bm'.NewBlock?
            && areBlocksTheSameExceptForTheCommitSealsAndRound(bm'.block, b')
            && bm'.block.header.height == i
            && ValidNewBlock(s.nodes[n'].nodeState.blockchain[..i], bm'.block);
        b'' := bm'.block;    
        assert ValidNewBlock(s.nodes[n'].nodeState.blockchain[..|s.nodes[n].nodeState.blockchain|], b'');

        assert bm' in s.nodes[n'].nodeState.messagesReceived;
        assert bm' in allMesssagesSentIncSentToItselfWithoutRecipient(s);    
        assert bm'.block.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s));
 
   
    }

    // 2s 3.2.0
    lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper7(
        s: InstrDSState,
        s': InstrDSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        n: Address          
    ) returns (b:Block)
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)
    requires invBlockchainConsistency(s)
    requires InstrDSNextSingle(s, s')   
    requires  InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,n);    
    requires isInstrNodeHonest(s, n)
    requires invMessagesReceivedByHonestNodesAreInAllMesssagesSentIncSentToItselfWithoutRecipient(s)
    requires 
            var sForSubsteps := getStartStateForNodeNextSubstep(
                s, s', messagesReceivedByTheNodes, n
            );
            UponNewBlock(sForSubsteps.nodes[n].nodeState, s'.nodes[n].nodeState, messagesSentByTheNodes)   
    requires s.nodes[n].nodeState.blockchain !=  s'.nodes[n].nodeState.blockchain
    ensures |s'.nodes[n].nodeState.blockchain| > 0
    ensures pLemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(s'.nodes[n].nodeState.blockchain, s.nodes[n].nodeState.blockchain, b)
    ensures b.header.commitSeals <= getCommitSeals((allMesssagesSentIncSentToItselfWithoutRecipient(s)));
    ensures ValidNewBlock(s.nodes[n].nodeState.blockchain,b)
    {
        var sForSubsteps := getStartStateForNodeNextSubstep(
                s, s', messagesReceivedByTheNodes, n
            );
        var current := sForSubsteps.nodes[n];
        var next := s'.nodes[n];

        var i := |s'.nodes[n].nodeState.blockchain|-1;
        b:= s'.nodes[n].nodeState.blockchain[i];
        assert s'.nodes[n].nodeState.blockchain == s.nodes[n].nodeState.blockchain + [b];
        assert sForSubsteps.nodes[n].nodeState.blockchain == s'.nodes[n].nodeState.blockchain[..i];

        var bm'' :|
            bm'' in sForSubsteps.nodes[n].nodeState.messagesReceived && 
            validNewBlockMessage(sForSubsteps.nodes[n].nodeState.blockchain,bm'')
            && bm''.block == b; 

        assert bm'' in allMesssagesSentIncSentToItselfWithoutRecipient(s);  
        assert bm''.block.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s));    
 
    }  

    // 2s 3.2.0
    lemma 
    {:fuel validators,0,0} 
    {:fuel areBlockchainsTheSameExceptForTheCommitSealsAndRound,0,0} 
    {:fuel fromBlockchainToRawBlockchain,0,0}
    lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper9(
        s: InstrDSState,
        b: Block,
        b': Block,
        b'': Block,
        bn' : Block, 
        n1: Address,
        n2: Address,
        bc: Blockchain,
        bc': Blockchain,
        bcf: Blockchain,
        bcf': Blockchain,
        bm: QbftMessage
    )
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)
    requires invBlockchainConsistency(s)
    requires isInstrNodeHonest(s,n1)  
    requires isInstrNodeHonest(s,n2) 
    requires |bc| == |bc'| 
    requires |bc| > 0 
    requires pLemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(bcf, bc, b)
    requires pLemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(bcf', bc', b')
    requires bc <= s.nodes[n1].nodeState.blockchain
    requires bc' <= bcf' <= s.nodes[n2].nodeState.blockchain
    requires areBlocksTheSameExceptForTheCommitSealsAndRound(b', bn')
    requires areBlocksTheSameExceptForTheCommitSealsAndRound(b, b'') 
    requires    && b''.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                && ValidNewBlock(bc,b'')
    requires    && bn'.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                && ValidNewBlock(bc',bn')
    requires bm.NewBlock?
    requires bm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
    requires ValidNewBlock(bcf,bm.block)
    ensures bm.block.header.proposer in validators(bcf);    
    {
        lemmaAreBlocksTheSameExceptForTheCommitSealsAndRoundIsReflexiveAndAreBlocksTheSameExceptForTheCommitSealsAndRoundAndFromBlockchainToRawBlockchainEquivalenceAreEquivalent();
        assert  consistentBlockchains(
                    s.nodes[n1].nodeState.blockchain,
                    s.nodes[n2].nodeState.blockchain
                );
        lemmaPrefixesOfConsistentBlockchainsAreConsistenAndIfOfTheSameLengthThenAreAlsoFromBlockchainToRawBlockchainEquivalentAndAreBlockchainsTheSameExceptForTheCommitSealsAndRound(
            bc,
            bc',
            s.nodes[n1].nodeState.blockchain,
            s.nodes[n2].nodeState.blockchain);

        lemmaFromBlockchainToRawBlockchainEquivalencePreservesValidNewBlock(
            bn', bc, bc'
        );

        // assert  ValidNewBlock(bc', b) <==> ValidNewBlock(bc, b);
        assert ValidNewBlock(bc',bn');
        // assert ValidNewBlock(bc,bn');
        assert bc == s.nodes[n1].nodeState.blockchain[..|bc|];

        // assert proposerPrecondition(s.nodes[n1].nodeState.blockchain[..|bc|]);
        assert ValidNewBlock(s.nodes[n1].nodeState.blockchain[..|bc|], bn');
        assert ValidNewBlock(s.nodes[n1].nodeState.blockchain[..|bc|], b'');
        lemmaInvBlockchainConsistencyImpliesInvBlockchainConsistencyUpToHeight(s, |bc|);
        assert  pBlockchainConsistencyUpToHeight(s, |bc|);

        lemmaInvAnyTwoValidNewBlockMessagesWithCommitSealsIncludedInAllCommitSealsSentForTheSameHeightAreConsistent(
            s,
            b'',
            bn',
            |bc|,
            n1
        );

        assert areBlocksTheSameExceptForTheCommitSealsAndRound(b'', bn');
        assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
        assert areBlockchainsTheSameExceptForTheCommitSealsAndRound(bc, bc');
        lemmaAddBlocksThatAreTheSameExceptForCommitSealsAndRoundNumberToBlockchainsThatAreTheSameExceptForCommitSealsAndRoundNumberPreservesFromBlockchainToRawBlockchainEquivalence(
            b,
            b',
            bc,
            bc'
        );

        assert areBlockchainsTheSameExceptForTheCommitSealsAndRound(bcf, bcf');

        lemmaFromBlockchainToRawBlockchainEquivalencePreservesValidNewBlock(bm.block, bcf, bcf');
        assert ValidNewBlock(bcf',bm.block);

        

        assert pBlockIsAValidBlockOfAnHonestBlockchain(
            s, 
            bm, 
            n2, 
            bcf'
            );

        assert bm.block.header.proposer in validators(bcf');

        lemmaOnFromBlockchainToRawBlockchainIImpliesValidatorsEquality(bcf, bcf');
        assert bm.block.header.proposer in validators(bcf);

        // lemmaAddBlocksThatAreTheSameExceptForCommitSealsAndRoundNumberToBlockchainsThatAreTheSameExceptForCommitSealsAndRoundNumberPreservesFromBlockchainToRawBlockchainEquivalence(

        // )
        //  lemmaInvBlockchainConsistencyImpliesInvBlockchainConsistencyUpToHeight(s,|bc|);
        //  lemmaOnFromBlockchainToRawBlockchainPrefixImpliesBlockchainsTruncatedToTheSameLengthAreTheSameExceptForTheCommitSealsAndRound(s.nodes[n].nodeState.blockchain, s.nodes[n'].nodeState.blockchain);
    }

    // 34s 3.2.0
    lemma {:fuel validators, 0, 0} lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper10(
        s: InstrDSState,
        s': InstrDSState,
        n: Address,
        bm: QbftMessage,
        blockchain: Blockchain     
    )
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)
    requires invBlockchainConsistency(s)
    requires invMessagesReceivedByHonestNodesAreInAllMesssagesSentIncSentToItselfWithoutRecipient(s)
    requires InstrDSNextSingle(s, s')    
    requires    && isInstrNodeHonest(s', n)
                && blockchain <= s'.nodes[n].nodeState.blockchain
                && |blockchain| > 0
                && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s')
                && validNewBlockMessage(blockchain,bm)
    requires bm in  allMesssagesSentIncSentToItselfWithoutRecipient(s)
    requires !(blockchain <= s.nodes[n].nodeState.blockchain)
    ensures bm.block.header.proposer in validators(blockchain); 
    {
        assert isNodeThatTakesStep(s, s', n);
        var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,n); 

        var sForSubsteps, newMessagesReceived, newMessagesSentToItself := lemmaFromDSInstrNextNodeNodeNextSubStep(
            s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n
        );

        // // // var currentForSubsteps := sForSubsteps.nodes[n].nodeState;
        // // // var nextForSubsteps := s'.nodes[n].nodeState;
        assert NodeNextSubStep(sForSubsteps.nodes[n].nodeState, s'.nodes[n].nodeState, messagesSentByTheNodes); 
        lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper1(s, s', n);
        assert sForSubsteps.nodes[n].nodeState.blockchain <= s'.nodes[n].nodeState.blockchain;
        assert |sForSubsteps.nodes[n].nodeState.blockchain| + 1  == |s'.nodes[n].nodeState.blockchain|;          
        assert blockchain == s'.nodes[n].nodeState.blockchain;
        var b', bn', n' := lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper6(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n, bm);

        if  UponNewBlock(sForSubsteps.nodes[n].nodeState, s'.nodes[n].nodeState, messagesSentByTheNodes)
        {
            var b:= lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper7(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n);
            assert  pLemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(s'.nodes[n].nodeState.blockchain, s.nodes[n].nodeState.blockchain, b);
            assert pLemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(s.nodes[n'].nodeState.blockchain[..|s'.nodes[n].nodeState.blockchain|], s.nodes[n'].nodeState.blockchain[..|s.nodes[n].nodeState.blockchain|], b');
            // assert s.nodes[n'].nodeState.blockchain[..|s'.nodes[n].nodeState.blockchain|] == s.nodes[n'].nodeState.blockchain[..|s.nodes[n].nodeState.blockchain|] + [b'];                                        

            lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper9(
                s,
                b,
                b',
                b,
                bn',
                // |s.nodes[n].nodeState.blockchain|,
                n,
                n',
                s.nodes[n].nodeState.blockchain,
                s.nodes[n'].nodeState.blockchain[..|s.nodes[n].nodeState.blockchain|],
                s'.nodes[n].nodeState.blockchain,
                s.nodes[n'].nodeState.blockchain[..|s'.nodes[n].nodeState.blockchain|],
                bm
            );


            assert bm.block.header.proposer in validators(s'.nodes[n].nodeState.blockchain);  
            assert bm.block.header.proposer in validators(blockchain); 

        } 
        else if  UponCommit(sForSubsteps.nodes[n].nodeState, s'.nodes[n].nodeState, messagesSentByTheNodes)
        {
            var b, b'' := lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper5(s, s',messagesSentByTheNodes,messagesReceivedByTheNodes,n );
            assert  pLemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(s'.nodes[n].nodeState.blockchain, s.nodes[n].nodeState.blockchain, b);
            assert pLemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(s.nodes[n'].nodeState.blockchain[..|s'.nodes[n].nodeState.blockchain|], s.nodes[n'].nodeState.blockchain[..|s.nodes[n].nodeState.blockchain|], b');
            lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper9(
                s,
                b,
                b',
                b'',
                bn',
                // |s.nodes[n].nodeState.blockchain|,
                n,
                n',
                s.nodes[n].nodeState.blockchain,
                s.nodes[n'].nodeState.blockchain[..|s.nodes[n].nodeState.blockchain|],
                s'.nodes[n].nodeState.blockchain,
                s.nodes[n'].nodeState.blockchain[..|s'.nodes[n].nodeState.blockchain|],
                bm
            ); 

            assert bm.block.header.proposer in validators(s'.nodes[n].nodeState.blockchain);  
            assert bm.block.header.proposer in validators(blockchain);                                                                                                          
        }                  
        assert bm.block.header.proposer in validators(blockchain);            
    }

    // 45s 3.2.0
    lemma {:fuel validators, 0, 0} lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper11(
        s: InstrDSState,
        s': InstrDSState,
        n: Address,
        bm: QbftMessage,
        blockchain: Blockchain             
    )
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)
    requires invBlockchainConsistency(s)
    requires invMessagesReceivedByHonestNodesAreInAllMesssagesSentIncSentToItselfWithoutRecipient(s)
    requires InstrDSNextSingle(s, s') 
    requires s != s'
    requires                     && isInstrNodeHonest(s', n)
                    && blockchain <= s'.nodes[n].nodeState.blockchain
                    && |blockchain| > 0
                    && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s')
                    && validNewBlockMessage(blockchain,bm)
    requires bm !in allMesssagesSentIncSentToItselfWithoutRecipient(s)
    requires !(blockchain <= s.nodes[n].nodeState.blockchain)
    ensures false
    {
        assert isNodeThatTakesStep(s, s', n);
        var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,n); 

        var sForSubsteps, newMessagesReceived, newMessagesSentToItself := lemmaFromDSInstrNextNodeNodeNextSubStep(
            s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n
        );

        assert NodeNextSubStep(sForSubsteps.nodes[n].nodeState, s'.nodes[n].nodeState, messagesSentByTheNodes); 
        lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper1(s, s', n);
        assert sForSubsteps.nodes[n].nodeState.blockchain <= s'.nodes[n].nodeState.blockchain;
        assert |sForSubsteps.nodes[n].nodeState.blockchain| + 1  == |s'.nodes[n].nodeState.blockchain|;      
        if  UponCommit(sForSubsteps.nodes[n].nodeState, s'.nodes[n].nodeState, messagesSentByTheNodes)
        {
            assert false;
        }      
        else
        {
            assert false;
        }                 
        assert false;
    }


    // 26s 3.2.0
    lemma {:fuel validators, 0, 0} lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidators(
        s: InstrDSState,
        s': InstrDSState      
    )
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)
    requires invBlockchainConsistency(s)
    requires invMessagesReceivedByHonestNodesAreInAllMesssagesSentIncSentToItselfWithoutRecipient(s)
    requires InstrDSNextSingle(s, s')                          
    ensures invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s');
    {
        axiomRawValidatorsNeverChange();
        // lemmaIndInvForConsistency(s, s');
        lemmaDigest();
        if s != s'
        {
                // var newSentMessages := allMesssagesSentIncSentToItselfWithoutRecipient(s') - allMesssagesSentIncSentToItselfWithoutRecipient(s);
                forall bm, n, blockchain |
                    && isInstrNodeHonest(s', n)
                    && blockchain <= s'.nodes[n].nodeState.blockchain
                    && |blockchain| > 0
                    && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s')
                    && validNewBlockMessage(blockchain,bm)
                ensures bm.block.header.proposer in validators(blockchain); 
                {
                    // assume bm.block.header.proposer in validators(blockchain); 
                    
                    if bm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                    {
                        if s.nodes[n].nodeState.blockchain == s'.nodes[n].nodeState.blockchain
                        {
                            assert pBlockIsAValidBlockOfAnHonestBlockchain(s, bm, n, blockchain);
                            assert bm.block.header.proposer in validators(blockchain);  
                        }
                        
                        else
                        {
                            assert isNodeThatTakesStep(s, s', n);
                            var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                                    InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,n); 

                            var sForSubsteps, newMessagesReceived, newMessagesSentToItself := lemmaFromDSInstrNextNodeNodeNextSubStep(
                                s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, n
                            );

                            // // // var currentForSubsteps := sForSubsteps.nodes[n].nodeState;
                            // // // var nextForSubsteps := s'.nodes[n].nodeState;
                            assert NodeNextSubStep(sForSubsteps.nodes[n].nodeState, s'.nodes[n].nodeState, messagesSentByTheNodes); 
                            lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper1(s, s', n);
                            assert sForSubsteps.nodes[n].nodeState.blockchain <= s'.nodes[n].nodeState.blockchain;
                            assert |sForSubsteps.nodes[n].nodeState.blockchain| + 1  == |s'.nodes[n].nodeState.blockchain|;  

                            if blockchain <=  s.nodes[n].nodeState.blockchain
                            {
                                assert pBlockIsAValidBlockOfAnHonestBlockchain(s, bm, n, blockchain);
                                assert bm.block.header.proposer in validators(blockchain);  
                            }
                            else
                            {
                                lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper10(
                                    s,
                                    s',
                                    n,
                                    bm,
                                    blockchain
                                );                                                                                                         
                            }
                        }
                        assert bm.block.header.proposer in validators(blockchain);  
                        
                    }
                    
                    else
                    {
                        if blockchain <= s.nodes[n].nodeState.blockchain
                        {
                            lemmaAreBlocksTheSameExceptForTheCommitSealsAndRoundIsReflexiveAndAreBlocksTheSameExceptForTheCommitSealsAndRoundAndFromBlockchainToRawBlockchainEquivalenceAreEquivalent();
                            lemmaConsistentBlockchainIsSymmetric();
                            var pm', hSender1, b1' := lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper1(s, s', bm, n, blockchain);
                            assert
                                && isInstrNodeHonest(s, hSender1)
                                && pm'.Proposal?
                                && pm' in s.nodes[hSender1].proposalsAccepted
                                &&  
                                    var puPayload := pm'.proposalPayload.unsignedPayload;
                                &&  puPayload.height == bm.block.header.height == |blockchain|
                                &&  puPayload.round == bm.block.header.roundNumber
                                &&  digest(pm'.proposedBlock) == digest(b1')   
                                && areBlocksTheSameExceptForTheCommitSeals(b1',bm.block);


                            assert |s.nodes[hSender1].nodeState.blockchain| >= pm'.proposalPayload.unsignedPayload.height;
                            
                            // assert proposerPrecondition(s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);
                            // assert |s.nodes[hSender1].nodeState.blockchain| >= pm'.proposalPayload.unsignedPayload.height;

                            assert  consistentBlockchains(
                                        s.nodes[n].nodeState.blockchain,
                                        s.nodes[hSender1].nodeState.blockchain
                                    );          

                            lemmaPrefixesOfConsistentBlockchainsAreConsistenAndIfOfTheSameLengthThenAreAlsoFromBlockchainToRawBlockchainEquivalentAndAreBlockchainsTheSameExceptForTheCommitSealsAndRound(
                                blockchain,
                                s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height],
                                s.nodes[n].nodeState.blockchain,
                                s.nodes[hSender1].nodeState.blockchain);                                                      
                            assert  consistentBlockchains(
                                s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height],
                                blockchain
                            );      
                            assert s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height] != [];
                            assert isValidProposalJustification(pm', s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);
                            lemmaInvBlockchainConsistencyImpliesInvBlockchainConsistencyUpToHeight(s, pm'.proposalPayload.unsignedPayload.height);
                            assert pBlockchainConsistencyUpToHeight(s, pm'.proposalPayload.unsignedPayload.height);                            
                            lemmaInvTheProposerInAnyValidProposalUpToTheGivenRoundIsInTheSetOfValidators(s, pm'.proposalPayload.unsignedPayload.height, pm'.proposalPayload.unsignedPayload.round, hSender1);

                            assert pTheProposerInAnyValidProposalForTheGivenRoundIsInTheSetOfValidators(s, pm'.proposalPayload.unsignedPayload.round, s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);
                            assert pm' in allMesssagesSentIncSentToItselfWithoutRecipient(s);
                            // assert isValidProposalJustification(pm', s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height]);   
                            lemmaOnFromBlockchainToRawBlockchainIImpliesValidatorsEquality(
                                s.nodes[hSender1].nodeState.blockchain[..pm'.proposalPayload.unsignedPayload.height],
                                blockchain
                            );
                            assert bm.block.header.proposer in validators(blockchain); 

                        }
                        else 
                        {
                            lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper11(
                                s,
                                s',
                                n,
                                bm,
                                blockchain
                            );  

                            assert  bm.block.header.proposer in validators(blockchain);  
                        }
                        assert  bm.block.header.proposer in validators(blockchain); 

                    
                    }
                    
                    
                    
                }
        }
    }

    // 2s 3.2.0
    lemma lemmaInvValidInstrDSStateExHelper1(
        bc: Blockchain,
        bc': Blockchain,
        bc'': Blockchain,
        b: Block,
        i: nat
    )
    requires |bc| > 0
    requires bc == bc'
    requires i == |bc|-1;
    requires b == bc[i];
    requires bc'' == bc[..i]

    ensures  b == bc'[|bc'|-1]
    ensures bc'' == bc[..|bc|-1]
    ensures bc'' == bc'[..|bc'|-1]
    {  }

    // 14s 3.2.0
    lemma lemmaInvValidInstrDSStateExHelper2
    (
        s: InstrDSState,
        s': InstrDSState,
        n: Address,
        h: Blockchain        
    )
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)
    requires invBlockchainConsistency(s)
    requires InstrDSNextSingle(s, s')  
    requires isInstrNodeHonest(s', n)
    requires isNodeThatTakesStep(s, s', n) 
    requires h <= s'.nodes[n].nodeState.blockchain && |h| > 0
    requires !(h <= s.nodes[n].nodeState.blockchain) 
    ensures proposerPrecondition(h);
    {
        axiomRawValidatorsNeverChange();
        lemmaIndInvForConsistency(s, s');
        lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidators(s, s');        
        lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper1(s, s', n);
        assert s.nodes[n].nodeState.blockchain <= s'.nodes[n].nodeState.blockchain;        
        assert h == s'.nodes[n].nodeState.blockchain;
        var i := |s'.nodes[n].nodeState.blockchain| - 1;
        assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(s'.nodes[n], i);
        var b:= s'.nodes[n].nodeState.blockchain[i];

        var bm:QbftMessage :|
            && bm in s'.nodes[n].nodeState.messagesReceived
            && bm.NewBlock?
            && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
            && bm.block.header.height == i 
            && ValidNewBlock(s'.nodes[n].nodeState.blockchain[..i], bm.block); 

        assert invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s');

        var blockchain := s'.nodes[n].nodeState.blockchain[..i];
        assert
            && isInstrNodeHonest(s', n)
            && blockchain <= s'.nodes[n].nodeState.blockchain
            && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s')
            && validNewBlockMessage(blockchain,bm);                        

        // assert  s'.nodes[n].nodeState.blockchain[..i] <= s'.nodes[n].nodeState.blockchain;
        // assert bm in allMesssagesSentIncSentToItselfWithoutRecipient(s');
        // assert isInstrNodeHonest(s', n);
        // assert ValidNewBlock(s'.nodes[n].nodeState.blockchain[..i], bm.block); 
        assert pBlockIsAValidBlockOfAnHonestBlockchain(s', bm, n, blockchain);
        assert bm.block.header.proposer in validators(blockchain);   
        assert b.header.proposer in validators(blockchain);  
        assert b == s'.nodes[n].nodeState.blockchain[i];  
        assert |s'.nodes[n].nodeState.blockchain| > 0 ;
        lemmaInvValidInstrDSStateExHelper1(s'.nodes[n].nodeState.blockchain, h, blockchain, b, i);   
        assert blockchain == h[..|h|-1];                   
        assert h[|h|-1] == b;
        assert  h[|h|-1].header.proposer in validators(blockchain);  
        assert h[|h|-1].header.proposer in validators(h[..|h|-1]);
        // assert h[..|h|] == blockchain;
        // assert blockchain[|blockchain|-1] == b;
        assert proposerPrecondition(h);           
    }

    // 10s 3.2.0
    lemma lemmaInvValidInstrDSStateEx(
        s: InstrDSState,
        s': InstrDSState 
    )
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)
    requires invBlockchainConsistency(s)
    requires InstrDSNextSingle(s, s')    
    ensures validInstrDSStateEx(s');  
    {
        axiomRawValidatorsNeverChange();
        lemmaIndInvForConsistency(s, s');
        lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidators(s, s');
        forall n |
            && isInstrNodeHonest(s', n)
        ensures 
            && validInstrState(s'.nodes[n])
            && (forall h | h <= s'.nodes[n].nodeState.blockchain && h != [] :: proposerPrecondition(h))
        {
            if isNodeThatTakesStep(s, s', n)
            {
                var inQbftMessages, outQbftMessages :|
                    InstrNodeNextSingleStep(s.nodes[n], inQbftMessages, s'.nodes[n], outQbftMessages);

                lemmaInvInstrNodeStateTypesEx(s.nodes[n], inQbftMessages, s'.nodes[n], outQbftMessages);
                assert isInstrNodeHonest(s, n);
                lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeightHelper1(s, s', n);
                assert s.nodes[n].nodeState.blockchain <= s'.nodes[n].nodeState.blockchain;
                // assert |validators(s'.nodes[n].nodeState.blockchain)| > 0;
                
                forall h | 
                    h <= s'.nodes[n].nodeState.blockchain && |h| > 0
                ensures proposerPrecondition(h);
                {

                    if h <= s.nodes[n].nodeState.blockchain
                    {
                        assert proposerPrecondition(h);
                    }
                    else 
                    {
                        lemmaInvValidInstrDSStateExHelper2(s, s', n, h);
                        assert proposerPrecondition(h);                   
                  

                    }

                }

                assert s'.nodes[n].nodeState.blockchain <= s'.nodes[n].nodeState.blockchain;
                assert |s'.nodes[n].nodeState.blockchain| > 0;
                assert proposerPrecondition(s'.nodes[n].nodeState.blockchain);

                assert |s'.nodes[n].nodeState.blockchain| > 1 ==> s'.nodes[n].nodeState.blockchain[|s'.nodes[n].nodeState.blockchain|-1].header.proposer in validators(s'.nodes[n].nodeState.blockchain[..|s'.nodes[n].nodeState.blockchain|-1]);
            }

        }

        assert validInstrDSStateEx(s');  
    }

    // 2s 3.2.0
    lemma lemmaInvBlockchainConsistencyHelper1(
        s: InstrDSState,
        s': InstrDSState,
        node: Address
    )
    requires validInstrDSStateEx(s)  
    requires InstrDSNextSingle(s, s')
    requires isNodeThatTakesStep(s, s', node);
    requires isInstrNodeHonest(s,node)
    ensures s.nodes[node].nodeState.blockchain <= s'.nodes[node].nodeState.blockchain;
    ensures |s.nodes[node].nodeState.blockchain| <= |s'.nodes[node].nodeState.blockchain| <= |s.nodes[node].nodeState.blockchain|+1;
    {        
    }

    // 2s 3.2.0
    lemma lemmaInvBlockchainConsistencyHelper2(
        b1: Blockchain,
        b2: Blockchain
    ) returns (b: Block)
    requires b1 <= b2 
    requires |b2| == |b1| + 1
    ensures b1 + [b] == b2
    {
        b := b2[|b2| - 1];
    } 

    // 52s 3.2.0
    lemma {:fuel validators, 0, 0}  lemmaInvBlockchainConsistencyHelper4(
        s: InstrDSState,
        s': InstrDSState,
        node: Address,
        n: Address
    )
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invBlockchainConsistency(s)
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)    
    requires InstrDSNextSingle(s, s')
    requires isNodeThatTakesStep(s, s', node);
    requires isInstrNodeHonest(s,node)
    requires  isInstrNodeHonest(s, n)
    requires  s.nodes[node].nodeState.blockchain != s'.nodes[node].nodeState.blockchain
    requires |s.nodes[n].nodeState.blockchain| > |s.nodes[node].nodeState.blockchain|
    ensures consistentBlockchains(s'.nodes[node].nodeState.blockchain, s'.nodes[n].nodeState.blockchain);
    {
        lemmaIndInvForConsistency(s, s');
        lemmaInvValidInstrDSStateEx(s, s');
        // assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s);
        // lemmaIndInvInstrNodeStateLifterToInstrDSState(s, s');
        // assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s');
        lemmaInvBlockchainConsistencyHelper1(s, s', node);        
        assert   |s'.nodes[node].nodeState.blockchain| == |s.nodes[node].nodeState.blockchain|+1;
        var b := lemmaInvBlockchainConsistencyHelper2(s.nodes[node].nodeState.blockchain, s'.nodes[node].nodeState.blockchain);        
        assert b in s'.nodes[node].nodeState.blockchain;
        var i:= |s'.nodes[node].nodeState.blockchain| - 1;
        assert b == s'.nodes[node].nodeState.blockchain[i];
        assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(s.nodes[node]);
        assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(s'.nodes[node]);
        assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(s'.nodes[node], i);
        var bm :|
            && bm in s'.nodes[node].nodeState.messagesReceived
            && bm.NewBlock?
            && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
            && bm.block.header.height == i 
            && ValidNewBlock(s'.nodes[node].nodeState.blockchain[..i], bm.block);
    
        var b' := s.nodes[n].nodeState.blockchain[i];
        assert b' in s.nodes[n].nodeState.blockchain;
        assert b' in s'.nodes[n].nodeState.blockchain;
        assert b' == s'.nodes[n].nodeState.blockchain[i];
        assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(s'.nodes[n]);
        assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(s'.nodes[n], i);
        var bm' :|
            && bm' in s'.nodes[n].nodeState.messagesReceived
            && bm'.NewBlock?
            && areBlocksTheSameExceptForTheCommitSealsAndRound(bm'.block, b')
            && bm'.block.header.height == i 
            && ValidNewBlock(s'.nodes[n].nodeState.blockchain[..i], bm'.block);

        assert i == |s.nodes[node].nodeState.blockchain|;

        assert s'.nodes[n].nodeState.blockchain[..i] == s.nodes[n].nodeState.blockchain[..i];
        assert s.nodes[node].nodeState.blockchain <= s'.nodes[node].nodeState.blockchain;
        assert s'.nodes[node].nodeState.blockchain[..i] == s.nodes[node].nodeState.blockchain[..i];

        lemmaPrefixesOfConsistentBlockchainsAreConsistenAndIfOfTheSameLengthThenAreAlsoFromBlockchainToRawBlockchainEquivalentAndAreBlockchainsTheSameExceptForTheCommitSealsAndRound(
            s'.nodes[n].nodeState.blockchain[..i],
            s'.nodes[node].nodeState.blockchain[..i],
            s.nodes[n].nodeState.blockchain,
            s.nodes[node].nodeState.blockchain
        );

        assert consistentBlockchains(s'.nodes[n].nodeState.blockchain[..i], s'.nodes[node].nodeState.blockchain[..i]);
        lemmaFromBlockchainToRawBlockchainEquivalencePreservesValidNewBlock(bm'.block, s'.nodes[n].nodeState.blockchain[..i], s'.nodes[node].nodeState.blockchain[..i]);

        assert ValidNewBlock(s'.nodes[node].nodeState.blockchain[..i], bm'.block);
        lemmaInvMessagesReceivedByHonestNodesAreInAllMesssagesSentIncSentToItselfWithoutRecipient(s');
        assert bm in allMesssagesSentIncSentToItselfWithoutRecipient(s'); 
        assert bm' in allMesssagesSentIncSentToItselfWithoutRecipient(s');           

        lemmaInvBlockchainConsistencyImpliesInvBlockchainConsistencyUpToHeight(s, i);
        
        lemmaInvAnyTwoValidNewBlockMessagesForTheSameHeightAreConsistent(
            s',
            bm,
            bm',
            i,
            node
        );

        assert areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, bm'.block);
        assert areBlocksTheSameExceptForTheCommitSealsAndRound(b, b');
        assert s'.nodes[node].nodeState.blockchain == s'.nodes[node].nodeState.blockchain[..i] + [b];
        lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper4(
            s'.nodes[n].nodeState.blockchain,
            b',
            i
        );
        assert s'.nodes[n].nodeState.blockchain[..i+1] == s'.nodes[n].nodeState.blockchain[..i] + [b'];
        lemmaAreBlocksTheSameExceptForTheCommitSealsAndRoundIsReflexiveAndAreBlocksTheSameExceptForTheCommitSealsAndRoundAndFromBlockchainToRawBlockchainEquivalenceAreEquivalent();
        lemmaAddBlocksThatAreTheSameExceptForCommitSealsAndRoundNumberToBlockchainsThatAreTheSameExceptForCommitSealsAndRoundNumberPreservesFromBlockchainToRawBlockchainEquivalence(
            b,
            b',
            s'.nodes[node].nodeState.blockchain[..i],
            s'.nodes[n].nodeState.blockchain[..i]
        );
        assert fromBlockchainToRawBlockchain(
                s'.nodes[node].nodeState.blockchain) ==
                fromBlockchainToRawBlockchain(
                s'.nodes[n].nodeState.blockchain[..i+1]);

        lemmaFromBlockchainToRawBlockchainEquivalenceImpliesConsistentencyWithExtensionOfOneOfTheBlockchains(
            s'.nodes[node].nodeState.blockchain,
            s'.nodes[n].nodeState.blockchain[..i+1],
            s'.nodes[n].nodeState.blockchain
        );
        assert consistentBlockchains(s'.nodes[node].nodeState.blockchain, s'.nodes[n].nodeState.blockchain);
    }

    // 23s 3.2.0
    lemma {:fuel validators, 0, 0}  lemmaInvBlockchainConsistency(
        s: InstrDSState,
        s': InstrDSState
    )
    requires validInstrDSStateEx(s)  
    requires indInvForConsistency(s) 
    requires invBlockchainConsistency(s)
    requires invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
    requires invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)    
    requires InstrDSNextSingle(s, s')
    ensures invBlockchainConsistency(s')
    {

        if s != s'
        {
            var node :| isNodeThatTakesStep(s, s', node);

            var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node);  

  

            if isInstrNodeHonest(s,node)
            {
                lemmaIndInvForConsistency(s, s');
                lemmaInvValidInstrDSStateEx(s, s');
                // assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s);
                // lemmaIndInvInstrNodeStateLifterToInstrDSState(s, s');
                // assert liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s');
                lemmaInvBlockchainConsistencyHelper1(s, s', node);
                assert s.nodes[node].nodeState.blockchain <= s'.nodes[node].nodeState.blockchain;
                assert |s.nodes[node].nodeState.blockchain| <= |s'.nodes[node].nodeState.blockchain| <= |s.nodes[node].nodeState.blockchain|+1;

                if s.nodes[node].nodeState.blockchain == s'.nodes[node].nodeState.blockchain
                {
                    assert invBlockchainConsistency(s');                  
                }
                else
                {
                    assert   |s'.nodes[node].nodeState.blockchain| == |s.nodes[node].nodeState.blockchain|+1;

                    forall n |
                            && isInstrNodeHonest(s, n)
                    ensures consistentBlockchains(s'.nodes[node].nodeState.blockchain, s'.nodes[n].nodeState.blockchain);
                    ensures consistentBlockchains(s'.nodes[n].nodeState.blockchain, s'.nodes[node].nodeState.blockchain);
                    {
                        if |s.nodes[n].nodeState.blockchain| > |s.nodes[node].nodeState.blockchain|
                        {
                            lemmaInvBlockchainConsistencyHelper4(s, s', node, n);
                            // assume consistentBlockchains(s'.nodes[node].nodeState.blockchain, s'.nodes[n].nodeState.blockchain);
                        }
                        else
                        {
                            if n != node
                            {
                                assert s.nodes[n].nodeState.blockchain == s'.nodes[n].nodeState.blockchain;
                                lemmaConsistencyWithABlockchainImpliesConsistencyWithOneOfItsExtensions(
                                    s.nodes[n].nodeState.blockchain,
                                    s.nodes[node].nodeState.blockchain,
                                    s'.nodes[node].nodeState.blockchain
                                );

                                assert consistentBlockchains(s'.nodes[node].nodeState.blockchain, s.nodes[n].nodeState.blockchain );
                                assert consistentBlockchains(s.nodes[n].nodeState.blockchain, s'.nodes[node].nodeState.blockchain );
                                assert consistentBlockchains(s'.nodes[n].nodeState.blockchain, s'.nodes[node].nodeState.blockchain );                                
                            }
                            else
                            {
                                assert consistentBlockchains(s'.nodes[n].nodeState.blockchain, s'.nodes[node].nodeState.blockchain );                                 
                            }
                            assert consistentBlockchains(s'.nodes[node].nodeState.blockchain, s'.nodes[n].nodeState.blockchain );
                            
                        }

                    }
                    

                    assert invBlockchainConsistency(s');

                }

                assert invBlockchainConsistency(s');
            }
            else
            {
                assert invBlockchainConsistency(s');
            }
        
        }
        else {
            assert invBlockchainConsistency(s');
        }
    }   

    // 2s 3.2.0
    lemma lemmaInvBlockchainConsistencyWithAllInductiveInvariants(
        s: InstrDSState,
        s': InstrDSState
    )
    requires allIndInv(s)
    requires invBlockchainConsistency(s)
    requires InstrDSNextSingle(s, s')
    ensures allIndInv(s')
    ensures invBlockchainConsistency(s') 
    {
        lemmaIndInvForConsistency(s, s');
        lemmaInvValidInstrDSStateEx(s, s');
        lemmaInvBlockchainConsistency(s,s');
        lemmaInvIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s, s');
        lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidators(s, s');
    }

    // 25s 3.2.0
    lemma lemmaIndInvIsTrueInInit(
        s: InstrDSState,
        configuration:Configuration
    )
    requires InstrDSInit(s, configuration)
    ensures invBlockchainConsistency(s)
    ensures allIndInv(s)
    {
        forall n | isInstrNodeHonest(s, n)
        ensures indInvInstrNodeState(s.nodes[n])
        ensures validInstrStateEx(s.nodes[n])        
        {
            assert InstrNodeInit(s.nodes[n],configuration,n);
            lemmaInitInstrNodeState(s.nodes[n], configuration, n);

        }
    }                
}