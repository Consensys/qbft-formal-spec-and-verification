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
include "instr_node_state_invariants.dfy"
include "quorum.dfy"
include "general_lemmas.dfy"
include "../theorems_defs.dfy"


// TODO: Rename file and module
module EEAInstrDSStateInvariants
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
    import opened EEANetworkingInvariantsLemmas
    import opened EEATheoremsDefs

          
    predicate invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(
        s: InstrDSState
    )
    {
        forall n | isInstrNodeHonest(s,n) :: 
            var messagesReceived := s.nodes[n].nodeState.messagesReceived;
            forall m1, m2 |   
                            && m1 in messagesReceived
                            && m2 in messagesReceived
                            && m1.Prepare?
                            && m2.Prepare?
                            &&  var uPayload1 := m1.preparePayload.unsignedPayload;
                                var uPayload2 := m2.preparePayload.unsignedPayload;
                            &&  uPayload1.height == uPayload2.height
                            &&  uPayload1.round == uPayload2.round
                            && recoverSignedPrepareAuthor(m1.preparePayload) ==  recoverSignedPrepareAuthor(m2.preparePayload)
                            && isInstrNodeHonest(s,recoverSignedPrepareAuthor(m1.preparePayload))
                        ::
                            var uPayload1 := m1.preparePayload.unsignedPayload;
                            var uPayload2 := m2.preparePayload.unsignedPayload;
                            uPayload1.digest == uPayload2.digest  
    }

    predicate pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s: InstrDSState, b:Block, csAuthor: Address)
    requires isInstrNodeHonest(s, csAuthor)
    {
        exists cm:QbftMessage, b', p:QbftMessage ::    
            && cm in getAllMessagesSentByTheNode(s, csAuthor)
            && p.Proposal?
            && p in s.nodes[csAuthor].proposalsAccepted
            && p.proposedBlock == b'
            && areBlocksTheSameExceptForTheCommitSeals(b',b)
            && cm.Commit?
            && cm.commitPayload.unsignedPayload.height == b.header.height
            && cm.commitPayload.unsignedPayload.round == b.header.roundNumber
            && cm.commitPayload.unsignedPayload.digest == digest(b') 
    }      

    predicate invForEveryCommitSealsSignedByAnHonestNodeExcludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(
        s: InstrDSState
    )
    {
        forall b, cs, a |
            && cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent))
            && isInstrNodeHonest(s, a)
            && a == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
                ::
            pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,b,a)
    }  

    predicate invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(
        s: InstrDSState
    )
    {
        forall b, cs, a |
            && cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && isInstrNodeHonest(s, a)
            && a == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
                ::
            pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,b,a)
    }      

    predicate invCommitSealsInAdversaryMessagesReceivedAreSubsetOfCommitSealsSent(
        s: InstrDSState
    )  
    {
        getCommitSeals(s.adversary.messagesReceived)
        <=
        getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent))
    }

    // TODO: Change name and position?
    predicate pBlockchainConsistencyUpToHeight(
        s:InstrDSState,
        h: nat
    )
    {
        forall n1,n2 |  && isInstrNodeHonest(s,n1)
                        && isInstrNodeHonest(s,n2)
                     ::
                     consistentBlockchains(
                        truncateSeq(s.nodes[n1].nodeState.blockchain, h),
                        truncateSeq(s.nodes[n2].nodeState.blockchain, h))
    }     

    predicate invTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigest(
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
    {
        (
            && isInstrNodeHonest(s,n1)
            && isInstrNodeHonest(s,n2)
            && |s.nodes[n1].nodeState.blockchain| >= h
            && |s.nodes[n2].nodeState.blockchain| >= h
            && pBlockchainConsistencyUpToHeight(s, h)   
            && isQuorumOfPrepares(h,r,d1,QofP1,s.nodes[n1].nodeState.messagesReceived, s.nodes[n1].nodeState.blockchain)
            && isQuorumOfPrepares(h,r,d2,QofP2,s.nodes[n2].nodeState.messagesReceived, s.nodes[n2].nodeState.blockchain)  
        )
        ==>
        (
            d1 == d2 
        )
    }   

    predicate invTwoValidQuorumsForTheSameRoundPrepareOnTheSameDigestForAll(s:InstrDSState)
    {
        forall h,r, QofP1, QofP2, d1, d2,n1,n2 ::
            && isInstrNodeHonest(s,n1)
            && isInstrNodeHonest(s,n2)
            && |s.nodes[n1].nodeState.blockchain| >= h
            && |s.nodes[n2].nodeState.blockchain| >= h
            && pBlockchainConsistencyUpToHeight(s, h)            
            && isQuorumOfPrepares(h,r,d1,QofP1,s.nodes[n1].nodeState.messagesReceived, s.nodes[n1].nodeState.blockchain)
            && isQuorumOfPrepares(h,r,d2,QofP2,s.nodes[n2].nodeState.messagesReceived, s.nodes[n2].nodeState.blockchain)    

            ==>
            
            d1 == d2        
    }       

    predicate invTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigest(
        s:InstrDSState,
        n1: Address,
        n2: Address,
        m1: QbftMessage,
        m2: QbftMessage,
        h: nat,
        r: nat           
    )
    {
        (
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
        ) ==>  
        m1.commitPayload.unsignedPayload.digest == m2.commitPayload.unsignedPayload.digest         
    }    

    predicate pMessagesAreCommitMessagesForSameRoundSendByTwoHonestValidators(
        s:InstrDSState, n1:Address, n2:Address, m1:QbftMessage, m2:QbftMessage, h:nat, r:nat
    )
    {
        && isInstrNodeHonest(s,n1)
        && isInstrNodeHonest(s,n2)
        && m1 in getAllMessagesSentByTheNode(s, n1)
        && m2 in getAllMessagesSentByTheNode(s, n2)
        && pBlockchainConsistencyUpToHeight(s, h)
        && m1.Commit?
        && m2.Commit?
        &&  var uPayload1 := m1.commitPayload.unsignedPayload;
            var uPayload2 := m2.commitPayload.unsignedPayload;
        && uPayload1.height == uPayload2.height == h 
        && uPayload1.round == uPayload2.round == r 
    }  

    predicate intTwoCommitMessageForTheSameRoundSentByTwoHonestValidatorsHaveTheSameDigestForAll(
        s:InstrDSState
    )
    {
        forall n1:Address, n2:Address, m1:QbftMessage, m2:QbftMessage, h:nat, r:nat ::
            pMessagesAreCommitMessagesForSameRoundSendByTwoHonestValidators(s,n1,n2,m1,m2,h,r)
            ==> 
            m1.commitPayload.unsignedPayload.digest == m2.commitPayload.unsignedPayload.digest           
    }    

    predicate invTwoValidQuorumOfCommitSealsForSameRoundAreForTheSameBlockExceptForCommitSealsNotForAll(
        s:InstrDSState,
        b1: Block, 
        b2:Block,
        n1: Address,
        n2: Address, 
        h:nat 
    )
    {
        (      
            && isInstrNodeHonest(s,n1)
            && isInstrNodeHonest(s,n2)
            && |s.nodes[n1].nodeState.blockchain| >= h
            && |s.nodes[n2].nodeState.blockchain| >= h
            && pBlockchainConsistencyUpToHeight(s, h)
            && b1.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && b2.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b1)
            && ValidNewBlock(s.nodes[n2].nodeState.blockchain[..h],b2)
            && b1.header.roundNumber == b2.header.roundNumber
        ) ==>
        areBlocksTheSameExceptForTheCommitSeals(b1, b2)         
    }    

    predicate invValidBlockAndBlockIncludedInValidPropsosalJustificationForNextRoundAreTheSameExceptForCommitSeals(
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
    {
        (
            && isInstrNodeHonest(s,n1)
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
        ) ==>    
        (
            && areBlocksTheSameExceptForTheCommitSealsAndRound(b, b')   
            && b'.header.roundNumber == b.header.roundNumber + 1   
        )     
    }    

    predicate invValidBlockAndBlockIncludedInValidPropsosalForNextRoundAreTheSameExceptForCommitSeals(
        s: InstrDSState,
        h: nat,
        n1: Address
    )    
    requires n1 in s.nodes
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h]) 
    {
        forall 
            // bm, 
            b: Block, 
            // h:nat,  
            pm
                ::
            (
                && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h], b)
                && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
                && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                && pm.proposalPayload.unsignedPayload.round == b.header.roundNumber+1               
            ) ==> 
            (
                && areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm.proposedBlock)   
                && pm.proposedBlock.header.roundNumber == b.header.roundNumber + 1
            ) 
    }    

    predicate invIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidBlockForTheSameRoundIsAlsoConsistentWithThatBlock(
        s: InstrDSState,
        h: nat,
        r: nat,
        n1: Address,
        b: Block
    )
    requires n1 in s.nodes
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])     
    {
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
        ) ==>
        (
            forall b':Block | 
                    && b'.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                    && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b')
                    && b'.header.roundNumber == r
                ::
            areBlocksTheSameExceptForTheCommitSealsAndRound(b, b')
        )     
    }    

    predicate invIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockThenAnyValidQuorumOfPreparesForTheSameRoundIsAlsoConsistentWithThatBlock(
        s: InstrDSState,
        r: nat,
        h: nat,
        n1: Address,
        b: Block
    )
    requires n1 in s.nodes
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])     
    {
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
        ) ==>
        (
            var V := validators(s.nodes[n1].nodeState.blockchain[..h]);
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
            ::
                areBlocksTheSameExceptForTheCommitSealsAndRound(b, b')
        )        
    }    

    predicate     invIfAllValidProposalsSentForTheSameRoundAreConsistentWithABlockAnyValidQuorumOfPreparesForTheSameRoundIsForABlockWithProposerInTheSetOfValidators(
        s: InstrDSState,
        r: nat,
        h: nat,
        n1: Address
    )
    requires n1 in s.nodes
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])     
    {
        (
            forall pm ::
                (
                    && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                    && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
                    && pm.proposalPayload.unsignedPayload.round == r
                )  ==>
                (
                    && pm.proposedBlock.header.proposer in validators(s.nodes[n1].nodeState.blockchain[..h])
                )
        ) ==>
        (
            var V := validators(s.nodes[n1].nodeState.blockchain[..h]);
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
            ::
                && b'.header.proposer in validators(s.nodes[n1].nodeState.blockchain[..h]) 
        )       
    }    

    predicate invAnyValidQuorumOfPreparesForTheSameRoundAsAValidBlockIsForABlockConsistentWithTheValidBlock(
        s: InstrDSState,
        // r: nat,
        h: nat,
        n1: Address,
        b: Block
    )
    requires n1 in s.nodes
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])     
    {
        (
            && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h], b)
        ) ==>
        (
            var V := validators(s.nodes[n1].nodeState.blockchain[..h]);
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
            ::
                areBlocksTheSameExceptForTheCommitSealsAndRound(b, b')
        )         
    }    

    predicate invTheHighestRoundChangeInAValidProposalForRoundHigherThanThatOfAValidBlockHasRoundAtLeastAsHighAsThatOfTheValidBlock(
        s: InstrDSState,
        b: Block,
        r: nat,
        h:nat, 
        pm: QbftMessage,
        n1: Address,
        rcm: SignedRoundChange
    )
    requires n1 in s.nodes
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])     
    {
        (   
            && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b)
            && b.header.roundNumber == r    
            && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
            && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
            && pm.proposalPayload.unsignedPayload.round > r
            && rcm in pm.proposalJustification
            && isHighestPrepared(rcm,pm.proposalJustification)
        ) ==>
        (
            &&  !((forall m | m in pm.proposalJustification :: && !optionIsPresent(m.unsignedPayload.preparedRound)
                                                    && !optionIsPresent(m.unsignedPayload.preparedValue)))  
            && rcm.unsignedPayload.preparedRound.Optional?
            && rcm.unsignedPayload.preparedRound.value >= r
        )
    }    

    predicate invAValidProposalForRoundHigherThanThatOfAValidBlockContainsAtLeastOneRoundChangeMessageWithNoNullPreparedRoundAndValue(
        s: InstrDSState,
        b: Block,
        r: nat,
        h:nat, 
        pm: QbftMessage,
        n1: Address
    )
    requires n1 in s.nodes
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])     
    {
        (
            && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b)
            && b.header.roundNumber == r    
            && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
            && isValidProposalJustification(pm, s.nodes[n1].nodeState.blockchain[..h])
            && pm.proposalPayload.unsignedPayload.round > r
        ) ==>
        !((forall m | m in pm.proposalJustification ::  && !optionIsPresent(m.unsignedPayload.preparedRound)
                                                        && !optionIsPresent(m.unsignedPayload.preparedValue))) 
    }    

    predicate pAnyValidProposalMessageForTheProvidedRoundIsForABlockConsistentWithTheProvidedBlock(
        s: InstrDSState,
        r':nat,
        blockchain: Blockchain,
        b: Block
    )
    requires proposerPrecondition(blockchain)    
    {
            (
                forall 
                    pm
                        ::
                    (
                        && isValidProposalJustification(pm, blockchain)
                        && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                        && pm.proposalPayload.unsignedPayload.round == r'              
                    ) ==> 
                    (
                        && areBlocksTheSameExceptForTheCommitSealsAndRound(b, pm.proposedBlock)   
                        && pm.proposedBlock.header.roundNumber == r'
                    )
            )
    }

    predicate pAnyValidProposalMessageForTheProvidedRoundRangeIsForABlockConsistentWithTheProvidedBlock(
        r2: nat,
        s: InstrDSState,
        blockchain: Blockchain,
        r: nat,
        b: Block
    )
    requires proposerPrecondition(blockchain)    
    {
            forall r':nat|
                        inclusiveRange(r+1, r', r2)
                    ::
                pAnyValidProposalMessageForTheProvidedRoundIsForABlockConsistentWithTheProvidedBlock(s, r', blockchain, b)
    }    

    predicate invAnyValidProposalMessageWithRoundHigherThanThatOfAValidBlockIsForABlockConsistentWithTheValidBlock(
        s: InstrDSState,
        h: nat,
        r: nat,
        r2: nat,
        n1: Address,
        b: Block
    )
    requires n1 in s.nodes
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])     
    {
        (
            && r2 >= r
            && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h], b)
            && b.header.roundNumber == r
        ) ==>
        pAnyValidProposalMessageForTheProvidedRoundRangeIsForABlockConsistentWithTheProvidedBlock(r2, s, s.nodes[n1].nodeState.blockchain[..h], r, b)        
    }    

    predicate invAnyValidBlockForRoundAtLeastAsHighAsThatOfAValidBlockIsConsistentWithTheValidBlock(
        s: InstrDSState,
        b: Block,
        r: nat,
        r2: nat,
        h:nat, 
        n1: Address
    )
    requires n1 in s.nodes
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])     
    {
        (    
            && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b)
            && b.header.roundNumber == r    
            && r2 >= r
        ) ==>
        (
            forall b':Block | 
                    &&  b'.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                    && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b') 
                    &&  r <= b'.header.roundNumber <= r2  
            ::
                areBlocksTheSameExceptForTheCommitSealsAndRound(b, b')
        )
    }    

    predicate invAnyTwoValidNewBlockMessagesForTheSameHeightAreConsistent(
        s: InstrDSState,
        bm: QbftMessage,
        bm': QbftMessage,
        h:nat, 
        n1: Address
    )   
    requires n1 in s.nodes
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])       
    {
        (   
            && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
            && validNewBlockMessage(s.nodes[n1].nodeState.blockchain[..h],bm)
            && bm' in allMesssagesSentIncSentToItselfWithoutRecipient(s)
            && validNewBlockMessage(s.nodes[n1].nodeState.blockchain[..h],bm')
        ) ==>
        areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, bm'.block)
    }    

    predicate invAnyTwoValidNewBlockMessagesWithCommitSealsIncludedInAllCommitSealsSentForTheSameHeightAreConsistent(
        s: InstrDSState,
        b: Block,
        b': Block,
        h:nat, 
        n1: Address
    ) 
    requires n1 in s.nodes
    requires |s.nodes[n1].nodeState.blockchain| >= h
    requires proposerPrecondition(s.nodes[n1].nodeState.blockchain[..h])     
    {
        (
            && b.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b)
            && b'.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
            && ValidNewBlock(s.nodes[n1].nodeState.blockchain[..h],b')
        ) ==>
        areBlocksTheSameExceptForTheCommitSealsAndRound(b, b')
    }    

    predicate pTheProposerInAnyValidProposalForTheGivenRoundIsInTheSetOfValidators(
        s: InstrDSState,
        r':nat,
        blockchain: Blockchain
    )
    requires proposerPrecondition(blockchain)    
    {
        forall 
            pm
                ::
            (
                && isValidProposalJustification(pm, blockchain)
                && pm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                && pm.proposalPayload.unsignedPayload.round == r'              
            ) ==> 
            (
                && pm.proposedBlock.header.proposer in validators(blockchain)
            )
    }

    predicate invTheProposerInAnyValidProposalUpToTheGivenRoundIsInTheSetOfValidators(
        r2: nat,
        s: InstrDSState,
        blockchain: Blockchain
    )
    requires proposerPrecondition(blockchain)    
    {
            forall r':nat|
                        inclusiveRange(0, r', r2)
                    ::
                pTheProposerInAnyValidProposalForTheGivenRoundIsInTheSetOfValidators(s, r', blockchain)
    }    

    predicate invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(
        s: InstrDSState
    )
    {
        forall bm, blockchain |
                // && isInstrNodeHonest(s, n)
                && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                && validNewBlockMessage(blockchain,bm)
                && |blockchain| > 0
                ::
                (
                exists n ::
                    && isInstrNodeHonest(s, n) 
                    && |s.nodes[n].nodeState.blockchain| >= |blockchain|
                )
    }    

    predicate invTheProposerOfAnyValidBlockIsInTheSetOfValidators(
        s: InstrDSState
    )
    {
        forall bm, n |
                && isInstrNodeHonest(s, n)
                && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
                && validNewBlockMessage(s.nodes[n].nodeState.blockchain,bm)
                ::
                bm.block.header.proposer in validators(s.nodes[n].nodeState.blockchain)
    }

    predicate pBlockIsAValidBlockOfAnHonestBlockchain(
        s: InstrDSState,
        bm: QbftMessage,
        n: Address,
        blockchain: Blockchain
    )
    {
        && isInstrNodeHonest(s, n)
        && blockchain <= s.nodes[n].nodeState.blockchain
        && |blockchain| > 0
        && bm in allMesssagesSentIncSentToItselfWithoutRecipient(s)
        && validNewBlockMessage(blockchain,bm)
    }

    predicate invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(
        s: InstrDSState
    )
    {
        forall bm, n, blockchain |
                pBlockIsAValidBlockOfAnHonestBlockchain(s, bm, n, blockchain)
                ::
                bm.block.header.proposer in validators(blockchain)
    }    

    predicate invBlockchainConsistency(
        s:InstrDSState
    )
    {
        forall n1,n2 |  && isInstrNodeHonest(s,n1)
                        && isInstrNodeHonest(s,n2)
                     ::
                     consistentBlockchains(s.nodes[n1].nodeState.blockchain, s.nodes[n2].nodeState.blockchain)
    }
  
    // TODO: Rename
    predicate indInvForConsistency(
        s: InstrDSState
    )
    {
        && liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
        && indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
        && invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
        && invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
        && invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
        && invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
        && invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
        && invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
        && invProposalAcceptedByHonestNodesHaveBeenSent(s)
        && invConstantFields(s)
        && invIfPreparePaylodSentThenPrepareSent(s)  
        && invIfRoundChangePaylodSentThenRoundChangeSent(s)
        && invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
        && invMessagesReceivedByHonestNodesHaveBeenSent(s)      
    }

    predicate allIndInv(s: InstrDSState) 
    {
        && validInstrDSStateEx(s)  
        && indInvForConsistency(s) 
        && invIfValidNewBlockMessageThenThereExistsHonestBlockchainForThatHeight(s)
        && invTheProposerOfAnyValidBlockInAnHonestBlockchainIsInTheSetOfValidators(s)        
    }    
 
    // TODO: Reorder from here
    predicate invIfRoundChangePaylodSentThenRoundChangeSentSingleNode(
        s: InstrDSState,
        n: Address
    )
    requires n in s.nodes
    {
        forall srcp: SignedPayload | 
            && srcp.SignedRoundChangePayload? 
            && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,n)), n) 
            ::
            (
                exists rcm: QbftMessage :: 
                    && rcm in getAllMessagesSentByTheNode(s,n)
                    && rcm.RoundChange?
                    && rcm.roundChangePayload == srcp.signedRoundChangePayload
            )
    }

    predicate invIfRoundChangePaylodSentThenRoundChangeSent(
        s:InstrDSState
    )
    {
        forall n | 
            && isInstrNodeHonest(s, n) 
            ::
            invIfRoundChangePaylodSentThenRoundChangeSentSingleNode(s, n)
    }

    predicate invIfPreparePaylodSentThenPrepareSentSingleNode(
        s: InstrDSState,
        n: Address
    )
    requires n in s.nodes
    {
        forall srcp: SignedPayload | 
            && srcp.SignedPreparePayload? 
            && srcp in filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s,n)), n) 
            ::
            (
                exists rcm: QbftMessage :: 
                    && rcm in getAllMessagesSentByTheNode(s,n)
                    && rcm.Prepare?
                    && rcm.preparePayload == srcp.signedPreparePayload
            )
    }

    predicate invIfPreparePaylodSentThenPrepareSent(
        s:InstrDSState
    )
    {
        forall n | 
            && isInstrNodeHonest(s, n) 
            ::
            invIfPreparePaylodSentThenPrepareSentSingleNode(s, n)
    } 

    predicate invProposalAcceptedByANodesHaveBeenSent(
        s: InstrDSState,
        n: Address
    ) 
    requires n in s.nodes
    {
        s.nodes[n].proposalsAccepted <= allMesssagesSentIncSentToItselfWithoutRecipient(s) // fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent)
    }    

    predicate invProposalAcceptedByHonestNodesHaveBeenSent(
        s: InstrDSState
    ) 
    {
        forall n | 
                        && isInstrNodeHonest(s, n) 
                    ::
                        invProposalAcceptedByANodesHaveBeenSent(s, n)
    }

}