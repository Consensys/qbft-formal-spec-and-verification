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
// include "networking_invariants.dfy"

module EEAInstrNodeStateInvariants
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
    // import opened EEANetworkingInvariants


    predicate validInstrStateEx(s:InstrNodeState)
    {
        && validInstrState(s)
        && (forall h | h <= s.nodeState.blockchain && h != [] :: proposerPrecondition(h))
    }

    predicate indInvInstrNodeStateTypes(
        s: InstrNodeState
    )
    {
        && (forall m | m in s.proposalsAccepted :: && m.Proposal?)
    }

    lemma lemmaInvInstrNodeStateTypesEx(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    )        
    requires validInstrState(current)
    // requires indInvInstrNodeStateTypes(current)
    // requires indInvInstrNodeStateProposalsAccepted(current)
    // requires invInstrNodeStateProposalsAccepted(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)
    // ensures indInvInstrNodeStateTypes(next)
    // ensures indInvInstrNodeStateProposalsAccepted(next)
    // ensures invInstrNodeStateProposalsAccepted(next)  
    ensures && (optionIsPresent(next.nodeState.proposalAcceptedForCurrentRound) ==> optionGet(next.nodeState.proposalAcceptedForCurrentRound).Proposal?);
    ensures && (!optionIsPresent(next.nodeState.lastPreparedRound) <==> !optionIsPresent(next.nodeState.lastPreparedBlock));
    ensures && (optionIsPresent(next.nodeState.lastPreparedRound) ==>
            exists QofP ::
                && QofP <= validPreparesForHeightRoundAndDigest(
                                next.nodeState.messagesReceived,
                                |next.nodeState.blockchain|,
                                optionGet(next.nodeState.lastPreparedRound),
                                digest(optionGet(next.nodeState.lastPreparedBlock)),
                                validators(next.nodeState.blockchain))
                && |QofP| >= quorum(|validators(next.nodeState.blockchain)|)
    );
    ensures |next.nodeState.blockchain| > 0;    
    {
        assert && (optionIsPresent(next.nodeState.proposalAcceptedForCurrentRound) ==> optionGet(next.nodeState.proposalAcceptedForCurrentRound).Proposal?);
        assert && (!optionIsPresent(next.nodeState.lastPreparedRound) <==> !optionIsPresent(next.nodeState.lastPreparedBlock));
        assert && (optionIsPresent(next.nodeState.lastPreparedRound) ==>
                exists QofP ::
                    && QofP <= validPreparesForHeightRoundAndDigest(
                                    next.nodeState.messagesReceived,
                                    |next.nodeState.blockchain|,
                                    optionGet(next.nodeState.lastPreparedRound),
                                    digest(optionGet(next.nodeState.lastPreparedBlock)),
                                    validators(next.nodeState.blockchain))
                    && |QofP| >= quorum(|validators(next.nodeState.blockchain)|)
        );
        assert |next.nodeState.blockchain| > 0;

    }  

    predicate indInvInstrNodeStateProposalsAccepted(
        s: InstrNodeState
    )
    requires indInvInstrNodeStateTypes(s)
    {
        && (forall m | m  in s.proposalsAccepted :: 
                    && m.proposalPayload.unsignedPayload.height <= |s.nodeState.blockchain|
                    && m.proposalPayload.unsignedPayload.digest == digest(m.proposedBlock))
        && 
            (
            var propForCurrentHeight := set m | m in s.proposalsAccepted && m.proposalPayload.unsignedPayload.height == |s.nodeState.blockchain|;
            || propForCurrentHeight == {} 
            || (
                && propForCurrentHeight != {}
                && var rounds := set m | m in propForCurrentHeight :: m.proposalPayload.unsignedPayload.round;
                lemma_MapSubsetCardinalityOverNoInjective(propForCurrentHeight, rounds, (m:QbftMessage) requires m.Proposal? => m.proposalPayload.unsignedPayload.round);
                && s.nodeState.round >= 
                    
                    intsetmax(rounds)

                && (
                    s.nodeState.proposalAcceptedForCurrentRound.None?
                        ==>
                        s.nodeState.round >
                    
                    intsetmax(rounds)
                )
                )
            )

        && (s.nodeState.proposalAcceptedForCurrentRound.Optional? ==> 
                && s.nodeState.proposalAcceptedForCurrentRound.value.Proposal?
                && s.nodeState.round == s.nodeState.proposalAcceptedForCurrentRound.value.proposalPayload.unsignedPayload.round 
                && |s.nodeState.blockchain| == s.nodeState.proposalAcceptedForCurrentRound.value.proposalPayload.unsignedPayload.height)

        && (s.nodeState.proposalAcceptedForCurrentRound.Optional? ==>
                s.nodeState.proposalAcceptedForCurrentRound.value in s.proposalsAccepted) 
    }

    predicate invInstrNodeStateProposalsAccepted(
        s: InstrNodeState
    )
    requires indInvInstrNodeStateTypes(s)
    {
        && (forall m1,m2 |  && m1 in s.proposalsAccepted
                            && m2 in s.proposalsAccepted
                        ::
                            && m1.proposedBlock != m2.proposedBlock
                            ==>
                            (  var uPayload1 := m1.proposalPayload.unsignedPayload;
                                var uPayload2 := m2.proposalPayload.unsignedPayload;
                            || uPayload1.height != uPayload2.height
                            || uPayload1.round != uPayload2.round))  

        && (forall m |  m in s.proposalsAccepted
                    ::
                        && m.proposedBlock.header.roundNumber == m.proposalPayload.unsignedPayload.round
                        && m.proposedBlock.header.height == m.proposalPayload.unsignedPayload.height)
    }


    lemma lemmaInvInstrNodeStateProposalsAccepted(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    )        
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)
    ensures indInvInstrNodeStateTypes(next)
    ensures indInvInstrNodeStateProposalsAccepted(next)
    ensures invInstrNodeStateProposalsAccepted(next)
    {
        var cns := current.nodeState;
        var nns := next.nodeState;

        var crounds := set m | m in current.proposalsAccepted :: m.proposalPayload.unsignedPayload.round;  
        var nrounds := set m | m in next.proposalsAccepted :: m.proposalPayload.unsignedPayload.round;      

        if  nns.proposalAcceptedForCurrentRound.None?
        {
                        
            assert next.proposalsAccepted == current.proposalsAccepted;
        }        
        else 
        {
            var csPropForCurrentHeight := 
                set m | m in current.proposalsAccepted && m.proposalPayload.unsignedPayload.height == |current.nodeState.blockchain|;

            var nsPropForCurrentHeight := 
                set m | m in next.proposalsAccepted && m.proposalPayload.unsignedPayload.height == |next.nodeState.blockchain|;

            var nsRounds := set m | m in nsPropForCurrentHeight :: m.proposalPayload.unsignedPayload.round;

            var csRounds := set m | m in csPropForCurrentHeight :: m.proposalPayload.unsignedPayload.round;

            assert nsRounds == csRounds + {nns.proposalAcceptedForCurrentRound.value.proposalPayload.unsignedPayload.round};

        }          
    }  

    predicate indInvInstrNodeStateAllProposalsAcceptedAreValid(
        s: InstrNodeState
    )  
    requires validInstrState(s)
    requires indInvInstrNodeStateTypes(s)
    {
        s.nodeState.proposalAcceptedForCurrentRound.Optional? ==>
            isValidProposalJustification(s.nodeState.proposalAcceptedForCurrentRound.value, s.nodeState.blockchain)
    }   


    lemma leammIndInvInstrNodeStateAllProposalsAcceptedAreValid
    (
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>  
    )
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateAllProposalsAcceptedAreValid(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)
    ensures indInvInstrNodeStateTypes(next)
    ensures validInstrState(next) ==> indInvInstrNodeStateAllProposalsAcceptedAreValid(next)     
    {
        var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;

        var currentWithNewMessagesReceived :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );        
        if(validInstrState(next))
        {
            if(
                
                
                
                
                || UponProposal(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                
                
                )
            {
                assert current.nodeState.blockchain == next.nodeState.blockchain;
                assert next.nodeState.proposalAcceptedForCurrentRound.Optional?;
                assert indInvInstrNodeStateAllProposalsAcceptedAreValid(next);
            }
            else if(
                || UponPrepare(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                || UponCommit(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                || UponNewBlock(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                || UponRoundTimeout(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                || UponBlockTimeout(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                || UponRoundChange(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                
            )
            {
                assert indInvInstrNodeStateAllProposalsAcceptedAreValid(next);
            }
            else if(currentWithNewMessagesReceived == next.nodeState)
            {
                // assert current.nodeState.proposalAcceptedForCurrentRound == next.nodeState.proposalAcceptedForCurrentRound;
                // assert current.nodeState.blockchain == next.nodeState.blockchain;
                // assert current.nodeState.round == next.nodeState.round;

                // if current.nodeState.proposalAcceptedForCurrentRound.None?
                // {
                //     assert indInvInstrNodeStateAllProposalsAcceptedAreValid(next); 
                // }
                // else
                // {
                //     assert isValidProposal(current.nodeState.proposalAcceptedForCurrentRound.value, current.nodeState ) ==>
                //             isValidProposal(current.nodeState.proposalAcceptedForCurrentRound.value, next.nodeState );
                //     assert indInvInstrNodeStateAllProposalsAcceptedAreValid(next); 
                // }
                // // assert next.proposalsAccepted == current.proposalsAccepted;
                // // assert indInvInstrNodeStateAllProposalsAcceptedAreValid(next);
            }
        }        
    } 

    predicate invInstrNodeStateAllProposalsAcceptedAreValid(
        s: InstrNodeState
    )  
    requires validInstrStateEx(s)
    requires indInvInstrNodeStateTypes(s)
    {
        forall m1 |     && m1 in s.proposalsAccepted
                        && m1.proposalPayload.unsignedPayload.height > 0
                    :: 
                        && m1.proposalPayload.unsignedPayload.height <= |s.nodeState.blockchain|
                        && isValidProposalJustification(m1, s.nodeState.blockchain[..m1.proposalPayload.unsignedPayload.height])
    }

    // 3s 3.2.0
    lemma lemmaInvInstrNodeStateAllProposalsAcceptedAreValid
    (
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>  
    )
    requires validInstrStateEx(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires indInvInstrNodeStateAllProposalsAcceptedAreValid(current)
    requires invInstrNodeStateAllProposalsAcceptedAreValid(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)
    ensures indInvInstrNodeStateTypes(next)
    ensures validInstrStateEx(next) ==> invInstrNodeStateAllProposalsAcceptedAreValid(next)
    {
        var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;

        var currentWithNewMessagesReceived :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );        
        if(validInstrStateEx(next))
        {
            if(
                // || UponProposal(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                || UponPrepare(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                || UponRoundChange(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                // || UponNewBlock(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                || UponRoundTimeout(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                || UponBlockTimeout(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                )
            {
                assert invInstrNodeStateAllProposalsAcceptedAreValid(next);
            }
            else if(
                || UponProposal(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
            )
            {
                forall m | m in next.proposalsAccepted - current.proposalsAccepted
                ensures m.proposalPayload.unsignedPayload.height == |next.nodeState.blockchain|; 
                ensures isValidProposalJustification(m, next.nodeState.blockchain[..m.proposalPayload.unsignedPayload.height]);  
                {
                    // assert current.nodeState.blockchain == next.nodeState.blockchain;
                    assert m.proposalPayload.unsignedPayload.height == |next.nodeState.blockchain|; 
                    assert isValidProposal(m, current.nodeState);
                    assert current.nodeState.blockchain[..m.proposalPayload.unsignedPayload.height] == current.nodeState.blockchain;
                    assert isValidProposalJustification(m, current.nodeState.blockchain[..m.proposalPayload.unsignedPayload.height]);  
                    assert isValidProposalJustification(m, next.nodeState.blockchain[..m.proposalPayload.unsignedPayload.height]);  
                }
                
                assert invInstrNodeStateAllProposalsAcceptedAreValid(next);
            }
            else if(
                || UponCommit(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
                || UponNewBlock(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
            )
            {
                assert current.proposalsAccepted == next.proposalsAccepted;
                assert current.nodeState.blockchain <= next.nodeState.blockchain;
                forall m1 | m1 in next.proposalsAccepted
                ensures m1.proposalPayload.unsignedPayload.height <= |next.nodeState.blockchain|; 
                ensures m1.proposalPayload.unsignedPayload.height > 0 ==> isValidProposalJustification(m1, next.nodeState.blockchain[..m1.proposalPayload.unsignedPayload.height]);
                {
                    assert m1 in current.proposalsAccepted;
                    assert m1.proposalPayload.unsignedPayload.height <= |next.nodeState.blockchain|; 
                    if m1.proposalPayload.unsignedPayload.height > 0
                    {
                        assert isValidProposalJustification(m1, current.nodeState.blockchain[..m1.proposalPayload.unsignedPayload.height]);
                        assert current.nodeState.blockchain <= next.nodeState.blockchain;
                        assert current.nodeState.blockchain[..m1.proposalPayload.unsignedPayload.height] == next.nodeState.blockchain[..m1.proposalPayload.unsignedPayload.height];
                        assert isValidProposalJustification(m1, next.nodeState.blockchain[..m1.proposalPayload.unsignedPayload.height]);
                    }

                }
                assert invInstrNodeStateAllProposalsAcceptedAreValid(next);
            }
            else if(currentWithNewMessagesReceived == next.nodeState)
            {
                // assert current.nodeState.proposalAcceptedForCurrentRound == next.nodeState.proposalAcceptedForCurrentRound;
                assert next.proposalsAccepted == current.proposalsAccepted;
                assert invInstrNodeStateAllProposalsAcceptedAreValid(next);
            }
        }
    }

    predicate indInvProposalAcceptedHaveBeenReceived(s:InstrNodeState)
    {
        && (s.nodeState.proposalAcceptedForCurrentRound.Optional? ==> s.nodeState.proposalAcceptedForCurrentRound.value in s.nodeState.messagesReceived)
    }    

    predicate invProposalAcceptedHaveBeenReceived(s:InstrNodeState)
    {
        && s.proposalsAccepted <= s.nodeState.messagesReceived
    }

    lemma lemmaInvProposalAcceptedHaveBeenReceived(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    // requires indInvInstrNodeStateProposalsAccepted(current)
    // requires invInstrNodeStateProposalsAccepted(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    requires indInvProposalAcceptedHaveBeenReceived(current)
    requires invProposalAcceptedHaveBeenReceived(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)   
    ensures invProposalAcceptedHaveBeenReceived(next)
    ensures indInvProposalAcceptedHaveBeenReceived(next)
    {
        // var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;

        // var currentWithNewMessagesReceived :=
        //     current.nodeState.(
        //         messagesReceived := newMessagesReceived,
        //         localTime := next.nodeState.localTime
        //     );        
        // if(validInstrStateEx(next))
        // {
        //     if(
        //         // || UponProposal(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
        //         || UponPrepare(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
        //         || UponRoundChange(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
        //         // || UponNewBlock(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
        //         || UponRoundTimeout(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
        //         || UponBlockTimeout(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
        //         )
        //     {
        //         // assert invInstrNodeStateAllProposalsAcceptedAreValid(next);
        //     }
        //     else if(
        //         || UponProposal(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
        //     )
        //     {
        //         // forall m | m in next.proposalsAccepted - current.proposalsAccepted
        //         // ensures m.proposalPayload.unsignedPayload.height == |next.nodeState.blockchain|; 
        //         // ensures isValidProposalJustification(m, next.nodeState.blockchain[..m.proposalPayload.unsignedPayload.height]);  
        //         // {
        //         //     assert current.nodeState.blockchain == next.nodeState.blockchain;
        //         //     assert m.proposalPayload.unsignedPayload.height == |next.nodeState.blockchain|; 
        //         //     assert isValidProposal(m, current.nodeState);
        //         //     assert current.nodeState.blockchain[..m.proposalPayload.unsignedPayload.height] == current.nodeState.blockchain;
        //         //     assert isValidProposalJustification(m, current.nodeState.blockchain[..m.proposalPayload.unsignedPayload.height]);  
        //         //     assert isValidProposalJustification(m, next.nodeState.blockchain[..m.proposalPayload.unsignedPayload.height]);  
        //         // }
                
        //         // assert invInstrNodeStateAllProposalsAcceptedAreValid(next);
        //     }
        //     else if(
        //         || UponCommit(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
        //         || UponNewBlock(currentWithNewMessagesReceived, next.nodeState, outQbftMessages)
        //     )
        //     {
        //         // assert current.proposalsAccepted == next.proposalsAccepted;
        //         // assert current.nodeState.blockchain <= next.nodeState.blockchain;
        //         // forall m1 | m1 in next.proposalsAccepted
        //         // ensures m1.proposalPayload.unsignedPayload.height <= |next.nodeState.blockchain|; 
        //         // ensures isValidProposalJustification(m1, next.nodeState.blockchain[..m1.proposalPayload.unsignedPayload.height]);
        //         // {
        //         //     assert m1 in current.proposalsAccepted;
        //         //     assert m1.proposalPayload.unsignedPayload.height <= |next.nodeState.blockchain|; 
        //         //     assert isValidProposalJustification(m1, current.nodeState.blockchain[..m1.proposalPayload.unsignedPayload.height]);
        //         //     assert current.nodeState.blockchain <= next.nodeState.blockchain;
        //         //     assert current.nodeState.blockchain[..m1.proposalPayload.unsignedPayload.height] == next.nodeState.blockchain[..m1.proposalPayload.unsignedPayload.height];
        //         //     assert isValidProposalJustification(m1, next.nodeState.blockchain[..m1.proposalPayload.unsignedPayload.height]);
        //         // }
        //         // assert invInstrNodeStateAllProposalsAcceptedAreValid(next);
        //     }
        //     else if(currentWithNewMessagesReceived == next.nodeState)
        //     {
        //         assert invProposalAcceptedHaveBeenReceived(next);
        //         // assert current.nodeState.proposalAcceptedForCurrentRound == next.nodeState.proposalAcceptedForCurrentRound;
        //         // assert next.proposalsAccepted == current.proposalsAccepted;
        //         // assert invInstrNodeStateAllProposalsAcceptedAreValid(next);
        //     }
        // }
    }

    predicate indInvInstrNodeStateNoConflictingPreapresSent(s:InstrNodeState)
    requires indInvInstrNodeStateTypes(s)
    {
        var messagesSent := fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent);
        forall m1 | && m1 in messagesSent+ s.messagesSentToItself
                    ::
                        m1.Prepare?
                        ==>
                        var uPayload1 := m1.preparePayload.unsignedPayload;
                        (exists m2 | m2 in s.proposalsAccepted ::
                            var uPayload2 := m2.proposalPayload.unsignedPayload;
                            && uPayload1.digest == uPayload2.digest
                            && uPayload1.round == uPayload2.round
                            && uPayload1.height == uPayload2.height
                        )
    }


    predicate invInstrNodeStateNoConflictingPreapresSent(s:InstrNodeState)
    {
        var messagesSent := fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent);
        forall m1, m2 |   && m1 in messagesSent+ s.messagesSentToItself
                          && m2 in messagesSent + s.messagesSentToItself
                        ::
                        (
                        && m1.Prepare?
                        && m2.Prepare?
                        &&  var uPayload1 := m1.preparePayload.unsignedPayload;
                            var uPayload2 := m2.preparePayload.unsignedPayload;
                        &&  uPayload1.height == uPayload2.height
                        &&  uPayload1.round == uPayload2.round)
                        // && recoverSignedPrepareAuthor(m1.preparePayload) == recoverSignedPrepareAuthor(m2.preparePayload)

                        ==>
                            var uPayload1 := m1.preparePayload.unsignedPayload;
                            var uPayload2 := m2.preparePayload.unsignedPayload;
                            uPayload1.digest == uPayload2.digest  
    }

    lemma lemmaInvInstrNodeStateNoConflictingPreapresSent(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateNoConflictingPreapresSent(current)
    requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)    
    ensures indInvInstrNodeStateTypes(next)
    ensures indInvInstrNodeStateProposalsAccepted(next)
    ensures invInstrNodeStateProposalsAccepted(next)   
    ensures indInvInstrNodeStateNoConflictingPreapresSent(next)    
    ensures  invInstrNodeStateNoConflictingPreapresSent(next)
    {

        lemmaInvInstrNodeStateProposalsAccepted(current,inQbftMessages,next,outQbftMessages);
        assert invInstrNodeStateProposalsAccepted(next);
        assert indInvInstrNodeStateProposalsAccepted(next);

        var cns := current.nodeState;
        var nns := next.nodeState;     

        var csMessages := fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent) + current.messagesSentToItself;
        var nsMessages := fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent) + next.messagesSentToItself;

        var cSPrepares := set m | m in csMessages && m.Prepare?;
        var nSPrepares := set m | m in nsMessages && m.Prepare?;


        assert  && indInvInstrNodeStateNoConflictingPreapresSent(next)
                && invInstrNodeStateNoConflictingPreapresSent(next)
        by
        {        
            if nSPrepares == cSPrepares
            {
                assert current.proposalsAccepted <= next.proposalsAccepted;
                forall m1 | && m1 in nSPrepares
                ensures var uPayload1 := m1.preparePayload.unsignedPayload;
                        (exists m2 | m2 in next.proposalsAccepted ::
                            var uPayload2 := m2.proposalPayload.unsignedPayload;
                            && uPayload1.digest == uPayload2.digest
                            && uPayload1.round == uPayload2.round
                            && uPayload1.height == uPayload2.height
                        )
                {
                    assert m1 in cSPrepares;
                    assert m1 in csMessages;
                    var uPayload1 := m1.preparePayload.unsignedPayload;
                    var m2 :| && m2 in current.proposalsAccepted 
                            && var uPayload2 := m2.proposalPayload.unsignedPayload;
                            && uPayload1.digest == uPayload2.digest
                            && uPayload1.round == uPayload2.round
                            && uPayload1.height == uPayload2.height;
                }
                // assert indInvInstrNodeStateNoConflictingPreapresSent(next);
  

                // assert invInstrNodeStateNoConflictingPreapresSent(next);         
            }
            else
            {
                var currentWithNewMessagesReceived :=
                    current.nodeState.(
                        messagesReceived := current.nodeState.messagesReceived + inQbftMessages,
                        localTime := next.nodeState.localTime
                    );     

                assert UponProposal(currentWithNewMessagesReceived,next.nodeState,outQbftMessages);   
                lemmaSignedPrepare();    
                assert cSPrepares < nSPrepares;
                assert forall m | m in nSPrepares :: m.Prepare?;

                assert nns.proposalAcceptedForCurrentRound.value in next.proposalsAccepted;
                // assert nns.proposalAcceptedForCurrentRound.Optional?;
                assert forall m1 | m1 in (nSPrepares - cSPrepares) ::
                        var uPayload1 := m1.preparePayload.unsignedPayload;
                        var uPayload2 := nns.proposalAcceptedForCurrentRound.value.proposalPayload.unsignedPayload;
                        && uPayload1.digest == uPayload2.digest
                        && uPayload1.round == uPayload2.round
                        && uPayload1.height == uPayload2.height;


                assert forall m1 | m1 in (nSPrepares - cSPrepares) ::
                            var uPayload1 := m1.preparePayload.unsignedPayload;
                            (exists m2 | m2 in next.proposalsAccepted ::
                                var uPayload2 := m2.proposalPayload.unsignedPayload;
                                && uPayload1.digest == uPayload2.digest
                                && uPayload1.round == uPayload2.round
                                && uPayload1.height == uPayload2.height
                            );         

                assert forall m1 | m1 in nSPrepares ::
                            var uPayload1 := m1.preparePayload.unsignedPayload;
                            (exists m2 | m2 in next.proposalsAccepted ::
                                var uPayload2 := m2.proposalPayload.unsignedPayload;
                                && uPayload1.digest == uPayload2.digest
                                && uPayload1.round == uPayload2.round
                                && uPayload1.height == uPayload2.height
                           );                                      
                // assert |nSPrepares - cSPrepares| == 1;
                // assert indInvInstrNodeStateNoConflictingPreapresSent(next);

                lemmaDigest();

                // assert invInstrNodeStateNoConflictingPreapresSent(next);
            }
        }
        // assert indInvInstrNodeStateNoConflictingPreapresSent(next);
        // assert invInstrNodeStateNoConflictingPreapresSent(next);
    }

    predicate invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(s:InstrNodeState)
    {
        var messagesSent := fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent) + s.messagesSentToItself;
        forall m |
                    && m in messagesSent
                    && m.Commit?
                ::
                var uPayload := m.commitPayload.unsignedPayload;
                && |s.nodeState.blockchain| >= uPayload.height  
                && (s.nodeState.id in validators(s.nodeState.blockchain[..uPayload.height]))              
                &&  exists QofP:: 
                        && QofP <= validPreparesForHeightRoundAndDigest(
                                    s.nodeState.messagesReceived,
                                    uPayload.height,
                                    uPayload.round,
                                    uPayload.digest,
                                    validators(s.nodeState.blockchain[..uPayload.height]))
                        && (|QofP| >= quorum(|validators(s.nodeState.blockchain[..uPayload.height])|))

    }


    lemma lemmaInvInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)    
    ensures indInvInstrNodeStateTypes(next)
    ensures indInvInstrNodeStateProposalsAccepted(next)
    ensures invInstrNodeStateProposalsAccepted(next)   
    ensures invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(next)
    // ensures indInvInstrNodeStateNoConflictingPreapresSent(next)    
    // ensures  invInstrNodeStateNoConflictingPreapresSent(next)
    {

        lemmaInvInstrNodeStateProposalsAccepted(current,inQbftMessages,next,outQbftMessages);
        lemmaSignedCommit();
        assert forall bc:Blockchain :: bc == bc[..|bc|];

        forall m |
                    && m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent) + current.messagesSentToItself
                    && m.Commit?
        ensures
                exists QofP:: 
                    var uPayload := m.commitPayload.unsignedPayload;
                    && (next.nodeState.id in validators(next.nodeState.blockchain[..uPayload.height]))
                    && |next.nodeState.blockchain| >= uPayload.height
                    && QofP <= validPreparesForHeightRoundAndDigest(
                                next.nodeState.messagesReceived,
                                uPayload.height,
                                uPayload.round,
                                uPayload.digest,
                                validators(next.nodeState.blockchain[..uPayload.height]))
                    && |QofP| >= quorum(|validators(next.nodeState.blockchain[..uPayload.height])|) 
        {
            var uPayload := m.commitPayload.unsignedPayload;
            var QofP :| 
                    && |current.nodeState.blockchain| >= uPayload.height
                    && QofP <= validPreparesForHeightRoundAndDigest(
                                current.nodeState.messagesReceived,
                                uPayload.height,
                                uPayload.round,
                                uPayload.digest,
                                validators(current.nodeState.blockchain[..uPayload.height]))
                    && |QofP| >= quorum(|validators(current.nodeState.blockchain[..uPayload.height])|);

            assert current.nodeState.messagesReceived <= next.nodeState.messagesReceived;
            assert current.nodeState.blockchain[..uPayload.height] == next.nodeState.blockchain[..uPayload.height];

            assert QofP <=  validPreparesForHeightRoundAndDigest(
                                next.nodeState.messagesReceived,
                                uPayload.height,
                                uPayload.round,
                                uPayload.digest,
                                validators(next.nodeState.blockchain[..uPayload.height]));
        }


        // var cms := fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent);
        // var nms := fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent);

        // assert forall m:QbftMessage | m in (nms - cms) && m.Commit? :: 
        //         exists QofP:: 
        //             var uPayload := m.commitPayload.unsignedPayload;
        //             && |next.nodeState.blockchain| >= uPayload.height
        //             && QofP <= validPreparesForHeightRoundAndDigest(
        //                         next.nodeState.messagesReceived,
        //                         uPayload.height,
        //                         uPayload.round,
        //                         uPayload.digest,
        //                         validators(next.nodeState.blockchain[..uPayload.height]))
        //             && |QofP| >= quorum(|validators(next.nodeState.blockchain[..uPayload.height])|);
        // assert |next.nodeState.blockchain| >= |current.nodeState.blockchain|;
        // assert 
    }

    predicate indInvInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(
        s:InstrNodeState
    )
    {
        var messagesSent := fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent) + s.messagesSentToItself;
        forall cm | 
                    && cm in messagesSent
                    && cm.Commit?
                ::
                    && cm in s.nodeState.messagesReceived
                    && recoverSignedCommitAuthor(cm.commitPayload) == s.nodeState.id
    }

    lemma lemmaIndInvInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)    
    ensures indInvInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(next)
    {
        lemmaSignedCommit();
    }

    predicate invInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(s:InstrNodeState)
    {
        var messagesSent := fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent) + s.messagesSentToItself;
        forall m |
                    && m in messagesSent
                    && m.Commit?
                ::
                var uPayload := m.commitPayload.unsignedPayload;
                (
                    && uPayload.height == |s.nodeState.blockchain|
                    && uPayload.round == s.nodeState.round
                )
                ==>
                (
                    && s.nodeState.lastPreparedBlock.Optional?
                    && s.nodeState.lastPreparedRound.Optional?
                    && digest(s.nodeState.lastPreparedBlock.value) == uPayload.digest
                    && s.nodeState.lastPreparedRound.value == uPayload.round
                )
    }

    lemma lemmaInvInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyMessageSent(current)
    requires indInvInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(current)
    requires invInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)    
    // ensures indInvInstrNodeStateTypes(next)
    // ensures indInvInstrNodeStateProposalsAccepted(next)
    // ensures invInstrNodeStateProposalsAccepted(next)   
    ensures indInvInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(next)
    ensures invInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(next)
    // ensures indInvInstrNodeStateNoConflictingPreapresSent(next)    
    // ensures  invInstrNodeStateNoConflictingPreapresSent(next)  
    {
        lemmaSignedCommit();       
    }  

    predicate indInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(
        s: InstrNodeState
    )
    {
        forall m |  && m in getAllMessagesSentByInsrNodeState(s)
                    && m.Commit?
                ::
                    || (
                        |s.nodeState.blockchain| > m.commitPayload.unsignedPayload.height
                    ) 
                    || (
                        && |s.nodeState.blockchain| == m.commitPayload.unsignedPayload.height
                        && s.nodeState.lastPreparedRound.Optional?
                        && s.nodeState.lastPreparedRound.value >= m.commitPayload.unsignedPayload.round
                    )
    }

    lemma lemmaIndInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyMessageSent(current)
    requires indInvInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(current)
    requires invInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(current)
    requires indInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)   
    ensures indInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(next) 
    {
        lemmaSignedCommit();       
        assert indInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(next);
    }

    predicate indInvA_2(
        s: InstrNodeState
    )
    {
        forall cm, rm | && cm in getAllMessagesSentByInsrNodeState(s)
                        && cm.Commit?
                        && rm in getAllMessagesSentByInsrNodeState(s)
                        && rm.RoundChange?
                        && rm.roundChangePayload.unsignedPayload.height == cm.commitPayload.unsignedPayload.height
                        && rm.roundChangePayload.unsignedPayload.round == cm.commitPayload.unsignedPayload.round + 1
                ::
                    && rm.roundChangePayload.unsignedPayload.preparedRound.Optional?
                    // && rm.roundChangePayload.unsignedPayload.preparedRound.value >= cm.commitPayload.unsignedPayload.round
    }

    lemma lemmaIndInvA2(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyMessageSent(current)
    requires indInvInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(current)
    requires invInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(current)
    requires indInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(current)
    requires indInvA_2(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)   
    ensures indInvA_2(next)
    // ensures indInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(next) 
    {
        lemmaSignedCommit();  
        lemmaSignedRoundChange();             
        assert indInvA_2(next);
    }    


    predicate invRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(
        s: InstrNodeState
    )
    {
        forall cm, rm | && cm in getAllMessagesSentByInsrNodeState(s)
                        && cm.Commit?
                        && rm in getAllMessagesSentByInsrNodeState(s)
                        && rm.RoundChange?
                        && rm.roundChangePayload.unsignedPayload.height == cm.commitPayload.unsignedPayload.height
                        && rm.roundChangePayload.unsignedPayload.round > cm.commitPayload.unsignedPayload.round
                ::
                    && rm.roundChangePayload.unsignedPayload.preparedRound.Optional?
                    && rm.roundChangePayload.unsignedPayload.preparedRound.value >= cm.commitPayload.unsignedPayload.round
    }    

    lemma lemmaInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrStateEx(current)
    requires indInvInstrNodeStateTypes(current)
    // requires indInvInstrNodeStateProposalsAccepted(current)
    // requires invInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyMessageSent(current)
    // requires indInvInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateIfCommitAndNextRoundChangeThenTheyMatch(current)
    // requires invInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    requires indInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(current)
    requires invRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)   
    ensures indInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(next) 
    ensures invRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(next)
    {
        lemmaSignedCommit();  
        lemmaSignedRoundChange();                       
    }    

    predicate invInstrNodeStateCommitSentOnlyIfAcceptedProposal(
        s: InstrNodeState
    )
    requires indInvInstrNodeStateTypes(s)
    {
        forall m |  && m in getAllMessagesSentByInsrNodeState(s)
                    && m.Commit?
                ::
                exists pm ::    && pm in s.proposalsAccepted
                                &&  var cuPayload := m.commitPayload.unsignedPayload;
                                    var puPayload := pm.proposalPayload.unsignedPayload;
                                &&  puPayload.height == cuPayload.height
                                &&  puPayload.round == cuPayload.round
                                &&  digest(pm.proposedBlock) == cuPayload.digest
                                &&  signHash(hashBlockForCommitSeal(pm.proposedBlock), s.nodeState.id) == cuPayload.commitSeal
    }

    lemma lemmaInvInstrNodeStateCommitSentOnlyIfAcceptedProposal(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    // requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)    
    ensures indInvInstrNodeStateTypes(next)
    ensures indInvInstrNodeStateProposalsAccepted(next)
    ensures invInstrNodeStateProposalsAccepted(next)   
    // ensures invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(next)
    ensures invInstrNodeStateCommitSentOnlyIfAcceptedProposal(next)
    // ensures indInvInstrNodeStateNoConflictingPreapresSent(next)    
    // ensures  invInstrNodeStateNoConflictingPreapresSent(next)
    {

        lemmaInvInstrNodeStateProposalsAccepted(current,inQbftMessages,next,outQbftMessages);
        lemmaSignedCommit();
    }   


    predicate invInstrNodeStatePrepareAndCommitMatch(
        s: InstrNodeState
    )
    { 
        forall pm, cm |
                && pm in getAllMessagesSentByInsrNodeState(s)
                && pm.Prepare?
                && cm in getAllMessagesSentByInsrNodeState(s)
                && cm.Commit?
            ::
            var puPayload := pm.preparePayload.unsignedPayload;
            var cuPayload := cm.commitPayload.unsignedPayload;
            (
                && puPayload.height == cuPayload.height
                && puPayload.round == cuPayload.round
            )
            ==>
            (
                && puPayload.digest == cuPayload.digest
            )
    }

    lemma lemmaInvInstrNodeStatePrepareAndCommitMatch(
        current:InstrNodeState
    )
    // requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)

    requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)
    ensures  invInstrNodeStatePrepareAndCommitMatch(current) 
    {
        lemmaDigest();
    }
    

    predicate invInstrNodeStatePrepareSentOnlyIfAcceptedProposal(
        s: InstrNodeState
    )
    requires indInvInstrNodeStateTypes(s)
    {
        forall m |  && m in getAllMessagesSentByInsrNodeState(s)
                    && m.Prepare?
                ::
                exists pm ::    && pm in s.proposalsAccepted
                                &&  var cuPayload := m.preparePayload.unsignedPayload;
                                    var puPayload := pm.proposalPayload.unsignedPayload;
                                &&  puPayload.height == cuPayload.height
                                &&  puPayload.round == cuPayload.round
                                &&  digest(pm.proposedBlock) == cuPayload.digest
    }    

    lemma lemmaInvInstrNodeStatePrepareSentOnlyIfAcceptedProposal(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    // requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    requires invInstrNodeStatePrepareSentOnlyIfAcceptedProposal(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)    
    ensures indInvInstrNodeStateTypes(next)
    ensures indInvInstrNodeStateProposalsAccepted(next)
    ensures invInstrNodeStateProposalsAccepted(next)   
    // ensures invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(next)
    ensures invInstrNodeStatePrepareSentOnlyIfAcceptedProposal(next)
    // ensures indInvInstrNodeStateNoConflictingPreapresSent(next)    
    // ensures  invInstrNodeStateNoConflictingPreapresSent(next)
    {

        lemmaInvInstrNodeStateProposalsAccepted(current,inQbftMessages,next,outQbftMessages);
        lemmaSignedPrepare();
    }       


    predicate invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyRoundChangeSent(
         s: InstrNodeState
    )
    requires indInvInstrNodeStateTypes(s)
    {
        forall m |  && m in getAllMessagesSentByInsrNodeState(s)
                    && m.RoundChange?
                  ::
                    var uPayload := m.roundChangePayload.unsignedPayload;
                    || (
                        |s.nodeState.blockchain| > uPayload.height
                    )
                    || (
                        && |s.nodeState.blockchain| == uPayload.height
                        && s.nodeState.round >= uPayload.round
                    )
        
    }


    predicate invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyCommitSent(
         s: InstrNodeState
    )
    requires indInvInstrNodeStateTypes(s)
    {
        forall m |  && m in getAllMessagesSentByInsrNodeState(s)
                    && m.Commit?
                  ::
                    var uPayload := m.commitPayload.unsignedPayload;
                    || (
                        |s.nodeState.blockchain| > uPayload.height
                    )
                    || (
                        && |s.nodeState.blockchain| == uPayload.height
                        && s.nodeState.round >= uPayload.round
                    )
        
    }    

    predicate invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyMessageSent(
        s: InstrNodeState
    )
    requires indInvInstrNodeStateTypes(s)
    {
        && invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyRoundChangeSent(s)
        && invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyCommitSent(s)
    }

    lemma lemmaInvInstrNodeStateInARoundAtLeastEqualToThoseOfAnyRoundChangeSent(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyMessageSent(current)
    // requires indInvInstrNodeStateProposalsAccepted(current)
    // requires invInstrNodeStateProposalsAccepted(current)
    // // requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)    
    ensures indInvInstrNodeStateTypes(next)
    ensures invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyMessageSent(next)
    // ensures indInvInstrNodeStateProposalsAccepted(next)
    // ensures invInstrNodeStateProposalsAccepted(next)   
    // // ensures invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(next)
    // ensures invInstrNodeStateCommitSentOnlyIfAcceptedProposal(next)
    // ensures indInvInstrNodeStateNoConflictingPreapresSent(next)    
    // ensures  invInstrNodeStateNoConflictingPreapresSent(next)  
    {
        lemmaSignedRoundChange();   
        lemmaSignedCommit();   
    } 

    predicate invInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares(s:InstrNodeState)
    requires indInvInstrNodeStateTypes(s)
    {
        var messagesSent := fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent) + s.messagesSentToItself;
        forall m |
                    && m in messagesSent
                    && m.RoundChange?
                    && var uPayload := m.roundChangePayload.unsignedPayload;
                    && uPayload.preparedValue.Optional?
                    // && uPayload.preparedRound.Optional?
                ::
                var uPayload := m.roundChangePayload.unsignedPayload;
                && uPayload.preparedRound.Optional?
                && |s.nodeState.blockchain| >= uPayload.height                
                && (s.nodeState.id in validators(s.nodeState.blockchain[..uPayload.height]))
                &&  exists QofP:: 
                        && QofP <= validPreparesForHeightRoundAndDigest(
                                    s.nodeState.messagesReceived,
                                    uPayload.height,
                                    uPayload.preparedRound.value,
                                    uPayload.preparedValue.value,
                                    validators(s.nodeState.blockchain[..uPayload.height]))
                        && |QofP| >= quorum(|validators(s.nodeState.blockchain[..uPayload.height])|) 

    } 

    lemma lemmaGetQofPFromRoundChange(
        s: InstrNodeState,
        m: QbftMessage
    )    
    returns (QofP:set<QbftMessage>)
    requires indInvInstrNodeStateTypes(s)   
    requires invInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares(s)
    requires    && m in (fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent) + s.messagesSentToItself)
                && m.RoundChange?
                && var uPayload := m.roundChangePayload.unsignedPayload;
                && uPayload.preparedValue.Optional?
    ensures     var uPayload := m.roundChangePayload.unsignedPayload;
                && QofP <= validPreparesForHeightRoundAndDigest(
                            s.nodeState.messagesReceived,
                            uPayload.height,
                            uPayload.preparedRound.value,
                            uPayload.preparedValue.value,
                            validators(s.nodeState.blockchain[..uPayload.height]))
                && |QofP| >= quorum(|validators(s.nodeState.blockchain[..uPayload.height])|);    
    {
        var uPayload := m.roundChangePayload.unsignedPayload;
        QofP :| 
                        && QofP <= validPreparesForHeightRoundAndDigest(
                                    s.nodeState.messagesReceived,
                                    uPayload.height,
                                    uPayload.preparedRound.value,
                                    uPayload.preparedValue.value,
                                    validators(s.nodeState.blockchain[..uPayload.height]))
                        && |QofP| >= quorum(|validators(s.nodeState.blockchain[..uPayload.height])|);
    }

    lemma lemmaInvInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires invInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    // // requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)    
    ensures indInvInstrNodeStateTypes(next)
    ensures invInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares(next)
    // ensures indInvInstrNodeStateProposalsAccepted(next)
    // ensures invInstrNodeStateProposalsAccepted(next)   
    // // ensures invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(next)
    // ensures invInstrNodeStateCommitSentOnlyIfAcceptedProposal(next)
    // ensures indInvInstrNodeStateNoConflictingPreapresSent(next)    
    // ensures  invInstrNodeStateNoConflictingPreapresSent(next)  
    {
        lemmaSignedRoundChange();      
        lemmaSignedPrepare();
        lemmaDigest();
        lemmaInvInstrNodeStateProposalsAccepted(current,inQbftMessages,next,outQbftMessages);
        // lemmaSignedCommit();
        assert forall bc:Blockchain :: bc == bc[..|bc|];

        forall m |
                    && m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent) + current.messagesSentToItself
                    && m.RoundChange?
                    && var uPayload := m.roundChangePayload.unsignedPayload;
                    && uPayload.preparedValue.Optional?
        ensures
                exists QofP:: 
                    var uPayload := m.roundChangePayload.unsignedPayload;
                    && (next.nodeState.id in validators(next.nodeState.blockchain[..uPayload.height]))
                    && |next.nodeState.blockchain| >= uPayload.height
                    && QofP <= validPreparesForHeightRoundAndDigest(
                                next.nodeState.messagesReceived,
                                uPayload.height,
                                uPayload.preparedRound.value,
                                uPayload.preparedValue.value,
                                validators(next.nodeState.blockchain[..uPayload.height]))
                    && |QofP| >= quorum(|validators(next.nodeState.blockchain[..uPayload.height])|) 
        {
            var uPayload := m.roundChangePayload.unsignedPayload;

            // var uPayload := m.commitPayload.unsignedPayload;
            var QofP :| 
                    && |current.nodeState.blockchain| >= uPayload.height
                    && QofP <= validPreparesForHeightRoundAndDigest(
                                current.nodeState.messagesReceived,
                                uPayload.height,
                                uPayload.preparedRound.value,
                                uPayload.preparedValue.value,
                                validators(current.nodeState.blockchain[..uPayload.height]))
                    && |QofP| >= quorum(|validators(current.nodeState.blockchain[..uPayload.height])|);



                  

            assert current.nodeState.messagesReceived <= next.nodeState.messagesReceived;
            assert current.nodeState.blockchain[..uPayload.height] == next.nodeState.blockchain[..uPayload.height];

            assert QofP <=  validPreparesForHeightRoundAndDigest(
                                next.nodeState.messagesReceived,
                                uPayload.height,
                                uPayload.preparedRound.value,
                                uPayload.preparedValue.value,
                                validators(next.nodeState.blockchain[..uPayload.height]));

            assert exists QofP:: 
                    var uPayload := m.roundChangePayload.unsignedPayload;
                    && (next.nodeState.id in validators(next.nodeState.blockchain[..uPayload.height]))
                    && |next.nodeState.blockchain| >= uPayload.height
                    && QofP <= validPreparesForHeightRoundAndDigest(
                                next.nodeState.messagesReceived,
                                uPayload.height,
                                uPayload.preparedRound.value,
                                uPayload.preparedValue.value,
                                validators(next.nodeState.blockchain[..uPayload.height]))
                    && |QofP| >= quorum(|validators(next.nodeState.blockchain[..uPayload.height])|) ;              
        }        
    }     

    predicate invInstrNodeStateIfCommitAndNextRoundChangeThenTheyMatch(s:InstrNodeState)
    requires indInvInstrNodeStateTypes(s)
    {
        var messagesSent := fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent) + s.messagesSentToItself;
        forall cm, rm |
                    && cm in messagesSent
                    && cm.Commit?
                    && rm in messagesSent
                    && rm.RoundChange?
                    // && var urPayload := rm.roundChangePayload.unsignedPayload;
                    // && uPayload.preparedValue.Optional?
                    // && uPayload.preparedRound.Optional?
                ::
                var urPayload := rm.roundChangePayload.unsignedPayload;
                var ucPayload := cm.commitPayload.unsignedPayload;
                (
                    && urPayload.height == ucPayload.height
                    && urPayload.round == ucPayload.round + 1
                    // && |s.nodeState.blockchain| >= urPayload.height 
                    // && (s.nodeState.id in validators(s.nodeState.blockchain[..urPayload.height]))
                )
                 ==>
                (
                    && urPayload.preparedRound.Optional?
                    && urPayload.preparedValue.Optional?
                    && urPayload.preparedRound.value == ucPayload.round
                    && urPayload.preparedValue.value == ucPayload.digest
                    // &&  exists QofP:: 
                    //         && QofP <= validPreparesForHeightRoundAndDigest(
                    //                     s.nodeState.messagesReceived,
                    //                     urPayload.height,
                    //                     urPayload.preparedRound.value,
                    //                     urPayload.preparedValue.value,
                    //                     validators(s.nodeState.blockchain[..urPayload.height]))
                    //         && |QofP| >= quorum(|validators(s.nodeState.blockchain[..urPayload.height])|) 
                )

    }        

    lemma lemmaInvInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares2(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires invInstrNodeStateIfCommitAndNextRoundChangeThenTheyMatch(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyMessageSent(current)
    requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    requires invInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)    
    ensures indInvInstrNodeStateTypes(next)
    ensures invInstrNodeStateIfCommitAndNextRoundChangeThenTheyMatch(next)
    // ensures indInvInstrNodeStateProposalsAccepted(next)
    // ensures invInstrNodeStateProposalsAccepted(next)   
    // // ensures invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(next)
    // ensures invInstrNodeStateCommitSentOnlyIfAcceptedProposal(next)
    // ensures indInvInstrNodeStateNoConflictingPreapresSent(next)    
    // ensures  invInstrNodeStateNoConflictingPreapresSent(next)  
    {
        lemmaSignedRoundChange();      
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaDigest();
        lemmaInvInstrNodeStateProposalsAccepted(current,inQbftMessages,next,outQbftMessages);
        // lemmaSignedCommit();
        // assert forall bc:Blockchain :: bc == bc[..|bc|];

        // var messagesSent := fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent) + next.messagesSentToItself;
        // forall cm, rm |
        //     && cm in messagesSent
        //     && cm.Commit?
        //     && rm in messagesSent
        //     && rm.RoundChange?
        //     // && var urPayload := rm.roundChangePayload.unsignedPayload;
        //     // && uPayload.preparedValue.Optional?
        //     // && uPayload.preparedRound.Optional?
        // ensures
        //         var urPayload := rm.roundChangePayload.unsignedPayload;
        //         var ucPayload := cm.commitPayload.unsignedPayload;
        //         (
        //             && urPayload.height == ucPayload.height
        //             && urPayload.round == ucPayload.round + 1
        //             // && |next.nodeState.blockchain| >= urPayload.height 
        //             // && (next.nodeState.id in validators(next.nodeState.blockchain[..urPayload.height]))
        //         )
        //          ==>
        //         (
        //             && urPayload.preparedRound.Optional?
        //             && urPayload.preparedValue.Optional?
        //             && urPayload.preparedRound.value == ucPayload.round
        //             && urPayload.preparedValue.value == ucPayload.digest
        //         )
        // {
        //     var urPayload := rm.roundChangePayload.unsignedPayload;
        //     var ucPayload := cm.commitPayload.unsignedPayload;

        //     if(
        //             && urPayload.height == ucPayload.height
        //             && urPayload.round == ucPayload.round + 1
        //             // && |next.nodeState.blockchain| >= urPayload.height 
        //             // && (next.nodeState.id in validators(next.nodeState.blockchain[..urPayload.height]))
        //         )
        //     {
        //         // var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;

        //         // var currentWithNewMessagesReceived :=
        //         //     current.nodeState.(
        //         //         messagesReceived := newMessagesReceived,
        //         //         localTime := next.nodeState.localTime
        //         //     );

        //         // // if(UponPrepare(currentWithNewMessagesReceived, next.nodeState, outQbftMessages))
        //         // // {
        //         // //     assert   && urPayload.preparedRound.Optional?
        //         // //     && urPayload.preparedValue.Optional?
        //         // //     && urPayload.preparedRound.value == ucPayload.round
        //         // //     && urPayload.preparedValue.value == ucPayload.digest;
        //         // // }

        //         // if(UponRoundTimeout(currentWithNewMessagesReceived, next.nodeState, outQbftMessages))
        //         // {
        //         //     assert   && urPayload.preparedRound.Optional?
        //         //     && urPayload.preparedValue.Optional?
        //         //     && urPayload.preparedRound.value == ucPayload.round
        //         //     && urPayload.preparedValue.value == ucPayload.digest;
        //         // }
        //         // else if(UponRoundChange(currentWithNewMessagesReceived, next.nodeState, outQbftMessages))
        //         // {
        //         //     assert   && urPayload.preparedRound.Optional?
        //         //     && urPayload.preparedValue.Optional?
        //         //     && urPayload.preparedRound.value == ucPayload.round
        //         //     && urPayload.preparedValue.value == ucPayload.digest;
        //         // }
        //         // else if(UponNewBlock(currentWithNewMessagesReceived, next.nodeState, outQbftMessages))
        //         // {
        //         //     assume   && urPayload.preparedRound.Optional?
        //         //     && urPayload.preparedValue.Optional?
        //         //     && urPayload.preparedRound.value == ucPayload.round
        //         //     && urPayload.preparedValue.value == ucPayload.digest;
        //         // }
        //         // else if(UponProposal(currentWithNewMessagesReceived, next.nodeState, outQbftMessages))
        //         // {
        //         //     assume   && urPayload.preparedRound.Optional?
        //         //     && urPayload.preparedValue.Optional?
        //         //     && urPayload.preparedRound.value == ucPayload.round
        //         //     && urPayload.preparedValue.value == ucPayload.digest;
        //         // }                


        //     }
        // }    
    }    

    predicate invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(
        s:InstrNodeState
    )
    {
        forall n | n != s.nodeState.id ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent)), n) <=
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodeState.messagesReceived), n) 
                    
    }

    // 155 s
    lemma lemmaInvInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)  
    ensures invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next)
    {
        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();  
        lemmaGetSetOfSignedPayloads(); 

        var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;

        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );

        var nextForSubsteps := next.nodeState;

        assert currentForSubsteps.id == nextForSubsteps.id;
        assert next.messagesSent == current.messagesSent + multiset(outQbftMessages);

        if(     
                // || (currentForSubsteps == nextForSubsteps && outQbftMessages == {})
                || UponBlockTimeout(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponProposal(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponPrepare(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponCommit(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponNewBlock(currentForSubsteps, nextForSubsteps, outQbftMessages)
        )
        {
            assert forall n | n != next.nodeState.id ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n);

            assert invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);
        }         
        else if(     
                || UponRoundChange(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponRoundTimeout(currentForSubsteps, nextForSubsteps, outQbftMessages)
                )
        {
            assert forall n | n != next.nodeState.id ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))), n) <=
                    // filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) +
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n);

            assert forall n | n != next.nodeState.id ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) +
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))), n);
                    
            assert invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);

        } 
        else if(currentForSubsteps == nextForSubsteps)
        {
            assert outQbftMessages == {};

            assert forall n | n != next.nodeState.id ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n);            
            assert invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);
        }           
   
    }    


    predicate invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(
        s:InstrNodeState,
        bm: QbftMessage,
        b: Block,
        i: nat
    )
    requires 0 <= i < |s.nodeState.blockchain|
    {
        && bm in s.nodeState.messagesReceived
        && bm.NewBlock?
        && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
        && bm.block.header.height == i 
        && ValidNewBlock(s.nodeState.blockchain[..i], bm.block)
    }

    predicate invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(
        s:InstrNodeState,
        i:nat
    )
    requires 0 <= i < |s.nodeState.blockchain|
    {
            (   
                var b := s.nodeState.blockchain[i];
                exists bm :: invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(s, bm, b, i)   
            )        
    }


    predicate invInstrNodeStateBlocksInBlockchainHaveBeenReceived(
        s:InstrNodeState
    ) 
    {
        // forall b | b in s.nodeState.blockchain ::
        forall i | 1 <= i < |s.nodeState.blockchain| :: invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(s, i)

    }

    lemma lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(
        s:InstrNodeState
    )
    requires forall i | 1 <= i < |s.nodeState.blockchain| :: invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(s, i)
    ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceived(s)
    {

    }

    lemma lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(
        s:InstrNodeState,
        i: nat,
        j:nat
    )
    requires 0 <= i < |s.nodeState.blockchain|
    requires invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(s, i);
    requires i == j 
    ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(s, j);
    {

    }

    function getCommitSealsFromSetOfCommitMessages(
        QofC: set<QbftMessage>
    ): set<Signature>
    requires forall m | m in QofC :: m.Commit?
    {
        set m:QbftMessage | m in QofC :: m.commitPayload.unsignedPayload.commitSeal
    }

    predicate areAllMessagesCommits(
        QofC: set<QbftMessage>
    )
    {
        forall m | m in QofC :: m.Commit?
    }

    function getCommitSealFromCommitMessage(
        m: QbftMessage
    ) : Signature
    requires m.Commit?
    {
        m.commitPayload.unsignedPayload.commitSeal
    }

    lemma lllfdafadllCommit(
        height:nat,
        round:nat,
        block:Block,
        QofC:set<QbftMessage>,
        messagesReceived: set<QbftMessage>,
        blockchain: Blockchain
    )  
    requires |blockchain| >= height
    requires QofC == validCommitsForHeightRoundAndDigest(
                                    messagesReceived,
                                    height,
                                    round,
                                    block,
                                    validators(blockchain[..height]))
    ensures |QofC| == |getCommitSealsFromSetOfCommitMessages(QofC)|; 
    {
        lemmaSignedCommit();
        lemmaSignedHash();
        lemmaDigest();

        // forall m1, m2 | 
        //     && m1 in QofC 
        //     && m2 in QofC
        //     && m1 != m2
        // ensures getCommitSealFromCommitMessage(m1) != getCommitSealFromCommitMessage(m2)
        // {
        //     assert getCommitSealFromCommitMessage(m1) != getCommitSealFromCommitMessage(m2);
        // }

        lemma_MapSetCardinalityOver(
                QofC, 
                getCommitSealsFromSetOfCommitMessages(QofC), 
                (m:QbftMessage) requires m.Commit? => getCommitSealFromCommitMessage(m)
        );   

        assert |QofC| == |getCommitSealsFromSetOfCommitMessages(QofC)|;     

    }

    lemma lllfdafadllCommitSimp(
        round:nat,
        block:Block,
        QofC:set<QbftMessage>,
        messagesReceived: set<QbftMessage>,
        blockchain: Blockchain
    )  
    requires QofC <= validCommitsForHeightRoundAndDigest(
                                    messagesReceived,
                                    |blockchain|,
                                    round,
                                    block,
                                    validators(blockchain))
    ensures |QofC| == |getCommitSealsFromSetOfCommitMessages(QofC)|; 
    {
        lemmaSignedCommit();
        lemmaSignedHash();
        lemmaDigest();

        // forall m1, m2 | 
        //     && m1 in QofC 
        //     && m2 in QofC
        //     && m1 != m2
        // ensures getCommitSealFromCommitMessage(m1) != getCommitSealFromCommitMessage(m2)
        // {
        //     assert getCommitSealFromCommitMessage(m1) != getCommitSealFromCommitMessage(m2);
        // }

        lemma_MapSetCardinalityOver(
                QofC, 
                getCommitSealsFromSetOfCommitMessages(QofC), 
                (m:QbftMessage) requires m.Commit? => getCommitSealFromCommitMessage(m)
        );   

        assert |QofC| == |getCommitSealsFromSetOfCommitMessages(QofC)|;     

    }    

    lemma lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedUponCommit(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>,
        i: nat
    )   
    requires validInstrStateEx(current)
    requires invInstrNodeStateBlocksInBlockchainHaveBeenReceived(current)
    requires indInvInstrNodeStateTypes(current);
    requires indInvInstrNodeStateProposalsAccepted(current);
    requires (validInstrStateEx(current) ==> invInstrNodeStateAllProposalsAcceptedAreValid(current));    
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)   
    requires         
        var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;
        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );    
        UponCommit(currentForSubsteps, next.nodeState, outQbftMessages)
    requires |current.nodeState.blockchain| <= i < |next.nodeState.blockchain|
    ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
    {
        var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;
        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );         
        
        assert current.nodeState.blockchain <= next.nodeState.blockchain;
            
        assert i == |next.nodeState.blockchain|-1;

        var b := next.nodeState.blockchain[|next.nodeState.blockchain|-1];
        assert current.nodeState.blockchain +  [b] == next.nodeState.blockchain;

        assert current.nodeState.blockchain != next.nodeState.blockchain;

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

        var QofC:set<QbftMessage>, bm :|
            && QofC <= allValidCommitsForCurrentHeightAndRound
            && |QofC| == quorum(|validators(currentForSubsteps.blockchain)|)
            && next.nodeState.messagesReceived == currentForSubsteps.messagesReceived + {bm}
            && bm.NewBlock?
            && areBlocksTheSameExceptForTheCommitSeals(proposedBlock, bm.block)
            // && areAllMessagesCommits(QofC)
            && bm.block == proposedBlock.(
                                header := proposedBlock.header.(
                                    commitSeals := getCommitSealsFromCommitMessages(QofC)
                                )
                            )
            ;

            assert areBlocksTheSameExceptForTheCommitSeals(bm.block, b);


            var h := |currentForSubsteps.blockchain|;
            
            lllfdafadllCommitSimp(
                currentForSubsteps.round,
                currentForSubsteps.proposalAcceptedForCurrentRound.value.proposedBlock,
                QofC,
                currentForSubsteps.messagesReceived,
                currentForSubsteps.blockchain
            );
            assert 
                |bm.block.header.commitSeals| >= quorum(|validators(currentForSubsteps.blockchain)|);

            assert i == |current.nodeState.blockchain|;
            assert ValidNewBlock(current.nodeState.blockchain, bm.block);
            assert areBlocksTheSameExceptForTheCommitSeals(bm.block, proposedBlock);
            assert bm.block.header.height == i;
            assert next.nodeState.blockchain[..i] == current.nodeState.blockchain;
            assert bm in next.nodeState.messagesReceived;
            assert ValidNewBlock(next.nodeState.blockchain[..i], bm.block);
            assert areBlocksTheSameExceptForTheCommitSeals(bm.block, b);

            assert 
                && bm in next.nodeState.messagesReceived
                && bm.NewBlock?
                && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
                && bm.block.header.height == i 
                && ValidNewBlock(next.nodeState.blockchain[..i], bm.block)
                ;
            // assert |nextForSubsteps.blockchainp[]|

            assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, i);   
        // }


        assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);


        assert proposedBlock.header.height == |currentForSubsteps.blockchain|;
        assert proposedBlock.header.height == |next.nodeState.blockchain|-1;

        assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
        lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, |next.nodeState.blockchain|-1, i);    

        calc {
            invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, |next.nodeState.blockchain|-1);  
            ==>  {
                lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, |next.nodeState.blockchain|-1, i);    
            }
            invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);  
        }                      

        assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);  
                     
    }

    // 2s 3.2.0
    lemma lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceived(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient> 
    )
    requires validInstrStateEx(current)
    requires invInstrNodeStateBlocksInBlockchainHaveBeenReceived(current)
    requires indInvInstrNodeStateTypes(current);
    requires indInvInstrNodeStateProposalsAccepted(current);
    requires (validInstrStateEx(current) ==> invInstrNodeStateAllProposalsAcceptedAreValid(current));    
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)  
    ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next)
    {     

        var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;

        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );  

        var nextForSubsteps := next.nodeState;
    

        if(     
                || UponBlockTimeout(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponProposal(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponPrepare(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponRoundChange(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponRoundTimeout(currentForSubsteps, nextForSubsteps, outQbftMessages)                
        )
        {
            assert current.nodeState.blockchain == next.nodeState.blockchain;
            assert current.nodeState.messagesReceived <= next.nodeState.messagesReceived;
            forall i | 1 <= i < |next.nodeState.blockchain|
            ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
            {
                var b := current.nodeState.blockchain[i];
                assert b == next.nodeState.blockchain[i];

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(current, i);

                var bm :|   && bm in current.nodeState.messagesReceived
                            && bm.NewBlock?
                            && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
                            && bm.block.header.height == i
                            && ValidNewBlock(current.nodeState.blockchain[..i], bm.block);

                assert bm in next.nodeState.messagesReceived;

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, i);   

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);

            }

            calc ==> {
                forall i | 1 <= i < |next.nodeState.blockchain|
                :: invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
                {
                    lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next);
                }
                invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  
            } 
            assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  

        }         
        else if(     
                || UponNewBlock(currentForSubsteps, nextForSubsteps, outQbftMessages)
                )
        {
            assert current.nodeState.blockchain <= next.nodeState.blockchain;
            

            forall i | 1 <= i < |next.nodeState.blockchain|
            ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
            {
                if i < |current.nodeState.blockchain|
                {
                    var b := current.nodeState.blockchain[i];
                    assert b == next.nodeState.blockchain[i];

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(current, i);

                    var bm :|   && bm in current.nodeState.messagesReceived
                                && bm.NewBlock?
                                && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
                                && bm.block.header.height == i
                                && ValidNewBlock(current.nodeState.blockchain[..i], bm.block);

                    assert bm in next.nodeState.messagesReceived;
                    assert 0 <= i < |next.nodeState.blockchain|;
                    assert bm.NewBlock?;
                    assert areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b);
                    assert bm.block.header.height == i;
                    assert current.nodeState.blockchain[..i] == next.nodeState.blockchain[..i];

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, i);   

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
                }
                else 
                {
                    assert i == |next.nodeState.blockchain|-1;
                    var b := next.nodeState.blockchain[|next.nodeState.blockchain|-1];
                    assert current.nodeState.blockchain +  [b] == next.nodeState.blockchain;

                    var bm :|
                            && bm in next.nodeState.messagesReceived
                            && validNewBlockMessage(current.nodeState.blockchain, bm)
                            && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b);

                    assert bm.block.header.height == |current.nodeState.blockchain| == |next.nodeState.blockchain|-1;

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, |next.nodeState.blockchain|-1);
                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, |next.nodeState.blockchain|-1);                        
                }


            }

            calc ==> {
                forall i | 1 <= i < |next.nodeState.blockchain|
                :: invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
                {
                    lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next);
                }
                invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  
            }    
            assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  

        } 
        else if(     
                || UponCommit(currentForSubsteps, nextForSubsteps, outQbftMessages)
                )    
        {
            assert current.nodeState.blockchain <= next.nodeState.blockchain;
            

            forall i | 1 <= i < |next.nodeState.blockchain|
            ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
            {
                if i < |current.nodeState.blockchain|
                {
                    var b := current.nodeState.blockchain[i];
                    assert b == next.nodeState.blockchain[i];

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(current, i);

                    var bm :|   && bm in current.nodeState.messagesReceived
                                && bm.NewBlock?
                                && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
                                && bm.block.header.height == i
                                && ValidNewBlock(current.nodeState.blockchain[..i], bm.block);

                    assert bm in next.nodeState.messagesReceived;
                    assert current.nodeState.blockchain[..i] == next.nodeState.blockchain[..i];


                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, i);   

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
                }
                else 
                {
                 
                    lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedUponCommit(current, inQbftMessages, next, outQbftMessages, i);
                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);  
                }
            }   

            assert forall i | 1 <= i < |next.nodeState.blockchain|
                :: invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);

            calc ==> {
                forall i | 1 <= i < |next.nodeState.blockchain|
                :: invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
                {
                    lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next);
                }
                invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  
            }       
            assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  

        }    
        else if(currentForSubsteps == nextForSubsteps)
        {
            assert current.nodeState.blockchain == next.nodeState.blockchain;
            assert current.nodeState.messagesReceived <= next.nodeState.messagesReceived;
            forall i | 1 <= i < |next.nodeState.blockchain|
            ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
            {
                var b := current.nodeState.blockchain[i];
                assert b == next.nodeState.blockchain[i];

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(current, i);

                var bm :|   && bm in current.nodeState.messagesReceived
                            && bm.NewBlock?
                            && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
                            && bm.block.header.height == i
                            && ValidNewBlock(current.nodeState.blockchain[..i], bm.block);

                assert bm in next.nodeState.messagesReceived;

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, i);   

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);

            }

            assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);
        }             
    }
/*
    lemma lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedOld(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient> 
    )
    requires validInstrStateEx(current)
    requires invInstrNodeStateBlocksInBlockchainHaveBeenReceived(current)
    requires indInvInstrNodeStateTypes(current);
    requires indInvInstrNodeStateProposalsAccepted(current);
    requires (validInstrStateEx(current) ==> invInstrNodeStateAllProposalsAcceptedAreValid(current));    
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)  
    ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next)
    {     

        var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;

        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );  

        var nextForSubsteps := next.nodeState;
    

        if(     
                // || (currentForSubsteps == nextForSubsteps && outQbftMessages == {})
                || UponBlockTimeout(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponProposal(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponPrepare(currentForSubsteps, nextForSubsteps, outQbftMessages)
                // || UponCommit(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponRoundChange(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponRoundTimeout(currentForSubsteps, nextForSubsteps, outQbftMessages)                
                // || UponNewBlock(currentForSubsteps, nextForSubsteps, outQbftMessages)
        )
        {
            assert current.nodeState.blockchain == next.nodeState.blockchain;
            assert current.nodeState.messagesReceived <= next.nodeState.messagesReceived;
            forall i | 0 <= i < |next.nodeState.blockchain|
            ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
            {
                var b := current.nodeState.blockchain[i];
                assert b == next.nodeState.blockchain[i];

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(current, i);

                var bm :|   && bm in current.nodeState.messagesReceived
                            && bm.NewBlock?
                            && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
                            && bm.block.header.height == i; 

                assert bm in next.nodeState.messagesReceived;

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, i);   

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);

            }

            calc ==> {
                forall i | 0 <= i < |next.nodeState.blockchain|
                :: invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
                {
                    lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next);
                }
                invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  
            } 
            assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  

        }         
        else if(     
                || UponNewBlock(currentForSubsteps, nextForSubsteps, outQbftMessages)
                )
        {
            assert current.nodeState.blockchain <= next.nodeState.blockchain;
            

            forall i | 0 <= i < |next.nodeState.blockchain|
            ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
            {
                if i < |current.nodeState.blockchain|
                {
                    var b := current.nodeState.blockchain[i];
                    assert b == next.nodeState.blockchain[i];

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(current, i);

                    var bm :|   && bm in current.nodeState.messagesReceived
                                && bm.NewBlock?
                                && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
                                && bm.block.header.height == i; 

                    assert bm in next.nodeState.messagesReceived;

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, i);   

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
                }
                else 
                {
                    assert i == |next.nodeState.blockchain|-1;
                    var b := next.nodeState.blockchain[|next.nodeState.blockchain|-1];
                    assert current.nodeState.blockchain +  [b] == next.nodeState.blockchain;

                    var bm :|
                            && bm in next.nodeState.messagesReceived
                            && validNewBlockMessage(current.nodeState.blockchain, bm)
                            && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b);

                    assert bm.block.header.height == |current.nodeState.blockchain| == |next.nodeState.blockchain|-1;

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, |next.nodeState.blockchain|-1);
                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, |next.nodeState.blockchain|-1);                        
                }


            }

            calc ==> {
                forall i | 0 <= i < |next.nodeState.blockchain|
                :: invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
                {
                    lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next);
                }
                invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  
            }    
            assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  

        } 
        else if(     
                // || UponNewBlock(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponCommit(currentForSubsteps, nextForSubsteps, outQbftMessages)
                // || UponRoundTimeout(currentForSubsteps, nextForSubsteps, outQbftMessages)
                )    
        {
            assert current.nodeState.blockchain <= next.nodeState.blockchain;
            

            forall i | 0 <= i < |next.nodeState.blockchain|
            ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
            {
                if i < |current.nodeState.blockchain|
                {
                    var b := current.nodeState.blockchain[i];
                    assert b == next.nodeState.blockchain[i];

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(current, i);

                    var bm :|   && bm in current.nodeState.messagesReceived
                                && bm.NewBlock?
                                && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
                                && bm.block.header.height == i; 

                    assert bm in next.nodeState.messagesReceived;

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, i);   

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
                }
                else 
                {
                    assert i == |next.nodeState.blockchain|-1;

                    var b := next.nodeState.blockchain[|next.nodeState.blockchain|-1];
                    assert current.nodeState.blockchain +  [b] == next.nodeState.blockchain;

                    assert current.nodeState.blockchain != next.nodeState.blockchain;

                    var allValidCommitsForCurrentHeightAndRound := 
                        validCommitsForHeightRoundAndDigest(
                            currentForSubsteps.messagesReceived,
                            |currentForSubsteps.blockchain|,
                            currentForSubsteps.round,
                            currentForSubsteps.proposalAcceptedForCurrentRound.value.proposedBlock,
                            validators(currentForSubsteps.blockchain));     

                    var proposedBlock:Block := currentForSubsteps.proposalAcceptedForCurrentRound.value.proposedBlock;

                    assert exists bm:QbftMessage, newcs: set<Signature>   ::
                            &&    next.nodeState.messagesReceived ==
                                           currentForSubsteps.messagesReceived + {bm}; 

                    assert forall bm |
                            && bm in  (next.nodeState.messagesReceived - currentForSubsteps.messagesReceived)
                            ::
                            && bm.NewBlock?
                            && areBlocksTheSameExceptForTheCommitSeals(bm.block, proposedBlock)
                            && invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, |next.nodeState.blockchain|-1)
                            ;

                    assert proposedBlock.header.height == |currentForSubsteps.blockchain|;
                    assert proposedBlock.header.height == |next.nodeState.blockchain|-1;

                    assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, |next.nodeState.blockchain|-1);
                    lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, |next.nodeState.blockchain|-1, i);    

                    calc {
                        invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, |next.nodeState.blockchain|-1);  
                        ==>  {
                            lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, |next.nodeState.blockchain|-1, i);    
                        }
                        invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);  
                    }                      
                }
            }   


            calc ==> {
                forall i | 0 <= i < |next.nodeState.blockchain|
                :: invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
                {
                    lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next);
                }
                invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  
            }       
            assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);  

        }    
        else if(currentForSubsteps == nextForSubsteps)
        {
            assert current.nodeState.blockchain == next.nodeState.blockchain;
            assert current.nodeState.messagesReceived <= next.nodeState.messagesReceived;
            forall i | 0 <= i < |next.nodeState.blockchain|
            ensures invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);
            {
                var b := current.nodeState.blockchain[i];
                assert b == next.nodeState.blockchain[i];

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(current, i);

                var bm :|   && bm in current.nodeState.messagesReceived
                            && bm.NewBlock?
                            && areBlocksTheSameExceptForTheCommitSealsAndRound(bm.block, b)
                            && bm.block.header.height == i; 

                assert bm in next.nodeState.messagesReceived;

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper(next, bm, b, i);   

                assert invInstrNodeStateBlocksInBlockchainHaveBeenReceivedHelper2(next, i);

            }

            assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);
        }

            // assert invInstrNodeStateBlocksInBlockchainHaveBeenReceived(next);        }               
    }
*/  

    // 32s
    lemma lemmaInstrNodeStateMessagesSentToItselfNotSignedByTheNodeHaveBeenReceived(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    // requires invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)
    ensures var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;
            var signedPayloadMessagesSentToItself := getSetOfSignedPayloads(next.nodeState.messagesReceived) - getSetOfSignedPayloads(newMessagesReceived);
            forall m |
                m in signedPayloadMessagesSentToItself ::
                recoverSignedPayloadSignature(m) == current.nodeState.id;      
    {
        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();  
        lemmaGetSetOfSignedPayloads(); 

        var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;

        var signedPayloadMessagesSentToItself := getSetOfSignedPayloads(next.nodeState.messagesReceived) - getSetOfSignedPayloads(newMessagesReceived);

        var currentForSubsteps :=
            current.nodeState.(
                messagesReceived := newMessagesReceived,
                localTime := next.nodeState.localTime
            );

        var nextForSubsteps := next.nodeState;

        assert currentForSubsteps.id == nextForSubsteps.id;
        assert next.messagesSent == current.messagesSent + multiset(outQbftMessages);

        if(     
                // || (currentForSubsteps == nextForSubsteps && outQbftMessages == {})
                || UponBlockTimeout(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponProposal(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponPrepare(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponCommit(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponNewBlock(currentForSubsteps, nextForSubsteps, outQbftMessages)
        )
        {
            assert forall m |
                m in signedPayloadMessagesSentToItself ::
                recoverSignedPayloadSignature(m) == current.nodeState.id;
            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) ==
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n);

            // assume invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);
        }         
        else if(     
                || UponRoundChange(currentForSubsteps, nextForSubsteps, outQbftMessages)
                || UponRoundTimeout(currentForSubsteps, nextForSubsteps, outQbftMessages)
                )
        {
            assert forall m |
                m in signedPayloadMessagesSentToItself ::
                recoverSignedPayloadSignature(m) == current.nodeState.id;            
            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))), n) <=
            //         // filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) +
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(currentForSubsteps.messagesReceived), n);

            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n) ==
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) +
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))), n);
                    
            // assume invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);

        } 
        else if(currentForSubsteps == nextForSubsteps)
        {
            assert outQbftMessages == {};

            assert forall m |
                m in signedPayloadMessagesSentToItself ::
                recoverSignedPayloadSignature(m) == current.nodeState.id;

            // assert forall n | n != next.nodeState.id ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(current.messagesSent)), n) ==
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(next.messagesSent)), n);            
            // assert invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(next);
        }           
   
    }          

    predicate indInvInstrNodeState(
        s:InstrNodeState
    )
    {
        && indInvInstrNodeStateTypes(s)
        && indInvInstrNodeStateProposalsAccepted(s)
        && invInstrNodeStateProposalsAccepted(s)
        && invInstrNodeStateNoConflictingPreapresSent(s)
        && indInvInstrNodeStateNoConflictingPreapresSent(s)   
        && invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(s)  
        && invInstrNodeStateCommitSentOnlyIfAcceptedProposal(s)     
        && invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyRoundChangeSent(s)
        && invInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares(s)
        && invInstrNodeStateIfCommitAndNextRoundChangeThenTheyMatch(s)
        && invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(s)
        && invInstrNodeStateInARoundAtLeastEqualToThoseOfAnyMessageSent(s)
        && invInstrNodeStatePrepareSentOnlyIfAcceptedProposal(s)
        && invInstrNodeStateCommitSentForLatestReceivedQuorumOfPrepares(s)
        && (validInstrState(s) ==> indInvInstrNodeStateAllProposalsAcceptedAreValid(s))
        && (validInstrStateEx(s) ==> invInstrNodeStateAllProposalsAcceptedAreValid(s))
        && indInvProposalAcceptedHaveBeenReceived(s)
        && invProposalAcceptedHaveBeenReceived(s)
        && indInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(s)
        && invRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(s)
        && invInstrNodeStatePrepareAndCommitMatch(s)
        && invInstrNodeStateBlocksInBlockchainHaveBeenReceived(s)
    }

    lemma lemmaIndInvInstrNodeState(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrStateEx(current)
    requires indInvInstrNodeState(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)    
    ensures indInvInstrNodeState(next)
    {
        lemmaInvInstrNodeStatePrepareSentOnlyIfAcceptedProposal(current, inQbftMessages, next,outQbftMessages);
        lemmaInvInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current, inQbftMessages, next,outQbftMessages);
        lemmaInvInstrNodeStateNoConflictingPreapresSent(current, inQbftMessages, next,outQbftMessages);
        lemmaInvInstrNodeStateCommitSentOnlyIfAcceptedProposal(current, inQbftMessages, next,outQbftMessages);
        lemmaInvInstrNodeStateInARoundAtLeastEqualToThoseOfAnyRoundChangeSent(current, inQbftMessages, next,outQbftMessages);
        lemmaInvInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares(current, inQbftMessages, next,outQbftMessages);
        lemmaInvInstrNodeStateNonEmptyRoundChangeSentOnlyIfReceivedQuorumOfPrepares2(current, inQbftMessages, next,outQbftMessages);
        lemmaInvInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived(current, inQbftMessages, next,outQbftMessages);
        leammIndInvInstrNodeStateAllProposalsAcceptedAreValid(current, inQbftMessages, next,outQbftMessages);
        lemmaInvInstrNodeStateAllProposalsAcceptedAreValid(current, inQbftMessages, next,outQbftMessages);
        lemmaInvProposalAcceptedHaveBeenReceived(current, inQbftMessages, next,outQbftMessages);
        lemmaInvRoundChangeHigherThanCommitHaveAtLeastEqualPreparedRound(current, inQbftMessages, next,outQbftMessages);
        lemmaInvInstrNodeStateBlocksInBlockchainHaveBeenReceived(current, inQbftMessages, next,outQbftMessages);

        lemmaInvInstrNodeStatePrepareAndCommitMatch(next);

    }

    lemma lemmaInitInstrNodeState(
        s: InstrNodeState,
        c: Configuration,
        id: Address
    )
    requires InstrNodeInit(s, c, id)
    ensures indInvInstrNodeState(s)
    ensures validInstrStateEx(s)
    {
        // assert proposerPrecondition(s.nodeState.blockchain);
        // assert (forall h | h <= s.nodeState.blockchain && h != [] :: proposerPrecondition(h));
        
        forall h | h <= s.nodeState.blockchain && h != []
        ensures proposerPrecondition(h)
        {
            assert h == s.nodeState.blockchain;
            assert proposerPrecondition(h);
        }
        assert validInstrStateEx(s);
    }


    lemma lemmaNodeNextSubstepIfCommitIsSentThenUponPrepareStep(
        current:NodeState, 
        next:NodeState,
        outQbftMessages: set<QbftMessageWithRecipient>,
        m: QbftMessage     
    )
    requires validNodeState(current)
    requires  NodeNextSubStep(current, next, outQbftMessages)
    requires m.Commit?
    requires 
        var newMessagesSentToItself :=  (next.messagesReceived - current.messagesReceived);
        var allMessagesSentByTheNodeAtThisStep := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages)) + newMessagesSentToItself;
        m in allMessagesSentByTheNodeAtThisStep
    ensures UponPrepare(current, next, outQbftMessages)
    ensures digest(optionGet(current.proposalAcceptedForCurrentRound).proposedBlock) == m.commitPayload.unsignedPayload.digest
    {
                            lemmaSignedCommit();
                            lemmaSignedHash();
    }

   
    lemma lemmaAllSentAreSignedByTheNode(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    // requires indInvInstrNodeStateProposalsAccepted(current)
    // requires invInstrNodeStateProposalsAccepted(current)
    // // requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)     
    ensures  forall m | m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))
                            && isMsgWithSignedPayload(m)
                        ::
                            recoverSignature(m) == current.nodeState.id;       
    {
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedProposal();
        lemmaSignedRoundChange();        
        assert next.nodeState.id == current.nodeState.id;

        assert forall m | m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))
                            && isMsgWithSignedPayload(m)
                        ::
                            recoverSignature(m) == current.nodeState.id;         
    }

    lemma lemmaAllCommitSentHaveMessageSignatureCorrespondingToCSSignature(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    // requires indInvInstrNodeStateProposalsAccepted(current)
    // requires invInstrNodeStateProposalsAccepted(current)
    // // requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)     
    ensures  forall m, b | && m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))
                           && m.Commit?
                           && m.commitPayload.unsignedPayload.digest == digest(b)
                        ::
                            recoverSignature(m) == recoverSignedHashAuthor(hashBlockForCommitSeal(b), m.commitPayload.unsignedPayload.commitSeal)    
    {
        // lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedHash();
        lemmaDigest();
        // lemmaSignedProposal();
        // lemmaSignedRoundChange();        
        assert next.nodeState.id == current.nodeState.id;

        // assert forall m | m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))
        //                     && isMsgWithSignedPayload(m)
        //                 ::
        //                     recoverSignature(m) == current.nodeState.id;         
    }    

    lemma lemmaAllSentAreSignedByTheNodeEx(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    // requires indInvInstrNodeStateProposalsAccepted(current)
    // requires invInstrNodeStateProposalsAccepted(current)
    // // requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)     
    ensures var messagesReceived := inQbftMessages;
            var newMessagesReceived := current.nodeState.messagesReceived + messagesReceived;                     
            var newMessagesSentToItself :=  (next.nodeState.messagesReceived - newMessagesReceived - current.nodeState.messagesReceived);
            var allMessagesSentIncToItself  := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages)) + newMessagesSentToItself;
            forall m | m in allMessagesSentIncToItself
                            && isMsgWithSignedPayload(m)
                        ::
                            recoverSignature(m) == current.nodeState.id;       
    {
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedProposal();
        lemmaSignedRoundChange();        
        assert next.nodeState.id == current.nodeState.id;
       
    }    

    lemma lemmaAllSentAreSignedByTheNodeExNotForAll(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>,
        m: QbftMessage        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    // requires indInvInstrNodeStateProposalsAccepted(current)
    // requires invInstrNodeStateProposalsAccepted(current)
    // // requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages) 
    requires    var messagesReceived := inQbftMessages;
                var newMessagesReceived := current.nodeState.messagesReceived + messagesReceived;                     
                var newMessagesSentToItself :=  (next.nodeState.messagesReceived - newMessagesReceived - current.nodeState.messagesReceived);
                var allMessagesSentIncToItself  := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages)) + newMessagesSentToItself;
                && m in allMessagesSentIncToItself
                && isMsgWithSignedPayload(m)    
    ensures recoverSignature(m) == current.nodeState.id;       
    {
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedProposal();
        lemmaSignedRoundChange();        
        assert next.nodeState.id == current.nodeState.id;
       
    }      


    lemma lemmaAllNewBlockSentThereIsACommitInReceived(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)    
    // // requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)     
    // ensures  forall m | m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))
    //                         && isMsgWithSignedPayload(m)
    //                     ::
    //                         recoverSignature(m) == current.nodeState.id;   
    ensures
        forall m,cs | m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))
                            && m.NewBlock?
                            && cs in m.block.header.commitSeals
        ::
            (
                && current.nodeState.proposalAcceptedForCurrentRound.Optional?
                && exists cm :: 
                    && cm in next.nodeState.messagesReceived  
                    && cm.Commit?
                    && var uPayload := cm.commitPayload.unsignedPayload;
                    var proposedBlock := current.nodeState.proposalAcceptedForCurrentRound.value.proposedBlock;
                    && uPayload.commitSeal == cs
                    && uPayload.round == m.block.header.roundNumber
                    && uPayload.height == m.block.header.height
                    && recoverSignedHashAuthor(hashBlockForCommitSeal(proposedBlock), uPayload.commitSeal) == recoverSignedCommitAuthor(cm.commitPayload)
            );    
    ensures indInvInstrNodeStateTypes(next)
    ensures indInvInstrNodeStateProposalsAccepted(next)
    ensures invInstrNodeStateProposalsAccepted(next)
    ensures invInstrNodeStateCommitSentOnlyIfAcceptedProposal(next)                     
    {
        // assert next.nodeState.id == current.nodeState.id;
        lemmaAllSentAreSignedByTheNode(current,inQbftMessages,next,outQbftMessages);
        lemmaInvInstrNodeStateProposalsAccepted(current,inQbftMessages,next,outQbftMessages);
        lemmaInvInstrNodeStateCommitSentOnlyIfAcceptedProposal(current,inQbftMessages,next,outQbftMessages);
        // lemmaSignedPrepare();
        // lemmaSignedCommit();
        // lemmaSignedProposal();
        // lemmaSignedRoundChange();        
        // assert next.nodeState.id == current.nodeState.id;
        // lemmaAllSentAreSignedByTheNode(current,inQbftMessages,next,outQbftMessages);
        // lemmaInvInstrNodeStateProposalsAccepted(current,inQbftMessages,next,outQbftMessages);
        // lemmaInvInstrNodeStateCommitSentOnlyIfAcceptedProposal(current,inQbftMessages,next,outQbftMessages);

        // forall m,cs | m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))
        //                     && m.NewBlock?
        //                     && cs in m.block.header.commitSeals
        // ensures
        //                 (
        //                     && current.nodeState.proposalAcceptedForCurrentRound.Optional?
        //                     && exists cm :: 
        //                         && cm in next.nodeState.messagesReceived  
        //                         && cm.Commit?
        //                         && var uPayload := cm.commitPayload.unsignedPayload;
        //                             var proposedBlock := current.nodeState.proposalAcceptedForCurrentRound.value.proposedBlock;
        //                         && uPayload.commitSeal == cs
        //                         && uPayload.round == m.block.header.roundNumber
        //                         && uPayload.height == m.block.header.height
        //                         && recoverSignedHashAuthor(hashBlockForCommitSeal(proposedBlock), uPayload.commitSeal) == recoverSignedCommitAuthor(cm.commitPayload)
        //                 );       
        // {
            // assert current.nodeState.proposalAcceptedForCurrentRound.Optional?;

            // // var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;

            // // var currentWithNewMessagesReceived :=
            // //     current.nodeState.(
            // //         messagesReceived := newMessagesReceived,
            // //         localTime := next.nodeState.localTime
            // //     );   

            // // assert currentWithNewMessagesReceived.messagesReceived <= next.nodeState.messagesReceived;            

            // var proposedBlock := current.nodeState.proposalAcceptedForCurrentRound.value.proposedBlock;

            // // var allValidCommitsForCurrentHeightAndRoundCurrentMessagesReceived := 
            // //     validCommitsForHeightRoundAndDigest(
            // //         currentWithNewMessagesReceived.messagesReceived,
            // //         |current.nodeState.blockchain|,
            // //         current.nodeState.round,
            // //         proposedBlock,
            // //         validators(current.nodeState.blockchain));  

            // var allValidCommitsForCurrentHeightAndRound := 
            //     validCommitsForHeightRoundAndDigest(
            //         next.nodeState.messagesReceived,
            //         |current.nodeState.blockchain|,
            //         current.nodeState.round,
            //         proposedBlock,
            //         validators(current.nodeState.blockchain));  

            // assert allValidCommitsForCurrentHeightAndRoundCurrentMessagesReceived <= allValidCommitsForCurrentHeightAndRound;

                  

            // assert UponCommit(currentWithNewMessagesReceived, next.nodeState,outQbftMessages );

            // assert  
            //     exists QofC ::
            //         && QofC <= allValidCommitsForCurrentHeightAndRoundCurrentMessagesReceived
            //         && (forall m:QbftMessage | m in QofC :: m.Commit?)
            //         && m.block.header.commitSeals == set m:QbftMessage | m in QofC :: m.commitPayload.unsignedPayload.commitSeal; 

            // var QofC :| && QofC <= allValidCommitsForCurrentHeightAndRoundCurrentMessagesReceived
            //             && (forall m:QbftMessage {:trigger m.Commit?} :: m in QofC ==> m.Commit?);
            //         // && m.block.header.commitSeals == set m:QbftMessage | m in QofC :: m.commitPayload.unsignedPayload.commitSeal; 
            // assert  
            //     // exists QofC ::
            //         && QofC <= allValidCommitsForCurrentHeightAndRound
            //         && (forall m:QbftMessage | m in QofC :: m.Commit?);
                    // && m.block.header.commitSeals == set m:QbftMessage | m in QofC :: m.commitPayload.unsignedPayload.commitSeal;                       

            // assert  
            //     exists QofC ::
            //         && QofC <= allValidCommitsForCurrentHeightAndRound
            //         && (forall m:QbftMessage | m in QofC :: m.Commit?)
            //         // && |QofC| == quorum(|validators(current.nodeState.blockchain)|)
            //         && m.block.header.commitSeals == set m:QbftMessage | m in QofC :: m.commitPayload.unsignedPayload.commitSeal;

            // assert  
            //     exists QofC ::
            //         && QofC <= allValidCommitsForCurrentHeightAndRound
            //         && (forall m:QbftMessage | m in QofC :: m.Commit?)
            //         // && |QofC| == quorum(|validators(current.nodeState.blockchain)|)
            //         && m.block.header.commitSeals == set m:QbftMessage | m in QofC :: m.commitPayload.unsignedPayload.commitSeal;

            // assert exists cm :: 
            //                     && cm in allValidCommitsForCurrentHeightAndRound
            //                     && cm.Commit?
            //                     && var uPayload := cm.commitPayload.unsignedPayload;
            //                     && uPayload.commitSeal == cs
            //                     && uPayload.round == m.block.header.roundNumber
            //                     && uPayload.height == m.block.header.height
            //                     && recoverSignedHashAuthor(hashBlockForCommitSeal(proposedBlock), uPayload.commitSeal) == recoverSignedCommitAuthor(cm.commitPayload);       

            // var cm :|  
            //                     && cm in next.nodeState.messagesReceived  
            //                     && cm.Commit?
            //                     && var uPayload := cm.commitPayload.unsignedPayload;
            //                     && uPayload.commitSeal == cs;  

            // assert
            //         exists pm ::    && pm in next.proposalsAccepted
            //                         &&  var cuPayload := m.commitPayload.unsignedPayload;
            //                             var puPayload := pm.proposalPayload.unsignedPayload;
            //                         &&  puPayload.height == cuPayload.height
            //                         &&  puPayload.round == cuPayload.round
            //                         &&  digest(pm.proposedBlock) == cuPayload.digest
            //                         &&  signHash(hashBlockForCommitSeal(pm.proposedBlock), next.nodeState.id) == cuPayload.commitSeal;                                   
        // }   

        // assert forall m,cs | m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))
        //                     && m.NewBlock?
        //                     && cs in m.block.header.commitSeals
        //                 ::
        //                 (
        //                     exists cm :: 
        //                         && cm in next.nodeState.messagesReceived  
        //                         && cm.Commit?
        //                         && var uPayload := cm.commitPayload.unsignedPayload;
        //                         && uPayload.commitSeal == cs
        //                 );  
    }    

    lemma lemmaAllNewBlockSentIncItselfThereIsACommitInReceived(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>        
    ) 
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateProposalsAccepted(current)
    requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)    
    // // requires invInstrNodeStateCommitSentOnlyIfReceivedQuorumOfPrepares(current)
    // requires invInstrNodeStateCommitSentOnlyIfAcceptedProposal(current)
    // requires invInstrNodeStateNoConflictingPreapresSent(current)
    // requires indInvInstrNodeStateNoConflictingPreapresSent(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)     
    // ensures  forall m | m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))
    //                         && isMsgWithSignedPayload(m)
    //                     ::
    //                         recoverSignature(m) == current.nodeState.id;   
    ensures
            var messagesReceived := inQbftMessages;
            var newMessagesReceived := current.nodeState.messagesReceived + messagesReceived;                     
            var newMessagesSentToItself :=  (next.nodeState.messagesReceived - newMessagesReceived - current.nodeState.messagesReceived);
            var allMessagesSentIncToItself  := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages)) + newMessagesSentToItself;
            forall m,cs | m in allMessagesSentIncToItself
                                && m.NewBlock?
                                && cs in m.block.header.commitSeals
            ::
                (
                    && current.nodeState.proposalAcceptedForCurrentRound.Optional?
                    && exists cm :: 
                        && cm in next.nodeState.messagesReceived  
                        && cm.Commit?
                        && var uPayload := cm.commitPayload.unsignedPayload;
                        var proposedBlock := current.nodeState.proposalAcceptedForCurrentRound.value.proposedBlock;
                        && uPayload.commitSeal == cs
                        && uPayload.round == m.block.header.roundNumber
                        && uPayload.height == m.block.header.height
                        && recoverSignedHashAuthor(hashBlockForCommitSeal(proposedBlock), uPayload.commitSeal) == recoverSignedCommitAuthor(cm.commitPayload)
                );    
    ensures indInvInstrNodeStateTypes(next)
    ensures indInvInstrNodeStateProposalsAccepted(next)
    ensures invInstrNodeStateProposalsAccepted(next)
    ensures invInstrNodeStateCommitSentOnlyIfAcceptedProposal(next)                     
    {
        // assert next.nodeState.id == current.nodeState.id;
        lemmaAllSentAreSignedByTheNodeEx(current,inQbftMessages,next,outQbftMessages);
        lemmaInvInstrNodeStateProposalsAccepted(current,inQbftMessages,next,outQbftMessages);
        lemmaInvInstrNodeStateCommitSentOnlyIfAcceptedProposal(current,inQbftMessages,next,outQbftMessages);
        // lemmaSignedPrepare();
        // lemmaSignedCommit();
        // lemmaSignedProposal();
        // lemmaSignedRoundChange();        
        // assert next.nodeState.id == current.nodeState.id;
        // lemmaAllSentAreSignedByTheNode(current,inQbftMessages,next,outQbftMessages);
        // lemmaInvInstrNodeStateProposalsAccepted(current,inQbftMessages,next,outQbftMessages);
        // lemmaInvInstrNodeStateCommitSentOnlyIfAcceptedProposal(current,inQbftMessages,next,outQbftMessages);

        // forall m,cs | m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))
        //                     && m.NewBlock?
        //                     && cs in m.block.header.commitSeals
        // ensures
        //                 (
        //                     && current.nodeState.proposalAcceptedForCurrentRound.Optional?
        //                     && exists cm :: 
        //                         && cm in next.nodeState.messagesReceived  
        //                         && cm.Commit?
        //                         && var uPayload := cm.commitPayload.unsignedPayload;
        //                             var proposedBlock := current.nodeState.proposalAcceptedForCurrentRound.value.proposedBlock;
        //                         && uPayload.commitSeal == cs
        //                         && uPayload.round == m.block.header.roundNumber
        //                         && uPayload.height == m.block.header.height
        //                         && recoverSignedHashAuthor(hashBlockForCommitSeal(proposedBlock), uPayload.commitSeal) == recoverSignedCommitAuthor(cm.commitPayload)
        //                 );       
        // {
            // assert current.nodeState.proposalAcceptedForCurrentRound.Optional?;

            // // var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;

            // // var currentWithNewMessagesReceived :=
            // //     current.nodeState.(
            // //         messagesReceived := newMessagesReceived,
            // //         localTime := next.nodeState.localTime
            // //     );   

            // // assert currentWithNewMessagesReceived.messagesReceived <= next.nodeState.messagesReceived;            

            // var proposedBlock := current.nodeState.proposalAcceptedForCurrentRound.value.proposedBlock;

            // // var allValidCommitsForCurrentHeightAndRoundCurrentMessagesReceived := 
            // //     validCommitsForHeightRoundAndDigest(
            // //         currentWithNewMessagesReceived.messagesReceived,
            // //         |current.nodeState.blockchain|,
            // //         current.nodeState.round,
            // //         proposedBlock,
            // //         validators(current.nodeState.blockchain));  

            // var allValidCommitsForCurrentHeightAndRound := 
            //     validCommitsForHeightRoundAndDigest(
            //         next.nodeState.messagesReceived,
            //         |current.nodeState.blockchain|,
            //         current.nodeState.round,
            //         proposedBlock,
            //         validators(current.nodeState.blockchain));  

            // assert allValidCommitsForCurrentHeightAndRoundCurrentMessagesReceived <= allValidCommitsForCurrentHeightAndRound;

                  

            // assert UponCommit(currentWithNewMessagesReceived, next.nodeState,outQbftMessages );

            // assert  
            //     exists QofC ::
            //         && QofC <= allValidCommitsForCurrentHeightAndRoundCurrentMessagesReceived
            //         && (forall m:QbftMessage | m in QofC :: m.Commit?)
            //         && m.block.header.commitSeals == set m:QbftMessage | m in QofC :: m.commitPayload.unsignedPayload.commitSeal; 

            // var QofC :| && QofC <= allValidCommitsForCurrentHeightAndRoundCurrentMessagesReceived
            //             && (forall m:QbftMessage {:trigger m.Commit?} :: m in QofC ==> m.Commit?);
            //         // && m.block.header.commitSeals == set m:QbftMessage | m in QofC :: m.commitPayload.unsignedPayload.commitSeal; 
            // assert  
            //     // exists QofC ::
            //         && QofC <= allValidCommitsForCurrentHeightAndRound
            //         && (forall m:QbftMessage | m in QofC :: m.Commit?);
                    // && m.block.header.commitSeals == set m:QbftMessage | m in QofC :: m.commitPayload.unsignedPayload.commitSeal;                       

            // assert  
            //     exists QofC ::
            //         && QofC <= allValidCommitsForCurrentHeightAndRound
            //         && (forall m:QbftMessage | m in QofC :: m.Commit?)
            //         // && |QofC| == quorum(|validators(current.nodeState.blockchain)|)
            //         && m.block.header.commitSeals == set m:QbftMessage | m in QofC :: m.commitPayload.unsignedPayload.commitSeal;

            // assert  
            //     exists QofC ::
            //         && QofC <= allValidCommitsForCurrentHeightAndRound
            //         && (forall m:QbftMessage | m in QofC :: m.Commit?)
            //         // && |QofC| == quorum(|validators(current.nodeState.blockchain)|)
            //         && m.block.header.commitSeals == set m:QbftMessage | m in QofC :: m.commitPayload.unsignedPayload.commitSeal;

            // assert exists cm :: 
            //                     && cm in allValidCommitsForCurrentHeightAndRound
            //                     && cm.Commit?
            //                     && var uPayload := cm.commitPayload.unsignedPayload;
            //                     && uPayload.commitSeal == cs
            //                     && uPayload.round == m.block.header.roundNumber
            //                     && uPayload.height == m.block.header.height
            //                     && recoverSignedHashAuthor(hashBlockForCommitSeal(proposedBlock), uPayload.commitSeal) == recoverSignedCommitAuthor(cm.commitPayload);       

            // var cm :|  
            //                     && cm in next.nodeState.messagesReceived  
            //                     && cm.Commit?
            //                     && var uPayload := cm.commitPayload.unsignedPayload;
            //                     && uPayload.commitSeal == cs;  

            // assert
            //         exists pm ::    && pm in next.proposalsAccepted
            //                         &&  var cuPayload := m.commitPayload.unsignedPayload;
            //                             var puPayload := pm.proposalPayload.unsignedPayload;
            //                         &&  puPayload.height == cuPayload.height
            //                         &&  puPayload.round == cuPayload.round
            //                         &&  digest(pm.proposedBlock) == cuPayload.digest
            //                         &&  signHash(hashBlockForCommitSeal(pm.proposedBlock), next.nodeState.id) == cuPayload.commitSeal;                                   
        // }   

        // assert forall m,cs | m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages))
        //                     && m.NewBlock?
        //                     && cs in m.block.header.commitSeals
        //                 ::
        //                 (
        //                     exists cm :: 
        //                         && cm in next.nodeState.messagesReceived  
        //                         && cm.Commit?
        //                         && var uPayload := cm.commitPayload.unsignedPayload;
        //                         && uPayload.commitSeal == cs
        //                 );  
    }     
}