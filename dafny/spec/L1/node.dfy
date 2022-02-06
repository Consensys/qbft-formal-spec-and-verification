/**
 * Copyright © 2021 EEA Inc. 
 *
 * This document is available under the terms of the Apache 2.0 License
 * (http://www.apache.org/licenses/LICENSE-2.0.html)
 */
include "types.dfy"
include "node_auxiliary_functions.dfy"
include "lemmas.dfy"

module EEASpec
{
    import opened EEASpecTypes
    import opened EEAAuxiliaryFunctionsAndLemmas
    import opened EEALemmas


    /** =======================================================================
     * QBFT SPECIFICATION
     ========================================================================*/   
    // TODO: Check this one   
    /**
     * TO BE FIXED
     *
     * This function provides the overall specification of the QBFT protocol.
     *
     * @param configuration The system configuration
     * @param id The QBFT node id.
     * @param rms Sequence of messages received by node `id` where `rmt[i]` is
     *            the set of messages received on its `i`-th local clock tick.
     *
     * @returns 
     * 
     * 
     * The set, possible infinite, that specifies all the possible set
     *          of messages that a node `id` is allowed to send and the
     *          blockchains that a node `id` must have after receiving the
     *          sequence of messages `rms` when deployed in a QBFT network with
     *          configuration `c`. Specifically, a QBFT node with identifier
     *          `id`, that is deployed in a system with configuration `c` and
     *          that has received the sequence of messages `rms`, is allowed to
     *          send messages as specified by the set `outQbftMessages` and have
     *          blockchain `bc` only if the pair (`outQbftMessages`, `bc`) is
     *          included in the set returned by `QbftSpecification(c, id, rms)`.
     */
    function QbftSpecification(
        configuration: Configuration,
        id: Address,
        rms: seq<set<QbftMessage>>):
        iset<(set<QbftMessageWithRecipient>, Blockchain)>
    requires |rms| > 0 
    {
        iset sm:set<QbftMessageWithRecipient>, blockchain: Blockchain |
            exists nt: seq<NodeState>, smt: seq<set<QbftMessageWithRecipient>> ::
                && |nt| == |rms| + 1
                && |smt| == |rms|
                && NodeInit(nt[0], configuration, id)
                && (forall i:nat | 0 <= i < |rms| ::
                        && validNodeState(nt[i])
                        && NodeNext(nt[i], rms[i], nt[i+1], smt[i])
                )
                && sm == smt[|smt|-1]
                && blockchain == nt[|nt|-1].blockchain 
            ::
                (sm, blockchain)
    }       

    /** =======================================================================
     * QBFT NODE STATE TRANSITION AND MESSAGE TRANSMISSION SPECIFICATION
     ========================================================================*/    
    /**
     * Initial State Specification.
     *
     * This predicate specifies the set of allowed initial states for a QBFT
     * node.
     *
     * @param state A QBFT node state.
     * @param c A QBFT network configuration.
     * @param id A QBFT node identifier.
     *
     * @returns `true` if and only if `state` is a valid initial QBFT state for
     *          a node with id `id` deployed in a QBFT network with
     *          configuration `c`. 
     */
    predicate NodeInit(state:NodeState, c:Configuration, id:Address)
    {
        && state.blockchain == [c.genesisBlock]
        && |validators([c.genesisBlock])| > 0
        && state.round == 0
        && state.localTime == 0
        && state.id == id
        && state.configuration == c
        && state.messagesReceived == {} 
        && state.proposalAcceptedForCurrentRound == None
        && state.lastPreparedBlock == None
        && state.lastPreparedRound == None
        && state.timeLastRoundStart == 0
    }

    /**
     * Next State and Message Transmission Specification.
     *
     * This predicate specifies how the state of a QBFT node should evolve and
     * which messages should be transmitted every time that its system clock
     * ticks.
     *
     * @param current Current, or old, QBFT node state.
     * @param inQbftMessages The of messages received when the node clock ticks.
     * @param next Next state QBFT node state.
     * @param outQbftMessages Set of messages with recipient to be sent by the
     *                        QBFT node.
     *
     * @returns `true` if and only if a QBFT node with state `current` that
     *          receives the set of messages `inQbftMessages` on the next tick
     *          of its local clock can transition to state `next` and send the
     *          set of messages with recipient `outQbftMessages`.
     */
    predicate NodeNext(
        current:NodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:NodeState,
        outQbftMessages: set<QbftMessageWithRecipient>
        )
    requires validNodeState(current)   
    {
        var newMessagesReceived := current.messagesReceived + inQbftMessages;

        var currentWithNewMessagesReceived :=
            current.(
                messagesReceived := newMessagesReceived,
                localTime := current.localTime + 1
            );
    
        // `next` and `outQbftMessages` must be the result result of the
        // composition of as many `NodeNextSubStep` predicates as possible until
        // only stuttering actions are possible, i.e. until `NodeNextSubStep` is
        // `true` only if the state provided for the `next` parameter matches
        // the state provided for the `current` parameter and the
        // `outQbftMessages` parameter corresponds to the empty set.
        exists s:seq<NodeState>, o:seq<set<QbftMessageWithRecipient>> ::
            && |s| >= 2
            && |o| == |s| - 1
            && s[0] == currentWithNewMessagesReceived
            && s[|s|-1] == next
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
    }

    /**
     * Single Step State and Message Transmission Specification
     *
     * This predicate specifies how the state of a QBFT node should evolve and
     * which messages should be transmitted for any single event, like the
     * reception of a message of a specific type or the expiry of a specific
     * timer, that may occur when its local clock ticks. The predicate assumes
     * that `current.messagesReceived` corresponds to the set of all and only
     * messages received so far by the node. 
     *
     *
     * @param current Current, or old, QBFT node state.
     * @param next Next state QBFT node state.
     * @param outQbftMessages Set of messages with recipient to be sent by the
     * QBFT node.
     *
     * @returns `true` if and only if a QBFT node with state `current` that has
     *          received the set of messages `current.messagesReceived` can
     *          transition to state `next` and send the set of messages with
     *          recipient `outQbftMessages` when its local clock ticks.
     */
    predicate NodeNextSubStep(
        current:NodeState, 
        next: NodeState,

        outQbftMessages: set<QbftMessageWithRecipient>
    )
    requires validNodeState(current)       
    {
        || (
            && current.id in validators(current.blockchain)
            && (
                || UponBlockTimeout(current, next, outQbftMessages)
                || UponProposal(current, next, outQbftMessages)
                || UponPrepare(current, next, outQbftMessages)
                || UponCommit(current, next, outQbftMessages)
                || UponRoundChange(current, next, outQbftMessages)
                || UponRoundTimeout(current, next, outQbftMessages)
            )
        )
        || UponNewBlock(current, next, outQbftMessages)
        || (
            && next == current
            && outQbftMessages == {}
        )   
    }    

    /** =======================================================================
     * QBFT SINGLE EVENT STATE TRANSITION AND MESSAGE TRANSMISSION SPECIFICATION
     *
     * Each of the Upon<EventName> predicates in the remainder of this file
     * specifies how the state of a QBFT node should evolve and which messages
     * should be transmitted when the event <EventName> occurs the next local
     * clock tick.
     *
     * An <EventName> that end in `Timeout` indicates the expiry of a time, all
     * other event <EventName>s indicate the reception of a specific QBFT
     * message, i.e. `UponProposal` is the predicate associate with the
     * reception of a Proposal message.
     *
     * All Upon<EventName> predicates have the same parameters and the same
     * return value. Namely, 
     * @param current Current, or old, QBFT node state.
     * @param next Next state QBFT node state.
     * @param outQbftMessages Set of messages with recipient to be sent by the
     *                        QBFT node.
     *
     * @returns `true` if and only if a QBFT node with state `current` that has
     *          received the set of messages `current.messagesReceived` can
     *          transition to state `next` and send the set of messages with
     *          recipient `outQbftMessages` when event <EventName> occurs on its
     *          next local clock tick.
     ========================================================================*/  

    predicate UponBlockTimeout(
        current:NodeState,
        next: NodeState,

        outQbftMessages: set<QbftMessageWithRecipient>
        )
    requires validNodeState(current)      
    {
        if  && current.round == 0
            && proposer(0,current.blockchain) == current.id
            && current.localTime >= 
                current.blockchain[|current.blockchain|-1].header.timestamp + 
                current.configuration.blockTime 
        then
            var block := getNewBlock(current, 0);

            var proposal :=
                Proposal(
                    signProposal(
                        UnsignedProposal(
                            |current.blockchain|,
                            0,
                            digest(block)),
                        current.id),
                    block,
                    {},
                    {});
            
            && outQbftMessages ==
                Multicast(
                    validators(current.blockchain),
                    proposal
                )

            && next == current.(
                            messagesReceived := current.messagesReceived + {proposal}
                        )
        else
            false

    }  
 
    predicate UponProposal(
        current:NodeState, 
        next: NodeState,

        outQbftMessages: set<QbftMessageWithRecipient>)
    requires validNodeState(current)
    {
        if  exists m | m in current.messagesReceived :: isValidProposal(m, current)
        then
            var m :|    && m in current.messagesReceived
                        && isValidProposal(m, current);

            var newRound := m.proposalPayload.unsignedPayload.round;
            
            var prepare := 
                Prepare(
                    signPrepare(
                        UnsignedPrepare(
                            |current.blockchain|,
                            newRound,
                            digest(m.proposedBlock)),
                        current.id
                        )
                );

            && outQbftMessages ==
                    Multicast(
                        validators(current.blockchain),
                        prepare
                    )

            && next == current.(
                            round := newRound,
                            proposalAcceptedForCurrentRound := Optional(m),
                            timeLastRoundStart :=
                                if m.proposalPayload.unsignedPayload.round > current.round then
                                    current.localTime
                                else
                                    current.timeLastRoundStart  ,
                            messagesReceived := current.messagesReceived + {prepare}                 
                        )

        else
            false
    }   

    predicate UponPrepare(
        current:NodeState,
        next: NodeState,

        outQbftMessages: set<QbftMessageWithRecipient>
        )
    requires validNodeState(current)
    {
        if  && exists QofP:: 
                    && optionIsPresent(current.proposalAcceptedForCurrentRound)

                    && QofP <= validPreparesForHeightRoundAndDigest(
                                current.messagesReceived,
                                |current.blockchain|,
                                current.round,
                                digest(optionGet(current.proposalAcceptedForCurrentRound).proposedBlock),
                                validators(current.blockchain))
                    && |QofP| >= quorum(|validators(current.blockchain)|) 

            && !exists m :: && m in current.messagesReceived
                            && m.Commit?
                            && var uPayload := m.commitPayload.unsignedPayload;
                            && uPayload.height == |current.blockchain|
                            && uPayload.round == current.round
                            && recoverSignedCommitAuthor(m.commitPayload) == current.id
        then          
            var proposedBlock := optionGet(current.proposalAcceptedForCurrentRound).proposedBlock;

            var commit := 
                Commit(
                    signCommit(
                        UnsignedCommit(
                            |current.blockchain|,
                            current.round,
                            signHash(hashBlockForCommitSeal(proposedBlock), current.id),
                            digest(proposedBlock)),
                            current.id
                        )
                    );

            && outQbftMessages == 
                Multicast(
                    validators(current.blockchain),
                    commit
                )

            && next == current.(
                            lastPreparedBlock := Optional(proposedBlock),
                            lastPreparedRound := Optional(current.round),
                            messagesReceived := current.messagesReceived + {commit}
                        )
                     
        else
            false 
    }

    function getCommitSealsFromCommitMessages(
        msgs: set<QbftMessage>
    ): set<Signature>
    requires forall m | m in msgs :: m.Commit?
    {
        set m:QbftMessage | m in msgs :: m.commitPayload.unsignedPayload.commitSeal
    }

    predicate UponCommit(
        current:NodeState,
        next: NodeState,

        outQbftMessages: set<QbftMessageWithRecipient>
        )
    requires validNodeState(current)
    {
        if current.proposalAcceptedForCurrentRound.Optional? then
            var allValidCommitsForCurrentHeightAndRound := 
                validCommitsForHeightRoundAndDigest(
                    current.messagesReceived,
                    |current.blockchain|,
                    current.round,
                    current.proposalAcceptedForCurrentRound.value.proposedBlock,
                    validators(current.blockchain));

            if  exists QofC:: 
                    && QofC <= allValidCommitsForCurrentHeightAndRound
                    && |QofC| >= quorum(|validators(current.blockchain)|) 
            then  
                // The following statement is required only to let the varifier
                // prove the existence of the var QofC below
                lemmaIfSubSetOfGreaterSizeExistsThenSmallSubsetExists(allValidCommitsForCurrentHeightAndRound, quorum(|validators(current.blockchain)|));

                var QofC:|
                    && QofC <= allValidCommitsForCurrentHeightAndRound
                    && |QofC| == quorum(|validators(current.blockchain)|);

                var proposedBlock:Block := current.proposalAcceptedForCurrentRound.value.proposedBlock;

                var blockWithAddedCommitSeals :=  
                    proposedBlock.(
                        header := proposedBlock.header.(
                            commitSeals := getCommitSealsFromCommitMessages(QofC)
                        )
                    );            

                var newBlock := NewBlock( blockWithAddedCommitSeals);

                && outQbftMessages == 
                    Multicast(
                        current.configuration.nodes,
                        newBlock
                    )

                && next == current.(
                                blockchain := current.blockchain + [proposedBlock],
                                round := 0,
                                proposalAcceptedForCurrentRound := Optional.None,
                                lastPreparedBlock := Optional.None,
                                lastPreparedRound := Optional.None,
                                timeLastRoundStart := current.localTime,
                                messagesReceived := current.messagesReceived + {newBlock}
                            )
                        
            else
                false 
        else
            false
    }    

    predicate UponNewBlock(
        current:NodeState,
        next: NodeState,

        outQbftMessages: set<QbftMessageWithRecipient>
        )
    requires validNodeState(current)
    {
        if exists m | m in current.messagesReceived :: validNewBlockMessage(current.blockchain,m)
        then
            var m :| m in current.messagesReceived && validNewBlockMessage(current.blockchain,m);

            && next == current.(
                            blockchain := current.blockchain + [m.block],
                            round := 0,
                            proposalAcceptedForCurrentRound := Optional.None,
                            lastPreparedBlock := Optional.None,
                            lastPreparedRound := Optional.None,
                            timeLastRoundStart := current.localTime                            
                        )

            && outQbftMessages == {}
        else
            false
    } 

    predicate UponRoundTimeout(
        current:NodeState, 
        next: NodeState,

        outQbftMessages: set<QbftMessageWithRecipient>
        )
    requires validNodeState(current)
    {
        if  current.localTime >= current.timeLastRoundStart + roundTimeout(current.round)
        then
            var newRound := current.round + 1;
            var roundChange := createRoundChange(current, newRound);

            && outQbftMessages ==
                Multicast(
                    validators(current.blockchain),
                    roundChange
                )

            && next == current.(
                            round := newRound,
                            proposalAcceptedForCurrentRound := Optional.None,
                            messagesReceived := current.messagesReceived + {roundChange}
                        )
        else
            false
    }

    predicate UponRoundChange(
        current:NodeState, 
        next: NodeState,

        outQbftMessages: set<QbftMessageWithRecipient>)
    requires validNodeState(current)
    {
        if  hasReceivedProposalJustification(current)
        then
            var roundChanges,
                prepares,
                newRound:nat,
                block
                :|
                    isReceivedProposalJustification(roundChanges, prepares, newRound, block, current);

            var proposal :=
                Proposal(
                    signProposal(
                        UnsignedProposal(
                            |current.blockchain|,
                            newRound,
                            digest(block)),
                        current.id),
                    block,
                    extractSignedRoundChanges(roundChanges),
                    extractSignedPrepares(prepares));

            && outQbftMessages ==
                Multicast(
                    validators(current.blockchain),
                    proposal
                )

            && next ==  current.(
                            round := newRound,
                            proposalAcceptedForCurrentRound := Optional.None,
                            timeLastRoundStart :=
                                if newRound > current.round then
                                    current.localTime
                                else
                                    current.timeLastRoundStart,
                            messagesReceived := current.messagesReceived + {proposal}
                        )

        else if 
            exists Frc:set<SignedRoundChange> ::
                && Frc <= receivedSignedRoundChangesForCurrentHeightAndFutureRounds(current)
                && |getSetOfRoundChangeSenders(Frc)| >= f(|validators(current.blockchain)|) + 1
        then
            // The following lemma is not really part of the specification.
            // It is only required to prove that the set `Frc` below exists.
            lemmaToProveExistenceOfSetFrc(
                receivedSignedRoundChangesForCurrentHeightAndFutureRounds(current), 
                f(|validators(current.blockchain)|) + 1 );                
            
            var Frc:set<SignedRoundChange> :| 
                && Frc <= receivedSignedRoundChangesForCurrentHeightAndFutureRounds(current)
                && |getSetOfRoundChangeSenders(Frc)| == f(|validators(current.blockchain)|) + 1;

            var newRound := minSet(set rcm | rcm in Frc :: rcm.unsignedPayload.round);


            var roundChange := createRoundChange(current, newRound);

            && outQbftMessages ==
                Multicast(
                    validators(current.blockchain),
                    roundChange
                )

            && next == current.(
                            round := newRound,
                            proposalAcceptedForCurrentRound := Optional.None,
                            messagesReceived := current.messagesReceived + {roundChange}
                        )
        else
            false

    } 
}

