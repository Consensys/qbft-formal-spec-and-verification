/**
 * Copyright © 2021 EEA Inc. 
 *
 * This document is available under the terms of the Apache 2.0 License
 * (http://www.apache.org/licenses/LICENSE-2.0.html)
 */
include "types.dfy"
include "lemmas.dfy"

module L1_AuxiliaryFunctionsAndLemmas
{
    import opened L1_SpecTypes

    /** =======================================================================
     * CRYPTOGRAPHIC PRIMITIVES
     *
     * This section contains the declarations of the various cryptographic
     * primitives used throughout the specification along with `lemma`s listing
     * the minimum set of properties that each of them must satisfy.
     *
     * - The functions `sign<MessageType>(msg, author)` evaluate to a
     *   <MessageType> message signed by `author` with content `msg`.
     *
     * - The function `recoverSigned<MessagetType>Author(msg)` evaluate to the
     *   signer of the <MessageType> message `msg`.
     *
     * - The lemmas `lemmaSigned<MessageType>` list the minimum set of
     *   properties that any implementations of the `sign<MessageType>` and
     *   `recoverSigned<MessagetType>Author` functions used in the
     *   implementation of the QBFT specification must satisfy.
     *
     * - NOTE: In addition to the various properties of the formally stated in
     *   this specification, the `sign<MessageType>` and
     *   `recoverSigned<MessagetType>Author` functions must also ensure that the
     *   signatures cannot be forged by Byzantine nodes. This property can be
     *   formally expressed by providing a formal model of the systems
     *   (networks) that the QBFT protocol is intended to be deployed on. In the
     *   future, the QBFT specification may be extended to include such model.
     *
     ========================================================================*/  

    /**
     * @returns The digest of the block `block`.
     */
    function digest(block:Block):Hash

    /**
     * This lemma lists the minimum set of properties that any implementation of
     * the `digest` function used in the implementation of the QBFT
     * specification must satisfy.
     */
    lemma {:axiom} lemmaDigest()
    ensures forall b1, b2 :: digest(b1) == digest(b2) ==> b1 == b2     

    
    function signProposal(msg:UnsignedProposal, author: Address): SignedProposal  
    function recoverSignedProposalAuthor(msg:SignedProposal): Address     
    lemma {:axiom} lemmaSignedProposal()
    ensures forall m,a :: recoverSignedProposalAuthor(signProposal(m,a)) == a
    ensures forall m1,m2,a1,a2 :: (m1 != m2 || a1 != a2) ==> signProposal(m1,a1) != signProposal(m2,a2)
    ensures forall m: SignedProposal :: signProposal(m.unsignedPayload,recoverSignedProposalAuthor(m)) == m
    ensures forall m,a :: signProposal(m,a).unsignedPayload == m 

    function signPrepare(msg:UnsignedPrepare, author: Address): SignedPrepare
    function recoverSignedPrepareAuthor(msg:SignedPrepare): Address    
    lemma {:axiom} lemmaSignedPrepare()
    ensures forall m,a :: recoverSignedPrepareAuthor(signPrepare(m,a)) == a
    ensures forall m1,m2,a1,a2 :: (m1 != m2 || a1 != a2) ==> signPrepare(m1,a1) != signPrepare(m2,a2)
    ensures forall m: SignedPrepare :: signPrepare(m.unsignedPayload,recoverSignedPrepareAuthor(m)) == m
    ensures forall m,a :: signPrepare(m,a).unsignedPayload == m
    
    function signCommit(msg:UnsignedCommit, author: Address): SignedCommit
    function recoverSignedCommitAuthor(msg:SignedCommit): Address    
    lemma {:axiom} lemmaSignedCommit()
    ensures forall m,a :: recoverSignedCommitAuthor(signCommit(m,a)) == a
    ensures forall m1,m2,a1,a2 :: (m1 != m2 || a1 != a2) ==> signCommit(m1,a1) != signCommit(m2,a2)
    ensures forall m: SignedCommit :: signCommit(m.unsignedPayload,recoverSignedCommitAuthor(m)) == m
    ensures forall m,a :: signCommit(m,a).unsignedPayload == m   

    function signRoundChange(msg:UnsignedRoundChange, author: Address): SignedRoundChange
    function recoverSignedRoundChangeAuthor(msg:SignedRoundChange): Address    
    lemma {:axiom} lemmaSignedRoundChange()
    ensures forall m,a :: recoverSignedRoundChangeAuthor(signRoundChange(m,a)) == a
    ensures forall m1,m2,a1,a2 :: (m1 != m2 || a1 != a2) ==> signRoundChange(m1,a1) != signRoundChange(m2,a2)
    ensures forall m: SignedRoundChange :: signRoundChange(m.unsignedPayload,recoverSignedRoundChangeAuthor(m)) == m
    ensures forall m,a :: signRoundChange(m,a).unsignedPayload == m

    function signHash(hash:Hash, author: Address): Signature
    function recoverSignedHashAuthor(hash:Hash, signature: Signature): Address   
    lemma {:axiom} lemmaSignedHash()
    ensures forall h,a :: recoverSignedHashAuthor(h, signHash(h,a)) == a
    ensures forall h1,h2,a1,a2 :: (h1 != h2 || a1 != a2) ==> signHash(h1,a1) != signHash(h2,a2)
    ensures forall h,s :: signHash(h,recoverSignedHashAuthor(h,s)) == s     

    /** =======================================================================
     * UNDEFINED FUNCTIONS
     *
     * This section includes those functions for which no actual definition is
     * provided as that is beyond the scope of this specification. 
     ========================================================================*/  

    /**
     * @return `true` if and only if `block` is a valid `RawBlock` for the
     *         `RawBlockchain` `blockchain`. 
     *
     * @note This predicate is expected to check that `block` is valid from an
     *       blockchain application level perspective. This contrasts with the
     *       predicate `ValidNewBlock` defined below which checks that a block
     *       is valid from a consensus protocol perspective.
     */
    predicate validateRawEthereumBlock(blockchain:RawBlockchain, block:RawBlock)   

    /**
     * @return The set of nodes, or validators, responsible for deciding on the
     *         block to be appended to the `RawBlockchain` `rb`.
     */
    function validatorsOnRawBlockchain(rb: RawBlockchain): seq<Address>  

    /**
     * @returns The minimum value in set `S`.
     */
    function minSet(S:set<nat>): nat
    ensures minSet(S) in S 
    ensures forall e | e in S :: e >= minSet(S)    

    function getNewBlock(nodeState:NodeState, round:nat): Block
    ensures && getNewBlock(nodeState,round).header.roundNumber == round
            && |validators(nodeState.blockchain + [getNewBlock(nodeState,round)])| > 0
            && getNewBlock(nodeState,round).header.height == |nodeState.blockchain|

    /** =======================================================================
     * GENERAL FUNCTIONS
     *
     * This section defines those functions that, while used as part of the QBFT
     * specification, are general in nature
     ========================================================================*/

    /**
     * @return `true` if and only if the `Optional` value `o` is not empty.
     */
    predicate optionIsPresent<T>(o:Optional<T>)
    {
        o.Optional?
    }

    /**
     * @returns The value carried by the `Optional` value `o'.
     * 
     * @requires The `Optional` value `o` is not empty.
     */
    function optionGet<T>(o:Optional<T>): T
    requires optionIsPresent(o)
    {
        o.value
    } 
 
    /**
     * @returns The union of all sets included in `sets`.
     */
    function setUnionOnSeq<T>(sets:seq<set<T>>):set<T>
    {
        if sets == [] then
            {}
        else
            sets[0] + setUnionOnSeq(sets[1..])
    }             

    /**
     * @returns 2 ^ `exp`.
     */
    function powerOf2(exp:nat):nat
    {
        if exp == 0 then
            1
        else
            2 * powerOf2(exp-1)
    }

    /** =======================================================================
     * QBFT GENERAL FUNCTIONS
     *
     * This section defines those functions that are specific to the QBFT
     * protocol and that are used throughout the specification
     ========================================================================*/  
     
    /**
     * @returns A `RawBlock` equivalent to `Block` `b`.
     */
    function fromBlockToRawBlock(
        b: Block
    ) : RawBlock
    {
       RawBlock(
           RawBlockHeader(
               b.header.proposer,
               b.header.height,
               b.header.timestamp
           ),
           b.body,
           b.transactions
       ) 
    }

    /**
     * @returns A `RawBlockchain` equivalent to `Blockchain` `bc`.
     */
    function fromBlockchainToRawBlockchain(bc:Blockchain): RawBlockchain
    {
        seq(|bc|, (i: nat) requires i < |bc| => fromBlockToRawBlock(bc[i]))
    }

    /**
     * @return The set of nodes, or validators, responsible for deciding on the
     *         block to be appended to the `Blockchain` `blockchain`.
     *
     * @note The definition of this function models the requirement that any two
     *       `Blockchain`s that have the same length where each block in one
     *       blockchain is identical to the block in the other blockchain at the
     *       same position except for the field `commitSeals` evaluate to the
     *       same set of validators. 
     */
    function validators(blockchain:Blockchain): seq<Address>
    {
        validatorsOnRawBlockchain(fromBlockchainToRawBlockchain(blockchain))
    }    

    /**
     * @return `true` if and only if `block` is a valid `Block` for the
     *         `Blockchain` `blockchain`. 
     *
     * @note The definition of this function models the requirement that the
     *       field `commitSeals` of `Block`s does not account when evaluating
     *       block validity from a blockchain application level perspective.
     */
    predicate validateEthereumBlock(blockchain:Blockchain, block:Block)   
    {
        validateRawEthereumBlock(fromBlockchainToRawBlockchain(blockchain), fromBlockToRawBlock(block))
    }

    /**
     * @returns The maximum number of Byzantine validators allowed in a network
     *          of `setSize` validators
     */
    function f(setSize:nat):nat
    {
        if setSize == 0 then
            0
        else
            (setSize - 1) / 3
    }

    /**
     * @returns The minimum size that any two subsets of validators for a
     *          network with `setSize` validators must have to guarantee that
     *          their intersection includes at least one honest validator under
     *          the assumption that no more than `f(setSeize)` validators are
     *          Byzantine.
     */
    function quorum(setSize:nat):nat
    {
        (setSize*2 - 1) / 3 + 1
    }    

    /**
     * @returns The round timeout for round number `round`.
     */
    function roundTimeout(round:nat):nat
    {
        powerOf2(round)
    }    


    /**
     * @returns `block` with `roundNumber` set to `newRound`
     */
    function replaceRoundInBlock(block: Block, newRound: nat): Block
    {
        block.(
            header := block.header.(
                roundNumber := newRound
            )
        )
    }          

    /**
     * @returns The hash of a block identical to `block` except for the field
     *          `commitSeals` which is set to the empty set.
     */
    function hashBlockForCommitSeal(block:Block): Hash
    {
        digest(
            block.(
                header:= block.header.(
                    commitSeals := {})
            )
        )
    }

    /**
     * @returns The identifier of the validator that should propose the block to
     *          be appended to `blockchain` via a Proposal message for round
     *          `ibftRound`.
     */
    function proposer(ibftRound:nat, blockchain:Blockchain): Address
    requires |blockchain|  > 0
    requires |blockchain|  > 1 ==> blockchain[|blockchain|-1].header.proposer in validators(blockchain[..|blockchain|-1])
    requires |validators(blockchain)| > 0
    {
        var roundZeroIndex: nat :=
            if |blockchain| == 1 then
                0
            else
                var previousBlockIndex':nat :| 
                && previousBlockIndex' < |validators(blockchain[..|blockchain|-1])|
                && validators(blockchain[..|blockchain|-1])[previousBlockIndex'] == blockchain[|blockchain|-1].header.proposer;

                previousBlockIndex' + 1
            ;

        validators(blockchain)[
            (roundZeroIndex + ibftRound) % |validators(blockchain)|
        ]
    }

    /**
     * @returns A set of `QbftMessageWithRecipient` with the field `message` set
     *          to the parameter `m` and the field `recipient` set to the
     *          parameter `recipient.
     *
     * @note This function is used in the specification to moel message
     *       multicast.
     */
    function Multicast(recipients:seq<Address>, m:QbftMessage): set<QbftMessageWithRecipient>
    {
        set r | r in recipients :: QbftMessageWithRecipient(m,r)
    }  

    /**
     * @returns An `Optional` datatype representing the digest of the `Optional`
     *          `block` parameter.
     */
    function digestOptionalBlock(block: Optional<Block>): Optional<Hash>
    {
        if optionIsPresent(block) then
            Optional(digest(optionGet(block)))
        else
            Optional.None
    }    

    /** =======================================================================
     * PROPOSAL AND ROUND-CHANGE FUNCTIONS
     *
     * This section defines those functions that are used in the definition of
     * the `UponProposal` and `UponRoundChange` predicates.
     ========================================================================*/   
    /**
     * @returns The set of all Prepare messages included in `current.messagesReceived`.
     */
    function receivedPrepares(current:NodeState): set<QbftMessage>
    {
        set m | 
            && m in current.messagesReceived
            && m.Prepare?            
    }      

    /**
     * @returns The set of signed Prepare payloads included in the set of
     *          Prepare messages `messages`.
     */
    // TBD: Remove precondition?
    function extractSignedPrepares(messages:set<QbftMessage>): set<SignedPrepare>
    requires forall m | m in messages :: m.Prepare?
    {
        set m | m in messages
            ::
                m.preparePayload 
    }    
    
    /**
     * @returns The set of all RoundChange messages included in `current.messagesReceived`.
     */
    function receivedRoundChanges(current:NodeState): set<QbftMessage>
    {
        set m | 
            && m in current.messagesReceived
            && m.RoundChange?
            
    }    
    
    /**
     * @returns The set of signed RoundChange payloads included in messages in
     *          `current.messagesReceived` that have round higher than
     *          `current.round`.
     */
    function receivedSignedRoundChangesForCurrentHeightAndFutureRounds(current:NodeState): set<SignedRoundChange>
    {
        set m | 
            && m in current.messagesReceived
            && m.RoundChange?
            && var uPayload := m.roundChangePayload.unsignedPayload;
            && uPayload.height == |current.blockchain|
            && uPayload.round > current.round         
            ::
                m.roundChangePayload
            
    }    

    /**
     * @returns The set of signed RoundChange payloads included in the set of
     *          RoundChange messages `messages`.
     */
    function extractSignedRoundChanges(messages:set<QbftMessage>): set<SignedRoundChange>
    requires forall m | m in messages :: m.RoundChange?
    {
        set m | m in messages
            ::
                m.roundChangePayload
    }       
 
     /**
      * @returns The set of all node identifiers that have signed one or more
      *          RoundChange messages in `roundChanges`.
      */
    function getSetOfRoundChangeSenders(roundChanges: set<SignedRoundChange>): set<Address>
    {
        set m | m in roundChanges :: recoverSignedRoundChangeAuthor(m)
    }    
    
    /**
     * @returns The set of all blocks included in the set of RoundChange messages `messages`.
     */
    function receivedBlocksInRoundChanges(messages:set<QbftMessage>): set<Block>
    requires forall m | m in messages :: m.RoundChange?
    {
        set m   | 
                    && m in messages
                    && optionIsPresent(m.proposedBlockForNextRound)
                ::
                    optionGet(m.proposedBlockForNextRound)

    }     

    /**
     * @returns `true` if and only if `block` is a valid block for a Proposal
     *          message for round `round`  that does not carry any RoundChange
     *          Justification under the assumption that the current blockchain is
     *          `blockchain`.
     */
    predicate validateNonPreparedBlock(
        block: Block,
        blockchain: Blockchain,
        round: nat
    )
    requires StateBlockchainInvariant(blockchain)
    {
        && validateEthereumBlock(blockchain, block)
        && block.header.proposer == proposer(round, blockchain)
        && |validators(blockchain  + [block])| > 0
    }

    /**
     * @returns `true` if and only if `sPayload` is a valid signed RoundChange
     *          payload for height `height`, round `round` under the assumption
     *          that the current set of validators is `validators`.
     */
    predicate validRoundChange(
        sPayload: SignedRoundChange, 
        height: nat, 
        round: nat,
        validators: seq<Address>)
    {
        var uPayload := sPayload.unsignedPayload;

        && uPayload.height == height
        && uPayload.round == round
        && (if  && !optionIsPresent(uPayload.preparedRound)
                && !optionIsPresent(uPayload.preparedValue)
            then
                true
            else if && optionIsPresent(uPayload.preparedRound)
                    && optionIsPresent(uPayload.preparedValue)
            then
                    optionGet(uPayload.preparedRound) < round
            else
                false)
        && recoverSignedRoundChangeAuthor(sPayload) in validators
    }

    /**
     * @returns `true` if and only if `sPayload` is one of the signed
     *          RoundChange payloads with the highest round in the set
     *          `roundChanges`.
     */
    predicate isHighestPrepared(sPayload:SignedRoundChange, roundChanges:set<SignedRoundChange>)
    {
        &&  optionIsPresent(sPayload.unsignedPayload.preparedRound)
        &&  optionIsPresent(sPayload.unsignedPayload.preparedValue)
        &&  forall m | m in roundChanges ::
                optionIsPresent(m.unsignedPayload.preparedRound) ==>
                    optionGet(m.unsignedPayload.preparedRound) <= optionGet(sPayload.unsignedPayload.preparedRound)
                
    }

    /**
     * @returns `true` if and only if `roundChanges` and `prepares` are,
     *          respectively, valid Proposal and RoundChange justifications for
     *          a Proposal message for height `height`, round `round` including
     *          block `block` undef the following assumptions: (i) the only
     *          possible set of blocks that a node can justify is
     *          `setOfAvailableBlocks`, (ii) the validation function to be used
     *          in the case that `prepares` is empty is `validateBlock`, (iii)
     *          the leader for `round` is `roundLeader` and (iv) the current set
     *          of validators is `validators`.
     */
    predicate isProposalJustification( 
        roundChanges:set<SignedRoundChange>, 
        prepares:set<SignedPrepare>,   
        setOfAvailableBlocks: set<Block>,      
        height: nat,
        round: nat,
        block: Block,
        validateBlock: Block -> bool,
        roundLeader: Address,
        validators:seq<Address>)
    {
        if round == 0 then 
            && validateBlock(block)
            && block.header.roundNumber == 0
            && block.header.height == height
            && block.header.proposer == roundLeader
        else
            && |getSetOfRoundChangeSenders(roundChanges)| >= quorum(|validators|)
            && (forall m | m in roundChanges :: validRoundChange(m,height,round,validators))
            &&  if (forall m | m in roundChanges :: && !optionIsPresent(m.unsignedPayload.preparedRound)
                                                    && !optionIsPresent(m.unsignedPayload.preparedValue))
                then
                    && validateBlock(block)
                    && block.header.roundNumber == round
                    && block.header.height == height
                    && block.header.proposer == roundLeader
                else
                    && block in setOfAvailableBlocks
                    && block.header.roundNumber == round
                    && block.header.height == height
                    && |prepares| >= quorum(|validators|)
                    && exists rcm | rcm in roundChanges ::
                        && isHighestPrepared(rcm,roundChanges)
                        && var proposedBlockWithOldRound := 
                                replaceRoundInBlock(
                                    block,
                                    optionGet(rcm.unsignedPayload.preparedRound)
                                );                        
                        && optionGet(rcm.unsignedPayload.preparedValue) == digest(proposedBlockWithOldRound)
                        && (forall pm | pm in prepares :: 
                                            validSignedPrepareForHeightRoundAndDigest(
                                                pm,
                                                height,
                                                optionGet(rcm.unsignedPayload.preparedRound),
                                                optionGet(rcm.unsignedPayload.preparedValue),
                                                validators
                                            ))
    }

    /**
     * @returns `true` if and only if `m` is a valid Proposal message for a QBFT node with state `current.
     */
    predicate isValidProposal(m:QbftMessage, current:NodeState)
    requires validNodeState(current)
    {
        && m.Proposal?
        && var roundLeader := proposer(m.proposalPayload.unsignedPayload.round,current.blockchain);        
        && m.proposalPayload.unsignedPayload.height == |current.blockchain|
        && recoverSignedProposalAuthor(m.proposalPayload) == roundLeader
        && isProposalJustification(
            m.proposalJustification,
            m.roundChangeJustification,
            {m.proposedBlock},
            |current.blockchain|,
            m.proposalPayload.unsignedPayload.round,
            m.proposedBlock,
            b => validateNonPreparedBlock(b,current.blockchain,m.proposalPayload.unsignedPayload.round),
            roundLeader,
            validators(current.blockchain)
        )
        // NOTE: This check is not required by the QBFT paper as the message structure is a bit different
        && digest(m.proposedBlock) == m.proposalPayload.unsignedPayload.digest
        && (
            || (
                && !optionIsPresent(current.proposalAcceptedForCurrentRound)
                && m.proposalPayload.unsignedPayload.round == current.round
            )
            || (
                && optionIsPresent(current.proposalAcceptedForCurrentRound)
                && m.proposalPayload.unsignedPayload.round > current.round
            )
        )
    }    

    /**
     * @returns `true` if and only if `roundChanges` and `prepares` are,
     *          respectively, valid Proposal and RoundChange justifications for
     *          a Proposal message with round `newRound` including block `block`
     *          under the assumption that the current QBFT node state is
     *          `current`.
     */
    predicate isReceivedProposalJustification(
        roundChanges: set<QbftMessage>,
        prepares: set<QbftMessage>,  
        newRound: nat,
        block: Block,
        current:NodeState)
    requires validNodeState(current)
    {
        && roundChanges <= receivedRoundChanges(current)
        && prepares <= receivedPrepares(current)
        && isProposalJustification(
            extractSignedRoundChanges(roundChanges),
            extractSignedPrepares(prepares),
            receivedBlocksInRoundChanges(roundChanges),
            |current.blockchain|,
            newRound,
            block, 
            b => && b == getNewBlock(current, newRound),
            proposer(newRound,current.blockchain),
            validators(current.blockchain))
        && (
            || (
                && !optionIsPresent(current.proposalAcceptedForCurrentRound)
                && newRound == current.round
            )
            || (
                && optionIsPresent(current.proposalAcceptedForCurrentRound)
                && newRound > current.round
            )
        )
    }     
a
    /**
     * @returns `true` if and only if a QBFT node with state `current` has
     *          received a valid Proposal Justification.
     */
    predicate hasReceivedProposalJustification(current: NodeState)
    requires validNodeState(current)
    {
        exists  
            roundChanges: set<QbftMessage>,
            prepares: set<QbftMessage>,
            newRound: nat,
            block: Block
        ::
            isReceivedProposalJustification(roundChanges, prepares, newRound, block, current)
    }  
      
    /**
     * @returns The RoundChange Justification that a QBFT node with state
     *          `current` has received since adopting its current blockchain, or
     *          the empty set if no Round Change Justification has been received
     *          since.
     */
    function getRoundChangeJustification(current:NodeState): set<SignedPrepare>
    requires validNodeState(current)
    {
        if !optionIsPresent(current.lastPreparedBlock) then
            {}
        else
            var QofP :| 
                && QofP <= validPreparesForHeightRoundAndDigest(
                                    current.messagesReceived,
                                    |current.blockchain|,
                                    optionGet(current.lastPreparedRound),
                                    digest(optionGet(current.lastPreparedBlock)),
                                    validators(current.blockchain))
                && |QofP| >= quorum(|validators(current.blockchain)|);
            
            set m | m in QofP :: m.preparePayload
    } 

    /**
     * @returns The RoundChange message that a QBFT node with state `current`
     *          would send to move to round `newRound`.
     */
    function createRoundChange(
        current: NodeState,
        newRound:nat
        ):
        QbftMessage
    requires validNodeState(current)
    {
        RoundChange(
            signRoundChange(
                UnsignedRoundChange(
                    |current.blockchain|,
                    newRound,
                    digestOptionalBlock(current.lastPreparedBlock),
                    current.lastPreparedRound),
            current.id),
            current.lastPreparedBlock,
            getRoundChangeJustification(current)
        )
    }    

    /** =======================================================================
     * PREPARE VALIDATION FUNCTIONS
     *
     * This section defines those functions that are used to determine whether a
     * Prepare message is valid.
     ========================================================================*/  
    /**
     * @returns `true` if and only if `sPayload` is a valid signed Prepare
     *          payload for height `height`, round `round`, block digest
     *          `digest` under the assumption that the set of validators is
     *          `validators'.
     */
    predicate validSignedPrepareForHeightRoundAndDigest(
        sPayload: SignedPrepare, 
        height:nat, 
        round:nat, 
        digest:Hash,
        validators: seq<Address>
        )
    {
        var uPayload := sPayload.unsignedPayload;
        && uPayload.height == height
        && uPayload.round == round
        && uPayload.digest == digest
        && recoverSignedPrepareAuthor(sPayload) in validators
    }

    /**
     * @returns The set of all valid Prepare messages for height `height, round
     *          `round`, block digest `digest` that are included in the set
     *          `messagesReceived` under the assumption that the set of
     *          validators is `validators`.
     */
    function validPreparesForHeightRoundAndDigest(
        messagesReceived: set<QbftMessage>, 
        height:nat, 
        round:nat, 
        digest:Hash,
        validators: seq<Address>
        ): set<QbftMessage>
    {

        set m  |    && m in messagesReceived
                    && m.Prepare?
                    && validSignedPrepareForHeightRoundAndDigest(
                        m.preparePayload,
                        height,
                        round,
                        digest,
                        validators
                    )
    }  

    /** =======================================================================
     * COMMIT VALIDATION FUNCTIONS
     *
     * This section defines those functions that are used to determine whether a
     * Commit message is valid.
     ========================================================================*/  
    /**
     * @returns `true` if and only if `sPayload` is a valid signed Commit
     *          payload for height `height`, round `round`, block
     *          `proposedBlock` under the assumption that the set of validators
     *          is `validators'.
     */
    predicate validateCommit(commit:SignedCommit, height:nat, round:nat, proposedBlock:Block, validators:seq<Address>)
    {
        var uPayload := commit.unsignedPayload;

        && uPayload.height == height
        && uPayload.round == round
        && uPayload.digest == digest(proposedBlock)
        && recoverSignedHashAuthor(hashBlockForCommitSeal(proposedBlock), uPayload.commitSeal) == recoverSignedCommitAuthor(commit)
        && recoverSignedCommitAuthor(commit) in validators
    }    

    /**
     * @returns The set of all valid Commit messages for height `height, round
     *          `round`, block `proposedBlock` that are included in the set
     *          `messagesReceived` under the assumption that the set of
     *          validators is `validators`.
     */    
    function validCommitsForHeightRoundAndDigest(
        messagesReceived: set<QbftMessage>, 
        height:nat, 
        round:nat, 
        proposedBlock:Block,
        validators: seq<Address>
        ): set<QbftMessage>
    {

        set m  |    && m in messagesReceived
                    && m.Commit?
                    && validateCommit(
                        m.commitPayload,
                        height,
                        round,
                        proposedBlock,
                        validators
                    )
    }    

    /** =======================================================================
     * NEW-BLOCK VALIDATION FUNCTIONS
     *
     * This section defines those functions that are used to determine whether a
     * NewBlock message is valid.
     ========================================================================*/  
    /**
     * @returns `true` if and only if block `block` carries a valid set of
     *          commit seals that justify appending it to blockchain
     *          `blockchain`.
     */
    predicate ValidNewBlock(blockchain:Blockchain, block: Block)
    {
        && block.header.height == |blockchain|
        && |block.header.commitSeals| >= quorum(|validators(blockchain)|)
        && (forall s | s in block.header.commitSeals :: recoverSignedHashAuthor(hashBlockForCommitSeal(block),s) in validators(blockchain))
    } 

    /**
     * @return `true` if and only if `msg` is a NewBlock message including a
     *         block that carries a valid set of commit seals that justify
     *         appending it to blockchain `blockchain`.
     */
    predicate validNewBlockMessage(blockchain: Blockchain, msg:QbftMessage)
    {
        && msg.NewBlock?
        && ValidNewBlock(blockchain, msg.block)
    }                

    /** =======================================================================
     * NON-SPECIFICATION FUNCTIONS
     *
     * This section defines those functions that are used in the specification
     * but that are used for verification purposes and not specification
     * purposes.
     ========================================================================*/  
    predicate validNodeState(nodeState: NodeState)
    {
        && (optionIsPresent(nodeState.proposalAcceptedForCurrentRound) ==> optionGet(nodeState.proposalAcceptedForCurrentRound).Proposal?)
        && (!optionIsPresent(nodeState.lastPreparedRound) <==> !optionIsPresent(nodeState.lastPreparedBlock))
        && (optionIsPresent(nodeState.lastPreparedRound) ==>
                exists QofP ::
                    && QofP <= validPreparesForHeightRoundAndDigest(
                                    nodeState.messagesReceived,
                                    |nodeState.blockchain|,
                                    optionGet(nodeState.lastPreparedRound),
                                    digest(optionGet(nodeState.lastPreparedBlock)),
                                    validators(nodeState.blockchain))
                    && |QofP| >= quorum(|validators(nodeState.blockchain)|) 
            )   
        && StateBlockchainInvariant(nodeState.blockchain)       
    }

    predicate StateBlockchainInvariant(blockchain: Blockchain)
    {
        && |blockchain|  > 0
        && (|blockchain|  > 1 ==> blockchain[|blockchain|-1].header.proposer in validators(blockchain[..|blockchain|-1]))
        && |validators(blockchain)| > 0  
    }             
}