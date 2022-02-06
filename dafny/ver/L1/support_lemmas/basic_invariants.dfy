include "../../../spec/L1/types.dfy"
include "../distr_system_spec/common_functions.dfy"
include "../distr_system_spec/network.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"
include "../../../spec/L1/node.dfy"
include "../distr_system_spec/distributed_system.dfy"
include "../../common/sets.dfy"
include "instrumented_specs.dfy"

module EEAAuxBasicInvariantsProof
{
    import opened EEASpecTypes
    import opened EEASpecNetwork
    import opened EEAAuxiliaryFunctionsAndLemmas
    import opened EEACommonFunctions
    import opened EEASpec
    import opened HelperLemmasSets
    import opened EEADistributedSystem
    import opened EEAInstrumentedSpecs  

    predicate invNodesIdMatchesMapKey(s:InstrDSState)
    {
        forall n | isInstrNodeHonest(s,n) :: s.nodes[n].nodeState.id == n
    }  

    predicate invEnvMessagesSentYetToBeReceivedIsASubsetOfAllMessagesSent(
        s:InstrDSState
    )
    {
        && s.environment.messagesSentYetToBeReceived <= s.environment.allMessagesSent
        // && (forall a :: a in s.environment.allMessagesSentTo.Keys <==> a in s.environment.nodes)
    }

    lemma lemmaInvEnvMessagesSentYetToBeReceivedIsASubsetOfAllMessagesSent(
        s:InstrDSState, 
        s': InstrDSState
    )    
    requires validInstrDSState(s)
    requires invEnvMessagesSentYetToBeReceivedIsASubsetOfAllMessagesSent(s)
    requires InstrDSNextSingle(s, s')
    ensures invEnvMessagesSentYetToBeReceivedIsASubsetOfAllMessagesSent(s')
    {

    }        

    predicate invConstantFields(s:InstrDSState)
    {
        && invNodesIdMatchesMapKey(s)
        && |s.adversary.byz| <= f(|validators([s.configuration.genesisBlock])|)
        && s.nodes.Keys == seqToSet(s.configuration.nodes)
        && seqToSet(validators([s.configuration.genesisBlock])) <= seqToSet(s.configuration.nodes)
        && isUniqueSequence(validators([s.configuration.genesisBlock]))
    }

    lemma lemmaInvConstantFields(
        s:InstrDSState, 
        s': InstrDSState
    )
    requires validInstrDSState(s)
    requires invConstantFields(s)
    requires InstrDSNextSingle(s, s')
    ensures invConstantFields(s')    
    {

    }

    lemma lemmaInvConstantFieldsInit(
        s: InstrDSState,
        c: Configuration
    )
    requires InstrDSInit(s,c)
    ensures invConstantFields(s)    
    {

    }



}