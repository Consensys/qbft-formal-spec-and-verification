include "../../../spec/L1/types.dfy"
include "../distr_system_spec/network.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"
include "../../../spec/L1/node.dfy"
include "../distr_system_spec/distributed_system.dfy"
include "../../common/sets.dfy"

module EEAAxioms
{
    import opened EEASpecTypes
    import opened EEASpecNetwork
    import opened EEAAuxiliaryFunctionsAndLemmas
    import opened EEASpec
    import opened HelperLemmasSets
    import opened EEADistributedSystem

    lemma {:axiom} axiomRawValidatorsNeverChange()
    ensures forall b1, b2 :: validatorsOnRawBlockchain(b1) == validatorsOnRawBlockchain(b2)                           

}