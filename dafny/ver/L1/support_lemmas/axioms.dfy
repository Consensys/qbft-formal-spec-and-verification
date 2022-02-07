include "../../../spec/L1/types.dfy"
include "../distr_system_spec/network.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"
include "../../../spec/L1/node.dfy"
include "../distr_system_spec/distributed_system.dfy"
include "../../common/sets.dfy"

module L1_Axioms
{
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_Spec
    import opened HelperLemmasSets
    import opened L1_DistributedSystem

    lemma {:axiom} axiomRawValidatorsNeverChange()
    ensures forall b1, b2 :: validatorsOnRawBlockchain(b1) == validatorsOnRawBlockchain(b2)                           

}