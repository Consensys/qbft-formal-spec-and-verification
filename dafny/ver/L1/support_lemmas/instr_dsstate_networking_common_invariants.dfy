include "../../../spec/L1/types.dfy"
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
include "instr_node_state_invariants.dfy"
// include "quorum.dfy"
// include "general_lemmas.dfy"

module EEAInstrDSStateNetworkingCommonInvariants
{
    import opened EEASpecTypes
    import opened EEASpecNetwork
    import opened EEAAuxiliaryFunctionsAndLemmas
    import opened EEASpec
    import opened HelperLemmasSets
    import opened EEADistributedSystem
    import opened EEAInstrumentedSpecs
    import opened EEAAxioms
    import opened EEAAuxFunctionsProof
    import opened EEAAuxBasicInvariantsProof
    import opened EEAInstrNodeStateInvariants

    predicate validInstrDSStateEx(s:InstrDSState)
    {
        forall ns | isInstrNodeHonest(s,ns) :: validInstrStateEx(s.nodes[ns])
    }  
  
    function liftIndInvInstrNodeStateToInstrDSState(
        p: InstrNodeState -> bool
    ): InstrDSState -> bool
    {
        (s:InstrDSState) =>
            forall n | isInstrNodeHonest(s,n) :: p(s.nodes[n])
    }


    lemma lemmaIndInvInstrNodeStateLifterToInstrDSState(
        s:  InstrDSState, 
        s': InstrDSState
    )    
    requires validInstrDSStateEx(s) 
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires InstrDSNextSingle(s,s')  
    ensures liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s')
    {
        if s != s'
        {
            var node :| isNodeThatTakesStep(s, s', node);

            if isInstrNodeHonest(s,node)
            {
                var inm, outm :| InstrNodeNextSingleStep(s.nodes[node],inm,s'.nodes[node],outm);
                lemmaIndInvInstrNodeState(s.nodes[node],inm,s'.nodes[node],outm);
            }
        }        
    }
}