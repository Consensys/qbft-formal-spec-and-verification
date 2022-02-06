include "../../../spec/L1/types.dfy"
include "../distr_system_spec/network.dfy"
include "../distr_system_spec/adversary.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"
include "../../../spec/L1/node.dfy"
include "../distr_system_spec/distributed_system.dfy"
include "../../common/sets.dfy"
include "instrumented_specs.dfy"
include "networking_invariants.dfy"
include "instr_dsstate_multiple_invariants.dfy"
include "instr_dsstate_invariants_defs.dfy"
include "instr_dsstate_invariants_2.dfy"
include "trace_proofs_helpers.dfy"
include "aux_functions.dfy"
include "trace_defs.dfy"
include "trace_general_lemmas.dfy"
include "../theorems_defs.dfy"


// TODO: Change module name
module EETraceProofs {
    import opened EEASpecTypes
    import opened EEASpecNetwork
    import opened EEAAuxiliaryFunctionsAndLemmas
    import opened EEASpec
    import opened EEAAdversary
    import opened HelperLemmasSets
    import opened EEADistributedSystem
    import opened EEAInstrumentedSpecs
    import opened EEANetworkingInvariants   
    import opened EEAInstrDSStateInvariants
    import opened EEARefinementForMutipleStep
    import opened EEAInstrDSStateInvariantsNew
    import opened EEATraceProofsHelpers
    import opened EEAAuxFunctionsProof
    import opened EETraceDefs
    import opened EEATraceGeneralLemmas    
    import opened EEATheoremsDefs

    predicate consistencyAndStabilityInstrTrace(t: InstrTrace)
    {
        forall i,j,n1,n2 |
                            && isInstrNodeHonest(t(i),n1)
                            && isInstrNodeHonest(t(j),n2)
                        ::
                        && consistentBlockchains(t(i).nodes[n1].nodeState.blockchain, t(j).nodes[n2].nodeState.blockchain)
    }

    predicate consistencyInstrTrace(t: InstrTrace)
    {
        forall i,n1,n2 |
                    && isInstrNodeHonest(t(i),n1)
                    && isInstrNodeHonest(t(i),n2)
                ::
                consistentBlockchains(t(i).nodes[n1].nodeState.blockchain, t(i).nodes[n2].nodeState.blockchain)
    }

      

    lemma lemmaConsistencyInstrTrace(
        t: InstrTrace,
        c: Configuration
    )
    requires validInstrTrace(t,c)
    ensures consistencyInstrTrace(t)
    {
        lemmaIndInvForBlockchainConsistencyHoldsInAnyStateOfAValidInstrTrace(t,c);
        reveal_indInvForBlockchainConsistency();

        forall i,n1,n2 |
            && isInstrNodeHonest(t(i),n1)
            && isInstrNodeHonest(t(i),n2)
        ensures consistentBlockchains(t(i).nodes[n1].nodeState.blockchain, t(i).nodes[n2].nodeState.blockchain);
        {
            assert indInvForBlockchainConsistency(t(i));
            assert invBlockchainConsistency((t(i)));
            assert consistentBlockchains(t(i).nodes[n1].nodeState.blockchain, t(i).nodes[n2].nodeState.blockchain);
        }
    }




    lemma lemmaConsistencyAndStabilityInstr(
        t: InstrTrace,
        c: Configuration
    )
    requires validInstrTrace(t,c)
    ensures consistencyAndStabilityInstrTrace(t)
    {
        lemmaConsistentBlockchainIsSymmetric();
        forall i:nat,j:nat,n1,n2 |
                    && isInstrNodeHonest(t(i),n1)
                    && isInstrNodeHonest(t(j),n2)
        ensures        
                        && consistentBlockchains(t(i).nodes[n1].nodeState.blockchain, t(j).nodes[n2].nodeState.blockchain)
        {
            if i <= j 
            {
                lemmaConsistencyAndStabilityInstrHelper(t, c, i, j, n1, n2);
            }
            else
            {
                lemmaConsistencyAndStabilityInstrHelper(t, c, j, i, n2, n1);
            }
            
        }
    }

                   

}