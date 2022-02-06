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
include "aux_functions.dfy"
include "trace_defs.dfy"
include "trace_general_lemmas.dfy"
include "../theorems_defs.dfy"


module EEATraceProofsHelpers {
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
    import opened EEAAuxFunctionsProof
    import opened EETraceDefs
    import opened EEATraceGeneralLemmas
    import opened EEATheoremsDefs


    lemma lemmaIndInvForBlockchainConsistencyHoldsInAnyStateOfAValidInstrTraceHelper(
        t: InstrTrace,
        c: Configuration,
        i: nat
    )
    requires validInstrTrace(t, c)
    ensures forall j | 0 <= j <= i :: indInvForBlockchainConsistency(t(j))
    {
        if i == 0
        {
            assert InstrDSInit(t(0), c);
            lemmaIndPredNonOpaqueIsTrueInInit(t(0), c);
            assert indInvForBlockchainConsistency(t(0));
        }
        else
        {
            lemmaIndInvForBlockchainConsistencyHoldsInAnyStateOfAValidInstrTraceHelper(t, c, i-1);
            lemmaInstrDSNextMultipleIndInvForBlockchainConsistency(t(i-1), t(i));
        }
    }

    lemma lemmaIndInvForBlockchainConsistencyHoldsInAnyStateOfAValidInstrTrace(
        t: InstrTrace,
        c: Configuration
    )
    requires validInstrTrace(t, c)
    ensures forall i: nat :: indInvForBlockchainConsistency(t(i))
    {
        forall i:nat 
        ensures indInvForBlockchainConsistency(t(i))
        {
            lemmaIndInvForBlockchainConsistencyHoldsInAnyStateOfAValidInstrTraceHelper(t,c,i);
        }
    }    


    lemma lemmaStabilityInstr1Helper(
        t: InstrTrace,
        c: Configuration,
        n: Address,
        i: nat,
        j: nat
    )
    requires validInstrTrace(t, c)
    requires i <= j 
    // requires isInstrNodeHonest(t(i), n)
    requires isInstrNodeHonest(t(j), n)
    ensures n in t(i).nodes
    ensures isInstrNodeHonest(t(i), n)    
    ensures t(i).nodes[n].nodeState.blockchain <=  t(j).nodes[n].nodeState.blockchain
    {
        if i == j 
        {
            assert t(i).nodes[n].nodeState.blockchain <=  t(j).nodes[n].nodeState.blockchain;
        }
        else
        {
            lemmaInstrDSStateStabilityMultiStep(t(j-1), t(j));
            lemmaStabilityInstr1Helper(t, c, n, i, j-1);
        }
    }

    lemma lemmaStabilityInstr1Helper2(
        t: InstrTrace,
        c: Configuration,
        n: Address,
        i: nat,
        j: nat
    )
    requires validInstrTrace(t, c)
    requires i <= j 
    requires isInstrNodeHonest(t(i), n)
    ensures isInstrNodeHonest(t(j), n)    
    {
        if i != j 
        {
            lemmaStabilityInstr1Helper2(t, c, n, i, j-1);
        }
    }    

    lemma lemmaConsistencyAndStabilityInstrHelper(
        t: InstrTrace,
        c: Configuration,
        i: nat,
        j: nat,
        n1: Address,
        n2: Address
    )
    requires validInstrTrace(t,c)
    requires    && i <= j
                && isInstrNodeHonest(t(i),n1)
                && isInstrNodeHonest(t(j),n2)
    ensures consistentBlockchains(t(i).nodes[n1].nodeState.blockchain, t(j).nodes[n2].nodeState.blockchain);
    {
        lemmaIndInvForBlockchainConsistencyHoldsInAnyStateOfAValidInstrTrace(t,c);
        reveal_indInvForBlockchainConsistency();            
        lemmaStabilityInstr1Helper2(t,c, n1,i,j);
        lemmaStabilityInstr1Helper(t,c,n1,i,j);

        // lemmaStabilityInstr1Helper(t,c,n2,i,j);
        assert t(i).nodes[n1].nodeState.blockchain <=  t(j).nodes[n1].nodeState.blockchain;
        assert consistentBlockchains(t(i).nodes[n1].nodeState.blockchain,  t(j).nodes[n1].nodeState.blockchain);
        assert indInvForBlockchainConsistency(t(j));
        assert invBlockchainConsistency((t(j)));
        assert consistentBlockchains(t(j).nodes[n1].nodeState.blockchain, t(j).nodes[n2].nodeState.blockchain);
        assert consistentBlockchains(t(i).nodes[n1].nodeState.blockchain, t(j).nodes[n2].nodeState.blockchain);
    }    

}