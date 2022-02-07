include "../../spec/L1/types.dfy"
include "distr_system_spec/distributed_system.dfy"
include "support_lemmas/aux_functions.dfy"
include "support_lemmas/trace_defs.dfy"
include "support_lemmas/trace_instrumented_lemmas.dfy"
include "support_lemmas/trace_general_lemmas.dfy"
include "theorems_defs.dfy"


module L1_Theorems {
    import opened L1_SpecTypes
    import opened L1_DistributedSystem
    import opened L1_AuxFunctionsProof
    import opened EETraceDefs
    import opened L1_TraceInstrumentedLemmas
    import opened L1_TraceGeneralLemmas    
    import opened L1_TheoremsDefs


    predicate consistency(t: Trace)
    {
        forall i,n1,n2 |
                    && isHonest(t(i),n1)
                    && isHonest(t(i),n2)
                ::
                consistentBlockchains(t(i).nodes[n1].blockchain, t(i).nodes[n2].blockchain)
    }  

    predicate consistencyAndStability(t: Trace)
    {
        forall i,j,n1,n2 |
                            && isHonest(t(i),n1)
                            && isHonest(t(j),n2)
                        ::
                        && consistentBlockchains(t(i).nodes[n1].blockchain, t(j).nodes[n2].blockchain)

    }    

    lemma lemmaInvBlockchainConsistency(
        t: Trace,
        c: Configuration
    )
    requires validTrace(t,c)
    ensures consistency(t)
    {
        forall instrt | validInstrTrace(instrt,c)
        ensures consistency(extractTraceFromInstrTrace(instrt))
        {
            lemmaConsistencyInstrTrace(instrt, c);
        }
        lemmaPredicateThatHoldsForAllTracesExtractedFromValidInstrTracesAlsoHoldsForAValidTrace(c,t,consistency);        
    }      

    lemma lemmaConsistencyAndStability(
        t: Trace,
        c: Configuration
    )
    requires validTrace(t, c)
    ensures consistencyAndStability(t)
    {
        forall instrt | validInstrTrace(instrt,c)
        ensures consistencyAndStability(extractTraceFromInstrTrace(instrt))
        {
            lemmaConsistencyAndStabilityInstr(instrt, c);
        }
        lemmaPredicateThatHoldsForAllTracesExtractedFromValidInstrTracesAlsoHoldsForAValidTrace(c,t,consistencyAndStability);
    }  

}