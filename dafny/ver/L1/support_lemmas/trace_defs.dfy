include "../../../spec/L1/types.dfy"
include "../distr_system_spec/distributed_system.dfy"
include "instrumented_specs.dfy"

module EETraceDefs {
    import opened L1_SpecTypes
    import opened L1_DistributedSystem
    import opened L1_InstrumentedSpecs   

    type Trace = nat -> DSState

    type InstrTrace = nat -> InstrDSState

    predicate validTrace(t:Trace, configuration: Configuration)
    {
        && DSInit(t(0),configuration)
        && (
            forall i:nat :: && validDSState(t(i))
                            && DSNext(t(i),t(i+1))
        )
    }   

    predicate validInstrTrace(t:InstrTrace, configuration: Configuration)
    {
        && InstrDSInit(t(0),configuration)
        && (
            forall i:nat :: && validInstrDSState(t(i))
                            && InstrDSNextMultiple(t(i),t(i+1))
        )
    }      


    function extractTraceFromInstrTrace(instrt: InstrTrace): Trace
    {
        (i:nat) => 
            var ns := instrt(i).nodes;
            DSState(
                    instrt(i).configuration,
                    instrt(i).environment,
                    map a | a in instrt(i).nodes :: instrt(i).nodes[a].nodeState,
                    instrt(i).adversary
            )
    }      
}