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

module L1_TraceGeneralLemmas {
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_Spec
    import opened L1_Adversary
    import opened HelperLemmasSets
    import opened L1_DistributedSystem
    import opened L1_InstrumentedSpecs
    import opened L1_NetworkingInvariants   
    import opened L1_InstrDSStateInvariantsDefs
    import opened L1_RefinementForMutipleStep
    import opened L1_InstrDSStateInvariantsNew
    import opened L1_AuxFunctionsProof
    import opened EETraceDefs    

    lemma lemmaPredicateThatHoldsForAllTracesExtractedFromValidInstrTracesAlsoHoldsForAValidTrace(
        c: Configuration,
        t: Trace,
        p: Trace -> bool
    )
    requires validTrace(t,c)
    requires forall instrt | validInstrTrace(instrt,c) :: p(extractTraceFromInstrTrace(instrt))
    requires forall t1:Trace, t2:Trace | (forall i :: t1(i) == t2(i)) :: p(t1) <==> p(t2)
    ensures p(t)
    {
        var instrt := fromTraceToInstrTrace(t,c);

        lemmaFieldsPreserveByFromTraceToInstrTrace(t,c);
        lemmaFromTraceToInstrTraceMaintainsValidity(t,c);     

        lemmaExtractTraceFromInstrTraceIsTheInversOfFromTraceToInstrTrace(t,c);   

        assert forall i :: t(i) == extractTraceFromInstrTrace(instrt)(i);

        assert p(t);
    } 

    function fromTraceToInstrTrace(
        t: Trace,
        c: Configuration
    ):  InstrTrace
    requires validTrace(t, c) 
    {
        lemmaShorterSequencesProducedByFromTraceToInstrDSStateSequenceArePrefixOfLongerSequences(t,c);
        
        (i:nat) => fromTraceToInstrDSStateSequence(t,c,i+1)[i]
    }    

    lemma {:fuel fromTraceToInstrDSStateSequence,0,0}  lemmaFromTraceToInstrTraceMaintainsValidity(
        t: Trace,
        c: Configuration
    )
    requires validTrace(t, c)
    ensures var instrt := fromTraceToInstrTrace(t,c); validInstrTrace(instrt, c)        
    {
        lemmaShorterSequencesProducedByFromTraceToInstrDSStateSequenceArePrefixOfLongerSequences(t,c);

        var instrt := fromTraceToInstrTrace(t,c);  
        forall i:nat    
        ensures && validInstrDSState(instrt(i))
                && InstrDSNextMultiple(instrt(i),instrt(i+1))
        {
            var tidss := fromTraceToInstrDSStateSequence(t,c,i+1);
            var tidssip := fromTraceToInstrDSStateSequence(t,c,i+2);
            assert instrt(i) == tidss[i];
            assert instrt(i+1) == tidssip[i+1];
            assert validInstrDSStateSequence(tidss, c);
        }
    }  

    lemma {:fuel fromTraceToInstrDSStateSequence,0,0}  lemmaFieldsPreserveByFromTraceToInstrTrace(
        t: Trace,
        c: Configuration
    )
    requires validTrace(t, c)
    ensures var instrt := fromTraceToInstrTrace(t,c);            
            && (forall j :: && t(j).environment == instrt(j).environment
                            && t(j).configuration == instrt(j).configuration
                            && t(j).adversary == instrt(j).adversary
                            && t(j).nodes.Keys == instrt(j).nodes.Keys
                            && (forall n :: n in instrt(j).nodes.Keys ==> instrt(j).nodes[n].nodeState == t(j).nodes[n])
                )  
    {
        lemmaShorterSequencesProducedByFromTraceToInstrDSStateSequenceArePrefixOfLongerSequences(t,c);

        var instrt := fromTraceToInstrTrace(t,c);  
        forall j:nat 
        ensures && t(j).environment == instrt(j).environment
                && t(j).configuration == instrt(j).configuration
                && t(j).adversary == instrt(j).adversary
                && t(j).nodes.Keys == instrt(j).nodes.Keys
                && (forall n :: n in instrt(j).nodes.Keys ==> instrt(j).nodes[n].nodeState == t(j).nodes[n])
        {
            assert fromTraceToInstrTrace(t,c)(j) == fromTraceToInstrDSStateSequence(t,c,j+1)[j];
            lemmaFieldsPreservedByFromTraceToInstrDSStateSequence(t,c,j);
            lemmaFieldsPreservedByFromTraceToInstrDSStateSequence(t,c,j+1);
        }
    }            

    predicate validInstrDSStateSequence(t:seq<InstrDSState>, configuration: Configuration)
    requires |t| > 0
    {
        && InstrDSInit(t[0],configuration)
        && (
            forall i:nat | i < |t| - 1
                        ::  && validInstrDSState(t[i])
                            && InstrDSNextMultiple(t[i],t[i+1])
        )
    }       

    function fromTraceToInstrDSStateSequenceHelper(
        ins: InstrNodeState,
        messageReceived: set<QbftMessage>,
        ns': NodeState,
        outm: set<QbftMessageWithRecipient>
    ) : InstrNodeState
    requires validNodeState(ins.nodeState)
    requires NodeNext(ins.nodeState, messageReceived, ns', outm )
    ensures var newNodeInstrState := fromTraceToInstrDSStateSequenceHelper(ins, messageReceived, ns', outm);
            && InstrNodeNextMultiple(ins,messageReceived,newNodeInstrState,outm)
            && newNodeInstrState.nodeState == ns'
    
    {
            var newMessagesReceived := ins.nodeState.messagesReceived + messageReceived;
            var currentWithNewMessagesReceived :=
                    ins.nodeState.(
                        messagesReceived := newMessagesReceived,
                        localTime := ins.nodeState.localTime + 1
                    );                         
            var s:seq<NodeState>, o:seq<set<QbftMessageWithRecipient>> :|
                && |s| >= 2
                && |o| == |s| - 1
                && s[0] == currentWithNewMessagesReceived
                && s[|s|-1] == ns'
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
                && outm == setUnionOnSeq(o);     
            var seqProposalsAccepted := seq(
                |s|-1 ,
                (i:nat) requires i + 1 < |s| =>
                    getSingletonOfAcceptedProposals(s[i+1])
            );                                               
            // NOTE: THe last parameter must be fixed due to the addition of fields to InstrNodeState
            var newNodeInstrState := InstrNodeState(
                ns',
                ins.proposalsAccepted + setUnionOnSeq(seqProposalsAccepted),
                ins.messagesSent + multiset(outm),
                ins.messagesSentToItself + (ns'.messagesReceived - messageReceived - ins.nodeState.messagesReceived)
            );  
            
            assert InstrNodeNextMultipleHelper(ins,messageReceived,newNodeInstrState,outm);
            assert InstrNodeNextMultiple(ins,messageReceived,newNodeInstrState,outm);
            newNodeInstrState

    }


    // 174s 3.3.0
    function fromTraceToInstrDSStateSequence(
        t: Trace,
        c: Configuration,
        i: nat
    ):   seq<InstrDSState>
    requires validTrace(t, c)
    ensures |fromTraceToInstrDSStateSequence(t,c,i)|  == i + 1
    ensures var ret :=  fromTraceToInstrDSStateSequence(t,c,i);
                && ret[i].nodes.Keys == t(i).nodes.Keys
                && ret[i].adversary == t(i).adversary
                && ret[i].environment == t(i).environment
                && ret[i].configuration == t(i).configuration
                && (forall n | n in ret[i].nodes.Keys :: ret[i].nodes[n].nodeState == t(i).nodes[n])                 
    ensures validInstrDSStateSequence(fromTraceToInstrDSStateSequence(t,c,i), c)
    {
       
        lemmaConstantFieldsInTrace(t,c);

        if i == 0 then
            var r :=
            [InstrDSState(
                t(0).configuration,
                t(0).environment,
                map a | a in t(0).nodes :: 
                    InstrNodeState(
                        t(0).nodes[a],
                        {},
                        multiset{},
                        {}
                    ),
                t(0).adversary
            )];
            // assert forall n | n in r[i].nodes.Keys :: r[i].nodes[n].nodeState == t(i).nodes[n];
            assert validInstrDSStateSequence(r, c);
            r
           
        else
            var instrtim1 := fromTraceToInstrDSStateSequence(t,c,i-1);

            if t(i-1) == t(i) then
                var ret :=
                instrtim1 +
                [instrtim1[|instrtim1|-1]];
                assert InstrDSNextMultiple(ret[i-1], ret[i]);
                assert validInstrDSStateSequence(ret, c);
                ret               
            else
                var inm, outm, node :| DSNextNode(t(i-1),t(i),outm, inm, node);

                var messageReceived := set mr:QbftMessageWithRecipient | mr in inm :: mr.message;            
                var rr :=
                    if isHonest(t(i-1),node)  then 

                        map a | a in instrtim1[i-1].nodes ::
                            if a == node then 
                                    fromTraceToInstrDSStateSequenceHelper(instrtim1[i-1].nodes[node], messageReceived, t(i).nodes[node], outm)
                                else
                                    instrtim1[i-1].nodes[a]
                    else
                        instrtim1[i-1].nodes;


                var ret := instrtim1 +
                [InstrDSState(
                    t(i).configuration,
                    t(i).environment,

                            rr
                        ,
                    t(i).adversary
                )];
                assert !isHonest(t(i-1),node) ==> AdversaryNext(instrtim1[i-1].adversary,messageReceived, ret[i].adversary,outm);
                assert !isHonest(t(i-1),node) ==> ret[i-1].nodes == ret[i].nodes;
                assert isHonest(t(i-1),node) ==> DSInstrNextNodeMultiple(instrtim1[i-1], ret[i], outm, inm, node);
                assert DSInstrNextNodeMultiple(instrtim1[i-1], ret[i], outm, inm, node);

                assert InstrDSNextMultiple(instrtim1[i-1], ret[i]);
                assert InstrDSNextMultiple(ret[i-1], ret[i]);
                assert validInstrDSStateSequence(ret, c);
                ret
    }      

    lemma lemmaShorterSequencesProducedByFromTraceToInstrDSStateSequenceArePrefixOfLongerSequencesHelper(
        t: Trace,
        c: Configuration,
        i: nat,
        j: nat
    )
    requires validTrace(t, c)
    requires i <= j
    ensures fromTraceToInstrDSStateSequence(t,c,i) <= fromTraceToInstrDSStateSequence(t,c,j)
    {
        if i < j 
        {
            calc <= {
                fromTraceToInstrDSStateSequence(t,c,i);
                fromTraceToInstrDSStateSequence(t,c,j-1);
                fromTraceToInstrDSStateSequence(t,c,j);
            }
        }
    
    }

    lemma lemmaShorterSequencesProducedByFromTraceToInstrDSStateSequenceArePrefixOfLongerSequences(
        t: Trace,
        c: Configuration
    )
    requires validTrace(t, c)
    ensures forall i,j | 0 <= i <= j :: fromTraceToInstrDSStateSequence(t,c,i) <= fromTraceToInstrDSStateSequence(t,c,j)
    {
        forall i,j | 0 <= i <= j 
        ensures fromTraceToInstrDSStateSequence(t,c,i) <= fromTraceToInstrDSStateSequence(t,c,j) {
            lemmaShorterSequencesProducedByFromTraceToInstrDSStateSequenceArePrefixOfLongerSequencesHelper(t, c, i, j);
        }
    }

    lemma lemmaFieldsPreservedByFromTraceToInstrDSStateSequence(
        t: Trace,
        c: Configuration,
        i: nat
    )   
    requires validTrace(t, c)  
    ensures var instrt := fromTraceToInstrDSStateSequence(t,c,i); 
            forall j | 0 <= j <= i::
            && t(j).nodes.Keys == instrt[j].nodes.Keys
            && t(j).configuration == instrt[j].configuration
            && t(j).adversary == instrt[j].adversary
            && t(j).environment == instrt[j].environment
            && (forall n :: n in instrt[j].nodes.Keys ==> instrt[j].nodes[n].nodeState == t(j).nodes[n])
    {  }    

    lemma {:fuel fromTraceToInstrTrace,0,0} lemmaExtractTraceFromInstrTraceIsTheInversOfFromTraceToInstrTrace(
        t: Trace,
        c: Configuration
    )
    requires validTrace(t, c)
    ensures forall i :: extractTraceFromInstrTrace(fromTraceToInstrTrace(t,c))(i) == t(i) 
    {
        var instrt := fromTraceToInstrTrace(t,c);

        lemmaFieldsPreserveByFromTraceToInstrTrace(t,c);
        lemmaFromTraceToInstrTraceMaintainsValidity(t,c);

        assert validInstrTrace(instrt, c);

        assert  
            && (forall j :: t(j).nodes.Keys == instrt(j).nodes.Keys);

        
        assert
            && (forall j,n :: n in instrt(j).nodes.Keys ==> instrt(j).nodes[n].nodeState == t(j).nodes[n]);
        assert
            && (forall j :: && t(j).environment == instrt(j).environment
                            && t(j).configuration == instrt(j).configuration
                            && t(j).adversary == instrt(j).adversary);   


        var i:nat;

        var extrt := extractTraceFromInstrTrace(fromTraceToInstrTrace(t,c));

        assert extrt(i).configuration == instrt(i).configuration == t(i).configuration;
        assert extrt(i).environment == instrt(i).environment == t(i).environment;
        assert extrt(i).adversary == instrt(i).adversary == t(i).adversary;
        assert extrt(i).nodes == t(i).nodes;    


        assert forall i :: extrt(i) == t(i);

        // assert extrt  == t;

        // assert extractTraceFromInstrTrace(fromTraceToInstrTrace(t,c)) == t ;     

    }  

    lemma lemmaConstantFieldsInTrace(t:Trace, c: Configuration)
    requires validTrace(t,c)
    ensures forall i,j :: t(i).nodes.Keys == t(j).nodes.Keys
    ensures forall i,j :: t(i).adversary.byz == t(j).adversary.byz
    {
        lemmaConstantNextImpliesAlwaysConstant(t,c, (s:DSState) => s.nodes.Keys);
        lemmaConstantNextImpliesAlwaysConstant(t,c, (s:DSState) => s.adversary.byz);
    }    

    lemma lemmaConstantNextImpliesAlwaysConstant<T>(t:Trace, c: Configuration, f:DSState -> T)
    requires validTrace(t,c)
    requires forall s,s' | validDSState(s) :: DSNext(s,s') ==> f(s) == f(s')
    ensures forall i:nat :: f(t(i)) == f(t(0))
    ensures forall i:nat, j:nat :: f(t(i)) == f(t(j))
    {
        forall i:nat
        ensures f(t(i)) == f(t(0))
        {
            lemmaConstantNextImpliesAlwaysConstantHelper(t,c,f,i);
        }
    }    

    lemma lemmaConstantNextImpliesAlwaysConstantHelper<T>(t:Trace, c: Configuration, f:DSState -> T, i:nat)
    requires validTrace(t,c)
    requires forall s,s' | validDSState(s) :: DSNext(s,s') ==> f(s) == f(s')
    ensures f(t(i)) == f(t(0))
    ensures forall j | 0 <= j <= i :: f(t(i)) == f(t(j))
    {
        if i == 0 
        {

        }
        else
        {
            lemmaConstantNextImpliesAlwaysConstantHelper(t,c,f,i-1);
        }
    }    
}