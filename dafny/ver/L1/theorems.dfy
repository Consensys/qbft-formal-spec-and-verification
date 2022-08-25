include "../../spec/L1/types.dfy"
include "distr_system_spec/distributed_system.dfy"
include "support_lemmas/aux_functions.dfy"
include "support_lemmas/trace_defs.dfy"
include "support_lemmas/trace_instrumented_lemmas.dfy"
include "support_lemmas/trace_general_lemmas.dfy"
include "theorems_defs.dfy"
include "../../spec/L1/node_auxiliary_functions.dfy"
include "distr_system_spec/common_functions.dfy"


module L1_Theorems {
    import opened L1_SpecTypes
    import opened L1_DistributedSystem
    import opened L1_AuxFunctionsProof
    import opened EETraceDefs
    import opened L1_TraceInstrumentedLemmas
    import opened L1_TraceGeneralLemmas    
    import opened L1_TheoremsDefs
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_CommonFunctions



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

    predicate pNodeStepIndexIsWithinBounds(
        seqNodes: iseq<Address>,
        n: Address,
        i: nat
    )
    {
        &&  if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n) then
                i <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1
            else 
                true
    }

    lemma lemmaAHelper(
        bc1: Blockchain,
        bc2: Blockchain,
        bc3: Blockchain,
        bc4: Blockchain
    )
    requires consistentBlockchains(bc1, bc2)
    requires bc1 == bc3 || bc3 == bc1 
    requires bc2 == bc4 || bc4 == bc2 
    ensures consistentBlockchains(bc3, bc4)
    {  }


    lemma lemmaAHelper2(
        dsBehaviour: DSBehaviour,
        dsStates: iseq<DSState>,
        seqNodes: iseq<Address>,
        blockchainSeqs: map<Address, iseq<Blockchain>>,
        i: nat,
        n1: Address

    ) returns (inv1: nat)
    requires n1 in blockchainSeqs
    requires n1 in dsBehaviour.nodesBehaviours
    requires blockchainSeqs == getBlockchainsSeq(dsBehaviour);
    requires pNodeStepIndexIsWithinBounds(seqNodes, n1, i)
    requires forall n | n in dsBehaviour.nodesBehaviours.Keys ::
            if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n) then
                forall i: nat | i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n).1 :: pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i) 
            else
                forall i: nat :: pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n, seqNodes, dsStates, i) 
    requires forall i: nat :: dsBehaviour.nodesBehaviours.Keys <= dsStates[i].nodes.Keys                
    requires forall n | n in dsBehaviour.nodesBehaviours.Keys  ::
        (dsStates[0].nodes[n].blockchain == dsBehaviour.nodesBehaviours[n].initialBlockchain)      
    ensures blockchainSeqs[n1][i] == dsStates[inv1].nodes[n1].blockchain;                  
    {
        // var inv1: nat;
        if i > 0 
        {
            var prevI: nat := i - 1;
            if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n1) 
            {
                assert prevI + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n1).1;
                assert pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n1, seqNodes, dsStates, prevI);
            }
            else
            {
                assert pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n1, seqNodes, dsStates, prevI);
            }

            inv1 := getStepsTakeByNodeSoFarReverse(seqNodes, n1, prevI + 1);
            assert dsBehaviour.nodesBehaviours[n1].steps[prevI].newBlockchain == dsStates[inv1].nodes[n1].blockchain;         

            // assert blockchainSeqs[n1][i] == dsBehaviour.nodesBehaviours[n1].steps[i-1].newBlockchain; //
            
            // assert blockchainSeqs[n1][i] == dsStates[inv1].nodes[n1].blockchain;

            lemmaGetBlockchainsSeq2(dsBehaviour, blockchainSeqs, n1, i);

            calc == {
                blockchainSeqs[n1][i];
                dsBehaviour.nodesBehaviours[n1].steps[i-1].newBlockchain;
                calc == {
                    i - 1;
                    prevI;
                }
                dsBehaviour.nodesBehaviours[n1].steps[prevI].newBlockchain;
                dsStates[inv1].nodes[n1].blockchain;
            }

            assert blockchainSeqs[n1][i] == dsStates[inv1].nodes[n1].blockchain;

         
        }
        else 
        {
            inv1 := 0;
            assert blockchainSeqs[n1][i] == dsStates[inv1].nodes[n1].blockchain;
        }
        // assert blockchainSeqs[n1][i] == dsStates[inv1].nodes[n1].blockchain;        
    }

    function getBlockchainsSeq(
        dsBehaviour: DSBehaviour
    ): (ret: map<Address, iseq<Blockchain>>)
    {
        var ret := map n: Address | 
            && n in dsBehaviour.nodesBehaviours.Keys
            ::
            (imap i: nat :: 
                if i == 0 then
                    dsBehaviour.nodesBehaviours[n].initialBlockchain
                else
                    dsBehaviour.nodesBehaviours[n].steps[i-1].newBlockchain
            );
        assert forall n | n in ret :: forall i:nat :: i in ret[n];
        ret
    }

    lemma lemmaGetBlockchainsSeq(
        dsBehaviour: DSBehaviour,
        blockchainSeqs: map<Address, iseq<Blockchain>>
    )
    requires blockchainSeqs == getBlockchainsSeq(dsBehaviour);
    ensures blockchainSeqs.Keys == dsBehaviour.nodesBehaviours.Keys
    ensures forall n, i:nat | n in dsBehaviour.nodesBehaviours.Keys && i > 0:: blockchainSeqs[n][i] == dsBehaviour.nodesBehaviours[n].steps[i-1].newBlockchain
    {

    }


    lemma lemmaGetBlockchainsSeq2(
        dsBehaviour: DSBehaviour,
        blockchainSeqs: map<Address, iseq<Blockchain>>,
        n: Address,
        i: nat
    )
    requires blockchainSeqs == getBlockchainsSeq(dsBehaviour);
    requires i > 0
    requires n in dsBehaviour.nodesBehaviours.Keys 
    ensures blockchainSeqs.Keys == dsBehaviour.nodesBehaviours.Keys
    ensures blockchainSeqs[n][i] == dsBehaviour.nodesBehaviours[n].steps[i-1].newBlockchain
    {
        lemmaGetBlockchainsSeq(dsBehaviour, blockchainSeqs);
    }    

    predicate consistencyAndStability2(
        dsBehaviour: DSBehaviour,
        configuration: Configuration
    )
    requires IsValidConfiguration(configuration)
    requires dsBehaviour in DSSpecificationBuilder(configuration).behaviours
    requires  |validators([configuration.genesisBlock])| > 0        
    {
        var blockchainSeqs := getBlockchainsSeq(dsBehaviour); 
        var allNodes := seqToSet(configuration.nodes);
        forall seqNodes, i:nat, j:nat, n1, n2 |
                    && pLemmajkfladjklfaGetSeqNodes(dsBehaviour, allNodes, seqNodes)
                    && n1 in dsBehaviour.nodesBehaviours.Keys
                    && n2 in dsBehaviour.nodesBehaviours.Keys
                    && pNodeStepIndexIsWithinBounds(seqNodes, n1, i)
                    && pNodeStepIndexIsWithinBounds(seqNodes, n2, j)
            ::
                consistentBlockchains(
                    blockchainSeqs[n1][i],
                    blockchainSeqs[n2][j]
                )

    }  

    lemma lemmaAHelper3(
        dsBehaviour: DSBehaviour,
        dsStates: iseq<DSState>,
        seqNodes: iseq<Address>,
        configuration: Configuration
    ) returns (t: Trace)
    requires DSInit(dsStates[0], configuration)
    requires 
            forall i: nat :: pLemmajkfladjklfa(dsStates, seqNodes, dsBehaviour.environmentBehaviour, i)   
    ensures  validTrace(t, configuration);
    ensures forall i: nat :: t(i) == dsStates[i]
    {
        forall i: nat
        ensures 
                    var s := dsStates[i];
                    var s' := dsStates[i+1];        
                    && validDSState(s)
                    && DSNext(s, s')   
        {
            assert pLemmajkfladjklfa(dsStates, seqNodes, dsBehaviour.environmentBehaviour, i);
            var s := dsStates[i];
            var s' := dsStates[i+1];

            assert validDSState(s);
            assert DSNext(s, s');
            // assert DSNext(dsStates[i], dsStates[i+1]);
        }

        t := 
            (i: nat) => 
                dsStates[i];

        assert DSInit(t(0), configuration);

        forall i:nat 
        ensures 
            && validDSState(t(i))
            && DSNext(t(i), t(i+1))         
        {
            var s := t(i);
            var s' := t(i+1);

            assert s == dsStates[i];
            assert s' == dsStates[i+1];

            assert validDSState(s);
            assert DSNext(s, s');            
        }
    }   

    lemma lemmaA (
       dsBehaviour: DSBehaviour,
       configuration: Configuration
    ) 
    requires IsValidConfiguration(configuration)
    requires dsBehaviour in DSSpecificationBuilder(configuration).behaviours
    requires  |validators([configuration.genesisBlock])| > 0   
    ensures consistencyAndStability2(dsBehaviour, configuration) 
    {


        var allNodes := seqToSet(configuration.nodes);
        forall seqNodes, i:nat, j:nat, n1, n2 |
                    && pLemmajkfladjklfaGetSeqNodes(dsBehaviour, allNodes, seqNodes)
                    && n1 in dsBehaviour.nodesBehaviours.Keys
                    && n2 in dsBehaviour.nodesBehaviours.Keys
                    && pNodeStepIndexIsWithinBounds(seqNodes, n1, i)
                    && pNodeStepIndexIsWithinBounds(seqNodes, n2, j)
        ensures var blockchainSeqs := getBlockchainsSeq(dsBehaviour); 
                consistentBlockchains(
                    blockchainSeqs[n1][i],
                    blockchainSeqs[n2][j]
                );
        {
            var dsStates := lemmajkfladjklfa(dsBehaviour, configuration, seqNodes);

            // forall i: nat
            // ensures 
            //             var s := dsStates[i];
            //             var s' := dsStates[i+1];        
            //             && validDSState(s)
            //             && DSNext(s, s')   
            // {
            //     assert pLemmajkfladjklfa(dsStates, seqNodes, dsBehaviour.environmentBehaviour, i);
            //     var s := dsStates[i];
            //     var s' := dsStates[i+1];

            //     assert validDSState(s);
            //     assert DSNext(s, s');
            //     // assert DSNext(dsStates[i], dsStates[i+1]);
            // }

            // var t: Trace := 
            //     (i: nat) => 
            //         dsStates[i];

            // assert DSInit(t(0), configuration);

            // forall i:nat 
            // // ensures 
            // //     && validDSState(t(i))
            // //     && DSNext(t(i), t(i+1))         
            // {
            //     var s := t(i);
            //     var s' := t(i+1);

            //     assert s == dsStates[i];
            //     assert s' == dsStates[i+1];

            //     assert validDSState(s);
            //     assert DSNext(s, s');            
            // }

            var t := lemmaAHelper3(dsBehaviour, dsStates, seqNodes, configuration);

            

            assert validTrace(t, configuration);

            lemmaConsistencyAndStability(t, configuration);

            var blockchainSeqs := getBlockchainsSeq(dsBehaviour);

            assert n1 in dsBehaviour.nodesBehaviours.Keys;
            assert n2 in dsBehaviour.nodesBehaviours.Keys;

           
            var inv1 := lemmaAHelper2(dsBehaviour, dsStates, seqNodes, blockchainSeqs, i, n1);
            var inv2 := lemmaAHelper2(dsBehaviour, dsStates, seqNodes, blockchainSeqs, j, n2);



            assert dsStates[0].nodes[n1].blockchain == [configuration.genesisBlock] == dsBehaviour.nodesBehaviours[n1].initialBlockchain;

            // assert dsStates[0].nodes[n1].blockchain == dsBehaviour.nodesBehaviours[n1].initialBlockchain;

            // if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n1) 
            // {
            //     assert i + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n1).1;
            //     assert pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n1, seqNodes, dsStates, i);
            // }
            // else
            // {
            //     assert pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n1, seqNodes, dsStates, i);
            // }

            // var inv1 := getStepsTakeByNodeSoFarReverse(seqNodes, n1, i + 1);
            // assert dsBehaviour.nodesBehaviours[n1].steps[i].newBlockchain == dsStates[inv1].nodes[n1].blockchain;

            // assert dsStates[inv1].nodes[n1].blockchain == dsBehaviour.nodesBehaviours[n1].steps[i].newBlockchain;

            // if pGetStepsTakeByNodeSoFarIsLimited(seqNodes, n2) 
            // {
            //     assert j + 1 <= getMaxWhenGetStepsTakeByNodeSoFarIsLimited(seqNodes, n2).1;
            //     assert pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n2, seqNodes, dsStates, j);
            // }
            // else
            // {
            //     assert pLemmaGetSeqHonestNodeStates4ForAll2(dsBehaviour, n2, seqNodes, dsStates, j);
            // }

            // var inv2 := getStepsTakeByNodeSoFarReverse(seqNodes, n2, j + 1);
            // assert dsBehaviour.nodesBehaviours[n2].steps[j].newBlockchain == dsStates[inv2].nodes[n2].blockchain;    

            assert isHonest(t(inv1), n1);
            assert isHonest(t(inv2), n2);        

            lemmaAHelper(
                dsStates[inv1].nodes[n1].blockchain,
                dsStates[inv2].nodes[n2].blockchain,
                blockchainSeqs[n1][i],
                blockchainSeqs[n2][j]
            );

            // assert consistentBlockchains(
            //     blockchainSeqs[n1][i],
            //     blockchainSeqs[n2][j]
            // );
        }
    }

}