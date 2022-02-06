include "../../../spec/L1/types.dfy"
include "../distr_system_spec/network.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"
include "../../../spec/L1/node.dfy"
include "../../common/sets.dfy"
include "../distr_system_spec/distributed_system.dfy"
include "axioms.dfy"

module EEALemmaQuorum
{

    import opened EEASpecTypes
    import opened EEASpecNetwork
    import opened EEADistributedSystem
    import opened EEAAuxiliaryFunctionsAndLemmas
    import opened EEASpec
    import opened HelperLemmasSets
    import opened EEAAxioms

    lemma lemmaQuorumIntersection<T(==)>(nodes:set<T>, byz:set<T>, Q1:set<T>, Q2:set<T>)
    requires nodes != {}
    requires Q1 <= nodes
    requires Q2 <= nodes
    // requires byz <= nodes
    requires |Q1| >= quorum(|nodes|)
    requires |Q2| >= quorum(|nodes|)
    requires |byz| <= f(|nodes|)
    ensures var hon := nodes - byz; Q1 * Q2 * hon != {}
    {
        var hon := nodes - byz;

        calc {
            |Q1 * Q2 * hon|;
            ==
            |(Q1*Q2) * hon|;
            ==
            |Q1*Q2| + |hon| - |(Q1*Q2) + hon|;
            >= 
            |Q1*Q2| + |nodes| - |byz| - |(Q1*Q2) + hon|;
            >= calc {
                |Q1 * Q2|;
                |Q1| + |Q2| - |Q1 + Q2|;
                >= calc {
                        |Q1 + Q2|; 
                        <= {SubsetCardinality(Q1 + Q2, nodes);}
                        |nodes|; 
                    }
                |Q1| + |Q2| - |nodes|;
            }
            |Q1| + |Q2| - |byz| - |(Q1*Q2) + hon|;
            >= {SubsetCardinality((Q1*Q2) + hon, nodes);}
            |Q1| + |Q2| - |byz| - |nodes|;
            >=
            2 * quorum(|nodes|)- |nodes| - f(|nodes|);
            >=
            1;
        }

    }

    lemma lemmaThereExistsAnHonestInQuorum<T(==)>(nodes:set<T>, byz:set<T>, Q1:set<T>)
    requires nodes != {}
    requires Q1 <= nodes
    requires |Q1| >= quorum(|nodes|)
    requires |byz| <= f(|nodes|)
    ensures var hon := nodes - byz; Q1 * hon != {}
    {
        var hon := nodes - byz;

        calc {
            |Q1 * hon|;
            ==
            |Q1| + |hon| - |Q1 + hon|;
            >= 
            |Q1| + |nodes| - |byz| - |Q1 + hon|;
            >= 
            {SubsetCardinality(Q1 + hon, nodes);}
            // calc {
            //     |Q1|;
            //     |Q1| + |Q2| - |Q1 + Q2|;
            //     >= calc {
            //             |Q1 + Q2|; 
            //             <= {SubsetCardinality(Q1 + Q2, nodes);}
            //             |nodes|; 
            //         }
            //     |Q1| + |Q2| - |nodes|;
            // }
            |Q1|  - |byz|;
            >=
            quorum(|nodes|) - f(|nodes|);
            >=
            1;
        }

    }    

    // lemma lllll(s:set<QbftMessage>, h:nat, r:nat, d:Hash)
    // requires forall m | m in s ::   && m.Prepare?
    //                                 && m.preparePayload.unsignedPayload.height == h
    //                                 && m.preparePayload.unsignedPayload.round == r
    //                                 && m.preparePayload.unsignedPayload.digest == d

    // ensures forall m1,m2 | m1 in s && m2 in s :: m1 != m2 ==> recoverSignature(m1) != recoverSignature(m2)
    // {
    //     lemmaSignedPrepare();
    // }





}