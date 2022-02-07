// TODO: Check copyright for node spec files
/**
 * Copyright © 2021 EEA Inc. 
 *
 * This document is available under the terms of the Apache 2.0 License
 * (http://www.apache.org/licenses/LICENSE-2.0.html)
 *
 * This file does provide any specification. It just contains lemmas that are
 * used in the `UponCommit` and `UponRoundChange` predicates in `node.dfy` when
 * declaring sets via such-that assignment (`:|`) as the verifier is not able to
 * automatically prove the existence of such sets.
 */
include "types.dfy"
include "node_auxiliary_functions.dfy"

module L1_Lemmas
{
    import opened L1_SpecTypes
    import opened L1_AuxiliaryFunctionsAndLemmas

    lemma lemmaIfMappedSubSetOfGreaterSizeExistsThenMappedSmallSubsetExistsHelper1<T,T2>(s:set<T>, s2: set<T2>, f:T -> T2)
    requires s2 == set m | m in s :: f(m)
    ensures |s2| <= |s|
    {
        if s != {}
        {
            var e :| e in s;
            var news := s - {e};
            var news2 := set m | m in news :: f(m);
            lemmaIfMappedSubSetOfGreaterSizeExistsThenMappedSmallSubsetExistsHelper1(news, news2,f);

            if f(e) in news2
            {
                assert s2 == news2;
            }
            else
            {
                assert |news2| < |s|;
                assert f(e) in s2;
                assert s2 == news2 + {f(e)};
                assert |s2| == |news2| + 1;
            }
        }
    }        

    lemma lemmaIfMappedSubSetOfGreaterSizeExistsThenMappedSmallSubsetExistsHelper2<T,T2>(a:set<T>, b:set<T>, c:set<T2>, d:set<T2>, f:T -> T2)
    requires b < a
    requires |a| == |b| + 1
    requires c == set m | m in a :: f(m)
    requires d == set m | m in b :: f(m)
    ensures |d| == |c| || |c| == |d| + 1
    {
        var diff := a - b;
        assert |diff| == 1;
        var e :| e in diff;
        assert |diff-{e}| == 0;
        // assert d - {e} == {};
        assert diff == {e};
        assert b + {e} == a;

        if f(e) in d 
        {
            assert d == c;
            assert |d| == |c|;
        }
        else
        {
            assert c == d + {f(e)};
        }        
    }         

    lemma lemmaIfMappedSubSetOfGreaterSizeExistsThenMappedSmallSubsetExistsHelper3<T,T2>(sM: set<T>, s1:set<T>, f:set<T> -> set<T2>, v:nat) returns (s2:set<T>)
    requires |f(s1)| >= v
    requires s1 <= sM
    requires forall a :: |f(a)| <= |a|
    requires forall a,b | b < a && |a| == |b| + 1  :: |f(a)| == |f(b)| || |f(a)| == |f(b)| + 1
    ensures s2  <= s1
    ensures |f(s2)| == v
    {
        if s1 == {} 
        {
            s2 := s1;
        }
        else if |f(s1)| == v 
        {
            s2 := s1;
        }
        else
        {
            var e :| e in s1;
            var news := s1 - {e};
            assert |news| == |s1| - 1;

            var s2r := lemmaIfMappedSubSetOfGreaterSizeExistsThenMappedSmallSubsetExistsHelper3(sM,news,f,v);
            s2 := s2r;
        }
    }

    lemma lemmaIfMappedSubSetOfGreaterSizeExistsThenMappedSmallSubsetExistsGeneric<T, T2>(
        s1: set<T>,
        fSetMap: set<T> -> set<T2>,
        fElMap: T -> T2,
        v: nat
    )
    requires exists s1' :: s1' <= s1 && |fSetMap(s1')| >= v
    // requires fSetMap == ((s: set<T>) => set m | m in s :: fElMap(m))
    requires forall s1' :: fSetMap(s1') == set m | m in s1' :: fElMap(m)
    ensures exists s2 :: s2 <= s1 && |fSetMap(s2)| == v  
    {
        forall a 
        ensures |fSetMap(a)| <= |a|
        {
            lemmaIfMappedSubSetOfGreaterSizeExistsThenMappedSmallSubsetExistsHelper1(a, fSetMap(a), fElMap);
        }        

        forall a,b | b < a && |a| == |b| + 1 
        ensures |fSetMap(a)| == |fSetMap(b)| || |fSetMap(a)| == |fSetMap(b)| + 1
        {
            lemmaIfMappedSubSetOfGreaterSizeExistsThenMappedSmallSubsetExistsHelper2(a,b,fSetMap(a),fSetMap(b),fElMap);
        }             

        var s1' :| s1' <= s1 && |fSetMap(s1')| >= v;
        var s2 := lemmaIfMappedSubSetOfGreaterSizeExistsThenMappedSmallSubsetExistsHelper3(s1, s1', fSetMap, v);             
    }  
 
    lemma lemmaToProveExistenceOfSetFrc(
        signedRoundChangesReceived: set<SignedRoundChange>,
        v: nat
    )
    requires exists s1 :: s1 <= signedRoundChangesReceived && |getSetOfRoundChangeSenders(s1)| >= v
    ensures exists s3 :: s3 <= signedRoundChangesReceived && |getSetOfRoundChangeSenders(s3)| == v  
    {
        lemmaIfMappedSubSetOfGreaterSizeExistsThenMappedSmallSubsetExistsGeneric(signedRoundChangesReceived, getSetOfRoundChangeSenders, recoverSignedRoundChangeAuthor, v);           
    }  

    lemma lemmaIfSubSetOfGreaterSizeExistsThenSmallSubsetExistsHelper<T>(s1:set<T>, s2:set<T>, sz1:nat) returns (s3:set<T>)
    requires s1 <= s2    
    requires |s1| >= sz1
    ensures s3 <= s2
    ensures |s3| == sz1
    {
        if |s1| == sz1
        {
            s3 := s1;
        }
        else
        {
            var e :| e in s1;
            var s1Sub := s1 - {e};
            s3 := lemmaIfSubSetOfGreaterSizeExistsThenSmallSubsetExistsHelper(s1Sub,s2,sz1);
        }
    }

    lemma lemmaIfSubSetOfGreaterSizeExistsThenSmallSubsetExists<T>(s2:set<T>, sz1:nat)
    requires exists s1 ::   && s1 <= s2    
                            && |s1| >= sz1
    ensures exists s3 ::    && s3 <= s2
                            && |s3| == sz1    
    {
        var s1 :| && s1 <= s2    
                            && |s1| >= sz1;
        var s3 := lemmaIfSubSetOfGreaterSizeExistsThenSmallSubsetExistsHelper(s1,s2,sz1);
    }
    
}