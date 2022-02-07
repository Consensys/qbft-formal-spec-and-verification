include "../../spec/L1/types.dfy"
include "distr_system_spec/common_functions.dfy"


module L1_TheoremsDefs {

    import opened L1_SpecTypes
    import opened L1_AuxiliaryFunctionsAndLemmas

    predicate consistentBlockchains(bc1:Blockchain, bc2:Blockchain)
    {
            var rbc1 := fromBlockchainToRawBlockchain(bc1);
            var rbc2 := fromBlockchainToRawBlockchain(bc2);
            || rbc1 <= rbc2
            || rbc2 <= rbc1
    }     
}