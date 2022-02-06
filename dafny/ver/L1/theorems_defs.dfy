include "../../spec/L1/types.dfy"
include "distr_system_spec/common_functions.dfy"


module EEATheoremsDefs {

    import opened EEASpecTypes
    import opened EEAAuxiliaryFunctionsAndLemmas

    predicate consistentBlockchains(bc1:Blockchain, bc2:Blockchain)
    {
            var rbc1 := fromBlockchainToRawBlockchain(bc1);
            var rbc2 := fromBlockchainToRawBlockchain(bc2);
            || rbc1 <= rbc2
            || rbc2 <= rbc1
    }     
}