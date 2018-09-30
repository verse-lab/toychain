From Toychain
Require Import Protocol Network Canonicals Parameters.
Require Import ExtrOcamlBasic ExtrOcamlString.

Extraction Inline ssrbool.SimplPred.
Extract Constant Timestamp => "float".
Extract Constant Hash => "string".
Extract Constant VProof => "string".
Extract Constant hashB => "Hashes.hashB".
Extract Constant hashT => "Hashes.hashT".
Extract Inlined Constant FCR => "Implementations.fcr".
Extract Inlined Constant genProof => "Implementations.mkProof".
Extract Inlined Constant GenesisBlock => "Implementations.genBlock".
Extract Inlined Constant VAF => "Implementations.vaf".
Extract Inlined Constant txValid => "Implementations.txValid".
Extract Inlined Constant tpExtend => "Implementations.tpExtend".
Cd "Extraction".
    Cd "Extracted".
        Separate Extraction procMsg procInt initWorld.
    Cd "..".
Cd "..".