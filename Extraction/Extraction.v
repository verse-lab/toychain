From Toychain
Require Import Protocol Network Canonicals Parameters.
Require Import ExtrOcamlBasic ExtrOcamlString.

Extraction Inline ssrbool.SimplPred.
Extract Constant Timestamp => "float".
Extract Constant Hash => "string".
Extract Constant VProof => "string".
Extract Constant hashB => "Hashes.hashB".
Extract Constant hashT => "Hashes.hashT".
Extract Constant FCR => "Implementations.fcr".
(* Extract Constant genProof => "Implementations.mkProof". *)
Extract Constant GenesisBlock => "Implementations.genBlock".
Extract Constant VAF => "Implementations.vaf".
Extract Constant txValid => "Implementations.txValid".
Extract Constant tpExtend => "Implementations.tpExtend".
Cd "Extraction".
    Cd "Extracted".
        Separate Extraction procMsg procInt initWorld.
    Cd "..".
Cd "..".