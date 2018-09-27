From Toychain
Require Import Protocol Network Canonicals Parameters.
Require Import ExtrOcamlBasic ExtrOcamlString.

Extraction Inline ssrbool.SimplPred.
Extract Constant Timestamp => "float".
Extract Constant Hash => "string".
Extract Constant VProof => "string".
Extract Constant hashB => "Hashes.hashB".
Extract Constant hashT => "Hashes.hashT".
Cd "Extraction".
    Cd "Extracted".
        Separate Extraction procMsg procInt initWorld.
    Cd "..".
Cd "..".