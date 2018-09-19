From Toychain
Require Import Protocol Network Forests.
Require Import ExtrOcamlBasic.

Extraction Inline ssrbool.SimplPred.
Extract Constant Timestamp => "float".
(* Extract Constant Hash => "string".
Extract Constant VProof => "string". *)
Cd "Extraction".
    Cd "Extracted".
        Separate Extraction procMsg procInt initWorld.
    Cd "..".
Cd "..".