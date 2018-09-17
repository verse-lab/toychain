From Toychain
Require Import Protocol Network.
Require Import ExtrOcamlBasic.

Extraction Inline ssrbool.SimplPred.
Cd "Extraction".
    Cd "Extracted".
        Separate Extraction procMsg procInt initWorld.
    Cd "..".
Cd "..".