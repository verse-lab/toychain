Require Extraction.
From Toychain
Require Import Protocol Forests Parameters Impl.
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt.

(* Instantiate modules *)
Module ForestImpl := Forests ProofOfWork.
Module ProtocolImpl := Protocol ProofOfWork ForestImpl.

Cd "Extraction/src".
Separate Extraction
  ProtocolImpl.procMsg
  ProtocolImpl.procInt
  ProtocolImpl.State.
Cd "../..".
