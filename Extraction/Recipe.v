Require Extraction.
From Toychain
Require Import Address Protocol Forests Parameters Impl.
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt.

(* Instantiate modules *)
Module ForestImpl := Forests ProofOfWork.
Module ProtocolImpl := Protocol ProofOfWork ForestImpl Addr.

(* This solves an error where the implementation of ssrbool.ml
   doesn't match the interface *)
Extraction Inline ssrbool.SimplPred.

Cd "Extraction/src/toychain".
Separate Extraction
  ProtocolImpl.procMsg
  ProtocolImpl.procInt
  ProtocolImpl.State.
Cd "../../..".
