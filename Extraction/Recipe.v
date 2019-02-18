Require Extraction.
From Toychain
Require Import Address Protocol Forests Parameters.
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt.

(* Instantiate modules *)
Module ForestImpl := Forests CP.
Module ProtocolImpl := Protocol CP ForestImpl Addr.

(* This solves an error where the implementation of ssrbool.ml
   doesn't match the interface *)
Extraction Inline ssrbool.SimplPred.

Extract Constant CP.Timestamp => "int".
Extract Constant CP.Hash => "string".
Extract Constant CP.VProof => "unit".
Extract Constant CP.Transaction => "string".

Cd "Extraction/src/toychain".
Separate Extraction
  ProtocolImpl.procMsg
  ProtocolImpl.procInt
  ProtocolImpl.State.
Cd "../../..".
