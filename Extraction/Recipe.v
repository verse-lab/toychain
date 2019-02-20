Require Extraction.
From Toychain
Require Import Address Protocol Forests Parameters Impl.
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt.

(* Instantiate modules *)
Module ForestImpl := Forests TypesImpl ProofOfWork.
Module ProtocolImpl := Protocol TypesImpl ProofOfWork ForestImpl Addr.

(* This solves an error where the implementation of ssrbool.ml
   doesn't match the interface *)
Extraction Inline ssrbool.SimplPred.

(* ordinals are nat, and we want to extract nat to int *)
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant ProofOfWork.hashT =>
  "(fun tx -> 0)".

Extract Constant ProofOfWork.hashB =>
  "(fun blk -> 0)".

(* coq_Blockchain -> coq_TxPool -> coq_Timestamp -> *)
(* (coq_TxPool * coq_VProof) option *)

Extract Constant ProofOfWork.genProof =>
  "(fun bc txp ts -> None)".

Cd "Extraction/src/toychain".
Separate Extraction
  ProtocolImpl.procMsg
  ProtocolImpl.procInt
  ProtocolImpl.State.
Cd "../../..".
