Require Extraction.
From Toychain
Require Import Address Protocol Forests Parameters TypesImpl Impl.
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt.

(* Instantiate modules *)
Module ForestImpl := Forests TypesImpl ProofOfWork.
Module ProtocolImpl := Protocol TypesImpl ProofOfWork ForestImpl Addr.

(* Avoid colliding with OCaml standard library names *)
Extraction Blacklist String List.

(* This solves an error where the implementation of ssrbool.ml
   doesn't match the interface *)
Extraction Inline ssrbool.SimplPred.

(* ordinals are nat, and we want to extract nat to int *)
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant ProofOfWork.hashT => "Core.hash_of_tx".

Extract Constant ProofOfWork.hashB => "Core.hash_of_block".

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
