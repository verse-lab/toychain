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

(* This works around what seems to be a bug in Coq's extraction
   mechanism. The normal extraction gives this code, but with "assert
   false" instead of "assert true". *)
Extract Constant fintype.Finite.base2 =>
"
  fun c ->
    { Choice.Countable.base = c.base; Choice.Countable.mixin =
      (Obj.magic mixin_base (assert true (* Proj Args *)) c.mixin) }
".


(* ordinals are nat, and we want to extract nat to int *)
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant ProofOfWork.hashT => "Core.hash_of_tx".

Extract Constant ProofOfWork.hashB => "Core.hash_of_block".

Extract Constant ProofOfWork.genProof =>
"
  fun bc tp ts ->
  if List.length bc == 0 then None else
  let template = Core.get_block_template bc in
  let acc_txs = Core.get_acceptable_txs bc tp in
  let block = {template with txs = acc_txs} in
  if coq_VAF block bc (block.txs) then Some (acc_txs, (block.proof)) else None
".

Cd "Extraction/src/toychain".
Separate Extraction
  ProtocolImpl.procMsg
  ProtocolImpl.procInt
  ProtocolImpl.State.
Cd "../../..".
