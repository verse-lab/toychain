open Forests

module Types = Impl.TypesImpl
module ConsensusParams = Impl.ProofOfWork
module ForestImpl = Forests (Types) (ConsensusParams)

open Types

let string_of_tx = string_of_int

let string_of_block (b : coq_Block) =
  let fmt = format_of_string "{prev = %s, txs = %s}" in
  Printf.sprintf fmt
    (string_of_int b.prevBlockHash)
    (String.concat " " (List.map string_of_tx b.txs))

let string_of_blockchain (chain : coq_Blockchain) =
  String.concat " " (List.map string_of_block chain)