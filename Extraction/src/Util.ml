open Forests

module Types = TypesImpl.TypesImpl
module ConsensusParams = Impl.ProofOfWork
module ForestImpl = Forests (Types) (ConsensusParams)

open Types

let clist_to_string cl = String.concat "" (List.map (String.make 1) cl)
let string_to_clist s = List.init (String.length s) (String.get s)

let string_of_tx tx = clist_to_string tx
let string_of_hash h = clist_to_string h

let string_of_block (b : coq_Block) =
  let fmt = format_of_string "%s = {prev = %s, txs = %s}" in
  Printf.sprintf fmt
    (string_of_hash (ConsensusParams.hashB b))
    (string_of_hash b.prevBlockHash)
    (String.concat " " (List.map string_of_tx b.txs))

let string_of_blockchain (chain : coq_Blockchain) =
  String.concat " " (List.map string_of_block chain)