open Forests

module Types = TypesImpl.TypesImpl
module Consensus = Impl.ProofOfWork
module ForestImpl = Forests (Types) (Consensus)

open Types
open Consensus

let clist_to_string cl = String.concat "" (List.map (String.make 1) cl)
let string_to_clist s = List.init (String.length s) (String.get s)

let string_of_tx tx = clist_to_string tx
let string_of_hash h = clist_to_string h

let string_of_block (b : coq_Block) =
  let fmt = format_of_string "%s = {prev = %s, txs = %s, nonce = %s}" in
  Printf.sprintf fmt
    (string_of_hash (hashB b))
    (String.sub (string_of_hash b.prevBlockHash) 0 8)
    (String.concat " " (List.map string_of_tx b.txs))
    (string_of_int b.proof)

let string_of_blockchain (chain : coq_Blockchain) =
  String.concat "\n" (List.map string_of_block chain)

