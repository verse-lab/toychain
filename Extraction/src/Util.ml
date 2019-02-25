open Forests
open Protocol

module Addr = Address.Addr
module Types = TypesImpl.TypesImpl
module Consensus = Impl.ProofOfWork
module ForestImpl = Forests (Types) (Consensus)
module Pr = Protocol (Types) (Consensus) (ForestImpl) (Addr)

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

let string_of_address addr = string_of_int addr

let string_of_message (msg : Pr.coq_Message) =
  match msg with
  | AddrMsg peers -> "AddrMsg [" ^ (String.concat "; " (List.map string_of_address peers)) ^ "]"
  | ConnectMsg -> "ConnectMsg"
  | BlockMsg block -> "BlockMsg (" ^ (string_of_block block) ^ ")"
  | TxMsg tx -> "TxMsg (" ^ (string_of_tx tx) ^ ")"
  | InvMsg hashes -> "InvMsg [" ^ (String.concat "; " (List.map string_of_hash hashes)) ^ "]"
  | GetDataMsg hash -> "GetDataMsg (" ^ (string_of_hash hash) ^ ")"

let string_of_packet (pkt : Pr.coq_Packet) =
  Printf.sprintf "(%s, %s, %s)"
    (string_of_address pkt.src)
    (string_of_address pkt.dst)
    (string_of_message pkt.msg)