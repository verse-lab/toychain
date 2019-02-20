open Forests
open Protocol
open Util

module Addr = Address.Addr
module Types = Impl.TypesImpl
module ConsensusParams = Impl.ProofOfWork
module ForestImpl = Forests (Types) (ConsensusParams)
module ProtocolImpl = Protocol (Types) (ConsensusParams) (ForestImpl) (Addr)

let node_id = 0
let st = ref (ProtocolImpl.coq_Init node_id);;

open ForestImpl

let main () =
  let chain = btChain !st.blockTree in
  Printf.printf "Chain: %s\n" (string_of_blockchain chain) ;;

  let blocks = all_blocks !st.blockTree in
  Printf.printf "Your blocktree has %s block(s)!\n"
    (string_of_int (List.length blocks)) ;;
 
  Printf.printf "You are node %s\n" (string_of_int !st.id) ;;

let () = main ()

