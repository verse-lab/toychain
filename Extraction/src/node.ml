open Forests
open Protocol
open Util

module Addr = Address.Addr
module ConsensusParams = Impl.ProofOfWork
module ForestImpl = Forests (ConsensusParams)
module ProtocolImpl = Protocol (ConsensusParams) (ForestImpl) (Addr)

let node_id = 0
let st = ref (ProtocolImpl.coq_Init node_id);;

open ForestImpl

let main () =
  let argv = Array.to_list Sys.argv in
  let args = List.tl argv in
  let blocks = all_blocks !st.blockTree in
  Printf.printf "Your blocktree has %s block(s)!\n"
    (string_of_int (List.length blocks)) ;;
  Printf.printf "You are node %s\n" (string_of_int !st.id) ;;


let () = main ()

