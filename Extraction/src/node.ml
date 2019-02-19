open Forests
open Protocol

module Addr = Address.Addr
module ConsensusParams = Impl.ProofOfWork
module ForestImpl = Forests (ConsensusParams)
module ProtocolImpl = Protocol (ConsensusParams) (ForestImpl) (Addr)

let state = ref (ProtocolImpl.coq_Init 0);;

let main () =
  let argv = Array.to_list Sys.argv in
  let args = List.tl argv in
  Printf.printf "You are node %s\n" (string_of_int (!state).id)

let () = main ()

