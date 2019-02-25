open Forests
open Protocol
open Util

module Addr = Address.Addr
module Types = TypesImpl.TypesImpl
module Consensus = Impl.ProofOfWork
module ForestImpl = Forests (Types) (Consensus)
module Pr = Protocol (Types) (Consensus) (ForestImpl) (Addr)

let _ = Random.self_init ()

let node_id = 0
let st = ref (Pr.coq_Init node_id)

open ForestImpl

let mine (_ : unit )= 
  let ts = ref (int_of_float (Unix.time ())) in
  let found_block = ref false in
  let new_state = ref !st in
  let hashes = ref 0 in
  while not (!found_block) do
    let (st' , msgs) = Pr.procInt !st Pr.MintT !ts in
    hashes := !hashes + 1 ;
    if List.length msgs > 0 then
      begin
        found_block := true ;
        new_state := st' ;
      end
  done;
  Printf.printf "Found block after %s hashes!\n" (string_of_int !hashes) ;
  !new_state


let main () =
  Printf.printf "You are node %s\n" (string_of_int !st.id) ;

  let blocks = all_blocks !st.blockTree in
  Printf.printf "Your blocktree has %s block(s)!\n"
    (string_of_int (List.length blocks)) ;

  let chain = btChain !st.blockTree in
  Printf.printf "Chain:\n %s\n" (string_of_blockchain chain) ;


  st := (mine ()) ;
  Printf.printf "Chain:\n %s\n" (string_of_blockchain (btChain !st.blockTree)) ;
  Printf.printf "Work of last block: %s\n"
    (string_of_int
      (Obj.magic (Consensus.work (List.nth (btChain !st.blockTree) 1)))
    ) ;

  let pkt : Pr.coq_Packet =
    {src = 0; dst = 1; msg = Pr.BlockMsg (List.nth (btChain !st.blockTree) 1)} in
  let ser = Net.serialize_packet pkt in
  let deser =  Net.deserialize_packet ser in
  Printf.printf "packet: %s\n" ser ;
  Printf.printf "deserialized: %s \n" (string_of_packet deser)

let () = main ()

