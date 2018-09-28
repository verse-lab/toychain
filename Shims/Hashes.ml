open Canonicals
open Blocks

let hashT (transaction:coq_Transaction): coq_Hash = 
  let hash = Hashtbl.hash transaction in 
  string_of_int hash

let hashB (blk:coq_Block): coq_Hash = 
  match Obj.magic blk.prevBlockHash with 
  | "0000000" -> "0000000"
  | _ -> let hash = Hashtbl.hash blk in 
  string_of_int hash
