(* Don't import this file directly! Use the implementations provided by Impl.ml *)

open TypesImpl.TypesImpl

let clist_to_string cl = String.concat "" (List.map (String.make 1) cl)
let string_to_clist s = List.init (String.length s) (String.get s)

(* Implemented here and extracted into Impl.ml *)
let hash_of_tx (tx_cl : char list) =
  let s = clist_to_string tx_cl in
  let hash_str =
    "0x" ^ Cryptokit.transform_string (Cryptokit.Hexa.encode ())
     (Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) s) in
  let hash_cl = string_to_clist hash_str in
  hash_cl

let hash_of_block (b : coq_Block) =
  let fmt = format_of_string "%s|%s|%s" in
  let s = Printf.sprintf fmt
    (clist_to_string b.prevBlockHash)
    (String.concat "&" (List.map clist_to_string b.txs))
    (string_of_int b.proof) in
  let hash_str =
    "0x" ^ Cryptokit.transform_string (Cryptokit.Hexa.encode ())
      (Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) s) in
  let hash_cl = string_to_clist hash_str in
  hash_cl

let get_block_template (bc : coq_Blockchain) =
  let prev = List.nth bc (List.length bc - 1) in
  let new_block = {
    prevBlockHash = (hash_of_block prev);
    txs = [];
    proof = Random.int 1073741823 (* 2^30 - 1 *)
  } in new_block

(* TODO: is there a way to not duplicate the txValid logic here? *)
let get_acceptable_txs (bc : coq_Blockchain) (tp : coq_TxPool) = 
  let bc_txs = List.flatten (List.map (fun b -> b.txs) bc) in
  (* Remove duplicates *)
  let candidates = List.sort_uniq compare tp in
  let acceptable = List.filter (fun t -> not (List.mem t bc_txs)) candidates in
  acceptable

(* coq_Blockchain -> coq_TxPool -> coq_Timestamp -> *)
(* (coq_TxPool * coq_VProof) option *)
(* 
let genProof =
  fun (bc : coq_Blockchain) (tp : coq_TxPool) (ts: coq_Timestamp) ->
  if List.length bc == 0 then None else
  let template = get_block_template bc in
  let acc_txs = get_acceptable_txs bc tp in
  let block = {template with txs = acc_txs} in
  if coq_VAF block bc (block.txs) then Some (acc_txs, (block.proof)) else None
   *)