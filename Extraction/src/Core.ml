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
  let fmt = format_of_string "%s|%s" in
  let s = Printf.sprintf fmt
    (clist_to_string b.prevBlockHash)
    (String.concat "&" (List.map clist_to_string b.txs)) in
  let hash_str =
    "0x" ^ Cryptokit.transform_string (Cryptokit.Hexa.encode ())
      (Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) s) in
  let hash_cl = string_to_clist hash_str in
  hash_cl