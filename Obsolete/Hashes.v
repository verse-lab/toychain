From mathcomp.ssreflect
Require Import fintype.

From Toychain
Require Import Canonicals.
Require Import String Ascii List.

Definition address_to_list (address:Address):= 
    let (ip, port) := address in
    match (ip, port) with 
    | (a, b, c, d, e) => (a :: b :: c :: d :: e :: nil)%list
    end.

Definition ordList_to_natList {n:nat} (ls : list 'I_n):=
    List.map (fun (x:'I_n) => nat_of_ord x) ls.

Definition addr_to_list n := (ordList_to_natList (address_to_list n)).

Check addr_to_list.
Fixpoint addr_to_string ls:= 
    match ls with 
    | x::xs => String (ascii_of_nat x) (addr_to_string xs)
    | nil => EmptyString
    end.

Definition hashT (t:Transaction):Hash := 
    let (src, dst, val) := t in
    let (s, d) := (addr_to_list src, addr_to_list dst) in
    String.append (String.append (addr_to_string s) (addr_to_string d)) (String (ascii_of_nat val) EmptyString).



    

