open Forests
open Protocol
open Util

module Addr = Address.Addr
module Types = TypesImpl.TypesImpl
module Consensus = Impl.ProofOfWork
module ForestImpl = Forests (Types) (Consensus)
module Pr = Protocol (Types) (Consensus) (ForestImpl) (Addr)
open ForestImpl
open Pr
open Net

(** STATE **)
let _ = Random.self_init ()
let node_id = ref (-1)
let cluster = ref []
let nodes = ref []
let st = ref (coq_Init 0)

let hashes = ref 0
let last_measurement = ref 0
let last_time = ref (Unix.time ())

(* Command line arguments *)
let usage msg =
  print_endline msg;
  Printf.printf "%s usage:\n" Sys.argv.(0);
  Printf.printf "    %s -me IP_ADDR PORT -cluster <CLUSTER>\n" (Array.get Sys.argv 0);
  print_endline "where:";
  print_endline "    CLUSTER   is a list of tuples of IP_ADDR PORT,";
  print_endline "              giving OTHER known nodes in the system";
  exit 1

let rec parse_args = function
  | [] -> ()
  | "-me" :: ip :: port :: args ->
    begin
      node_id := int_of_ip_port ip (int_of_string port);
      parse_args args
    end
  | "-cluster" :: args -> parse_args args
  | ip :: port :: args ->
    begin
      cluster := (ip, int_of_string port) :: !cluster;
      parse_args args
    end
  | arg :: args -> usage ("Unknown argument " ^ arg)


(* MESSAGE and TRANSITION LOGIC *)
let rec get_pkt = function
  | [] -> None
  | fd :: fds ->
      try
        Some (recv_pkt fd)
      with e ->
      begin
        get_pkt fds
      end

let send_all (pkts : coq_Packet list) =
  List.iter (fun pkt -> send_pkt pkt.dst pkt) pkts

(* TODO: will need special logic for ConnectMsg (i.e. update Net) *)
let procMsg_wrapper () =
  let () = check_for_new_connections () in
  let fds = get_all_read_fds () in
  let (ready_fds, _, _) = retry_until_no_eintr (fun () -> Unix.select fds [] [] 0.0) in
  begin
    match get_pkt ready_fds with
    | None -> (* nothing available *) None
    | Some pkt ->
        begin
          Printf.printf "Received packet %s" (string_of_packet pkt);
          print_newline ();
          if pkt.dst != !node_id then
          begin
            Printf.printf " - packet sent in error? (we're not the destination!)";
            print_newline ();
            None
          end
          else
          begin
            let (st', pkts) = Pr.procMsg !st pkt.src pkt.msg 0 in
            st := st';
            send_all pkts;
            Some (st, pkts)
          end
        end
  end

let procInt_wrapper () =
  (* Randomly decide what to do *)
  let shouldIssueTx = (Random.int 10000 == 0) in
  match shouldIssueTx with
  | true ->
      let tx = clist_of_string ("TX " ^ (string_of_int (Random.int 65536))) in
      let (st', pkts) = Pr.procInt !st (TxT tx) 0 in
      Printf.printf "Created %s" (string_of_clist tx);
      print_newline ();
      st := st';
      send_all pkts;
      Some (st, pkts)
  | false ->
      let (st', pkts) = Pr.procInt !st (MintT) 0 in
      hashes := !hashes + 1;
      (* Bit of a hack to figure out whether a block was mined *)
      if List.length pkts > 0 then
        begin
            Printf.printf "Mined a block!" ;
            print_newline ();
            st := st';
            send_all pkts;
            Some (st, pkts)
        end
      else None


(* NODE LOGIC *)
let main () = 
  (* XXX: our hack of packing IPv4:port into ints only works on 64 bit;
          see Net.ml `int_of_ip_port` and `ip_port_of_int`
  *)
  assert (Sys.word_size >= 64);;

  let args = (List.tl (Array.to_list Sys.argv)) in
  if List.length args == 0 then usage "" else
  begin
    parse_args args ;

    let _cluster = (List.map (fun (ip, port) -> int_of_ip_port ip port) !cluster) in
    let peer_ids = if not (List.mem !node_id _cluster) then !node_id :: _cluster else _cluster in
    nodes := List.map (fun nid -> (nid, ip_port_of_int nid)) peer_ids ;

    begin
      st := {(coq_Init !node_id) with peers = peer_ids} ;
      let (ip, port) = ip_port_of_int !node_id in
      Printf.printf "You are node %s (%s:%d)" (string_of_address !st.id) ip port;
      print_newline ();
      
      setup { nodes = !nodes; me = !node_id };
      Printf.printf "\n---------\nChain\n%s\n---------\n" (string_of_blockchain (btChain !st.blockTree));

      while true do
        ignore (procInt_wrapper ());
        ignore (procMsg_wrapper ()); 
        (* Every 10 seconds, print your chain. *)
        let ts = (int_of_float (Unix.time ())) in
        if ts mod 10 == 0 then 
          begin
            Printf.printf "\n---------\nChain\n%s\n---------\n" (string_of_blockchain (btChain !st.blockTree));
            Printf.printf "%0.2f hashes per second\n"
              ((float_of_int (!hashes - !last_measurement)) /. (Unix.time () -. !last_time));
            print_newline ();
            last_measurement := !hashes;
            last_time := Unix.time ();
            Unix.sleep 1 ;
            ()
          end
        else ()
      done;
    end
  end

let () = main ()