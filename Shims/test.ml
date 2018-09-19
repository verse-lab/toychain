open Protocol
open Datatypes
(* open Util *)
open Canonicals
  
let me : coq_Address ref = ref {ip = (((O,O),O),O); port=O}
let nodes : coq_Address list ref = ref []

(* let usage msg =
  print_endline msg;
  Printf.printf "%s usage:\n" Sys.argv.(0);
  Printf.printf "    %s [OPTIONS] <CLUSTER>\n" (Array.get Sys.argv 0);
  print_endline "where:";
  print_endline "    CLUSTER   is a list of pairs of IP_ADDR PORT,";
  print_endline "              giving all the nodes in the system.";
  print_endline "              The first pair given is taken as  .";
  print_endline "              the local node and treated as such.";
  print_newline ();
  print_endline "Options are as follows:";
  print_endline "    -me <NAME>        the identity of this node (required)";
  exit 1

let rec parse_args = function
  | [] -> ()
  | "-nodes" :: ip :: port :: args ->
      begin
        me := {ip = (((O,O),O),O); port = O};
        parse_args args
      end
  | ip :: port :: args -> begin
      nodes := {ip = (((O,O),O),O); port = O} :: !nodes;
      parse_args args
    end
  | arg :: args ->
      usage ("Unknown argument " ^ arg)

let main () = 
  let args = List.tl (Array.to_list Sys.argv) in
  parse_args (args);
  (* let lstate = {nodes = !nodes; me = !me} in 
    setup lstate;
    Runner.node_run ();
    closeSockets (); *)
    () *)

let _ = print_endline "test"
  (* Printf.printf "main %s\n"  (string_of_float (Unix.time ())); *)
  (* main () *)