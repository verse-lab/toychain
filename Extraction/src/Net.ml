open Unix

(* BEGIN utility functions *)

let raw_bytes_of_int (x : int) : bytes =
  let buf = Bytes.make 4 '\x00' in
  Bytes.set buf 0 (char_of_int (x land 0xff));
  Bytes.set buf 1 (char_of_int ((x lsr 8) land 0xff));
  Bytes.set buf 2 (char_of_int ((x lsr 16) land 0xff));
  Bytes.set buf 3 (char_of_int ((x lsr 24) land 0xff));
  buf

let int_of_raw_bytes (buf : bytes) : int =
  (int_of_char (Bytes.get buf 0)) lor
  ((int_of_char (Bytes.get buf 1)) lsl 8) lor
  ((int_of_char (Bytes.get buf 2)) lsl 16) lor
  ((int_of_char (Bytes.get buf 3)) lsl 24)

let int_of_ip_port (ip : string) (port : int) : int =
  let _x = Ipaddr.V4.to_int32 (Ipaddr.V4.of_string_exn ip) in
  let x = Int32.to_int _x in
  (x lsl 16) lor port

let ip_port_of_int (x : int) : (string * int) =
  let _ip = Int32.of_int ((x land (lnot 0xffff)) lsr 16) in
  let ip = Ipaddr.V4.to_string (Ipaddr.V4.of_int32 _ip) in
  let port = x land 0xffff in
  (ip, port)

let addr_of_ip_port (ip : string) (port : int) : ((int * int) * (int * int)) * (int * int) =
  let _x = int_of_ip_port ip port in
  let _port = _x land 0xffff in
  let (p0, p1) = ((_port land 0xff00) lsr 8, _port land 0x00ff) in
  let _ip = ((_x land (lnot 0xffff)) lsr 16) in
  let _right_quad = _ip land 0xffff in
  let _left_quad = (_ip land 0xffff0000) lsr 16 in
  let (a0, a1) = ((_left_quad land 0xff00) lsr 8, _left_quad land 0x00ff) in
  let (a2, a3) = ((_right_quad land 0xff00) lsr 8, _right_quad land 0x00ff) in
  (((a0, a1), (a2, a3)), (p0, p1))

let ip_port_of_addr addr : (string * int) =
  let (_ip, _port) = addr in
  let ((a0, a1), (a2, a3)) = _ip in
  let (p0, p1) = _port in
  let _i = (a0 lsl 24) lor (a1 lsl 16) lor (a2 lsl 8) lor a3 in
  let _p = (p0 lsl 8) lor p1 in
  let x = (_i lsl 16) lor _p in
  ip_port_of_int x

let int_of_addr addr =
  let ip, port = (ip_port_of_addr addr) in
  int_of_ip_port ip port

let addr_of_int x =
  let ip, port = ip_port_of_int x in
  addr_of_ip_port ip port

(* END utility functions *)

(* Interrupt-resistant versions of system calls  *)
let rec retry_until_no_eintr f =
  try f ()
  with Unix.Unix_error (EINTR, _, _) -> retry_until_no_eintr f

let num_nodes = 32
let read_fds : (Unix.file_descr, int) Hashtbl.t = Hashtbl.create num_nodes
let write_fds : (int, Unix.file_descr) Hashtbl.t = Hashtbl.create num_nodes

type cfg = { nodes : (int * (string * int)) list;
             me : int
           }

let the_cfg : cfg option ref = ref None
let listen_fd : file_descr = socket PF_INET SOCK_STREAM 0

let get_addr_port cfg name =
  try List.assoc name cfg.nodes
  with Not_found -> failwith (Printf.sprintf "Unknown name: %d" name)

let get_name_for_read_fd fd =
  Hashtbl.find read_fds fd

 (* TODO FIXME: receive all at once is one of the issues with Verdi *)
let send_chunk (fd : file_descr) (buf : bytes) : unit =
  let len = Bytes.length buf in
  (* Printf.printf "sending chunk of length %d" len; print_newline (); *)
  let n = retry_until_no_eintr (fun () -> send fd (raw_bytes_of_int len) 0 4 []) in
  if n < 4 then
    failwith "send_chunk: message header failed to send all at once.";
  let n = retry_until_no_eintr (fun () -> send fd buf 0 len []) in
  if n < len then
    failwith (Printf.sprintf "send_chunk: message of length %d failed to send all at once." len)

let recv_or_close fd buf offs len flags =
  let n = retry_until_no_eintr (fun () -> recv fd buf offs len flags) in
  if n = 0 then
    failwith "recv_or_close: other side closed connection.";
  n

let receive_chunk (fd : file_descr) : bytes =
  let buf4 = Bytes.make 4 '\x00' in
  let n = recv_or_close fd buf4 0 4 [] in
  if n < 4 then
    failwith "receive_chunk: message header did not arrive all at once.";
  let len = int_of_raw_bytes buf4 in
  let buf = Bytes.make len '\x00' in
  let n = recv_or_close fd buf 0 len [] in
  (* Printf.printf "received chunk of length %d" len; print_newline (); *)
  if n < len then
    failwith
        (Printf.sprintf "receive_chunk: message of length %d did not arrive all at once." len);
  buf

let get_cfg err_msg () =
  match !the_cfg with
  | None -> failwith (err_msg ^ " called before the_cfg was set")
  | Some cfg -> cfg

let str_cfg () =
  match !the_cfg with
  | None -> "No peers configured!"
  | Some cfg ->
    begin
      String.concat "; "
      (List.map
        (fun (nid, (ip, port)) -> (string_of_int nid) ^ " -> " ^ ip ^ ":" ^ (string_of_int port))
        cfg.nodes
      )
    end

let get_write_fd name =
  try Hashtbl.find write_fds name
  with Not_found ->
    let write_fd = socket PF_INET SOCK_STREAM 0 in
    let cfg = get_cfg "get_write_fd" () in
    let (ip, port) = get_addr_port cfg name in
    let entry = gethostbyname ip in
    let node_addr = ADDR_INET (Array.get entry.h_addr_list 0, port) in
    let chunk = Bytes.of_string (string_of_int cfg.me) in
    retry_until_no_eintr (fun () -> connect write_fd node_addr);
    send_chunk write_fd chunk;
    Hashtbl.add write_fds name write_fd;
    write_fd

let setup cfg =
  Printexc.record_backtrace true;
  the_cfg := Some cfg;
  let (_, port) = get_addr_port cfg cfg.me in
  Printf.printf "listening on port %d" port; print_newline ();
  setsockopt listen_fd SO_REUSEADDR true;
  bind listen_fd (ADDR_INET (inet_addr_any, port));
  listen listen_fd 8

let new_conn () =
  print_endline "new connection!";
  let (node_fd, node_addr) = retry_until_no_eintr (fun () -> accept listen_fd) in
  let chunk = receive_chunk node_fd in
  let node = Bytes.to_string chunk in
  let name = int_of_string node in
  Hashtbl.add read_fds node_fd name;
  (* ignore (get_write_fd name); *)
  Printf.printf "done processing new connection from node %s" node;
  print_newline ()

let check_for_new_connections () =
  let fds = [listen_fd] in
  let (ready_fds, _, _) = retry_until_no_eintr (fun () -> select fds [] [] 0.0) in
  List.iter (fun _ -> new_conn ()) ready_fds

let get_all_read_fds () =
  Hashtbl.fold (fun fd _ acc -> fd :: acc) read_fds []

let serialize_packet pkt = Marshal.to_string pkt []
let deserialize_packet s = Marshal.from_string s 0

let recv_pkt fd =
  let chunk = receive_chunk fd in
  let pkt = deserialize_packet (Bytes.to_string chunk) in
  (* let src = get_name_for_read_fd fd in *)
  pkt

let send_pkt dst pkt =
  let fd = get_write_fd dst in
  let s = serialize_packet pkt in
  let chunk = Bytes.of_string s in
  send_chunk fd chunk