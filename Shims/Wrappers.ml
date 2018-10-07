open Shim

let max_errors = 3
let errors = ref 0

let send_action_wrapper packet =
  send_packet packet

let rec get_packet = function
  | [] -> None
  | fds ->
    try
    Some (List.map recv_packet fds)
    with e ->
      errors := !errors + 1;
      if !errors < max_errors
      then get_packet (List.tl fds)
      else begin
          raise e
      end

let tryrecv_action_wrapper () =
  let () = check_for_new_connections () in
  let fds = get_all_read_fds () in
  let (ready_fds, _, _) = Unix.select fds [] [] 0.0 in
  match get_packet ready_fds with
    | None -> None
    | Some packets -> Some packets