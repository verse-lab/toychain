open Wrappers
open Util
open Shim

let aux lstate = 
    let me = lstate in
    match me.me.port with
        | 9001 -> send_action_wrapper {src = me.me; dst = {ip = "127.0.0.1"; port = 9002}; msg = ConnectMsg}
        | 9002 -> send_action_wrapper {src = me.me; dst = {ip = "127.0.0.1"; port = 9003}; msg = ConnectMsg};
                  send_action_wrapper {src = me.me; dst = {ip = "127.0.0.1"; port = 9001}; msg = AddrMsg me.nodes};
                  send_action_wrapper {src = me.me; dst = {ip = "127.0.0.1"; port = 9003}; msg = AddrMsg me.nodes};
        | 9003 -> send_action_wrapper {src = me.me; dst = me.me; msg = NullMsg};
        | _ -> send_action_wrapper {src = me.me; dst = me.me; msg = NullMsg}

let node_run () = 
    let counter = ref 0 in
    let lstate = get_lstate "node_run" in
    let me = lstate in
    let _ = tryrecv_action_wrapper () in
    aux lstate;
    (* let _ = tryrecv_action_wrapper () in *)
    (* let _ = tryrecv_action_wrapper () in *)
    let _ = tryrecv_action_wrapper () in
    while !counter<10 do 
        (* send_action_wrapper {src = me.me; dst = {ip = "127.0.0.1"; port = 9003}; msg = DataMsg "Hello"}; *)
        Unix.sleep 1;
        let _ = tryrecv_action_wrapper () in 
        counter:= !counter+1; 
    done