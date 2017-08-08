From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Relations.
Require Import Protocol Blockchain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Network semantics *)
Definition PacketSoup := seq Packet.

Definition StateMap := union_map [ordType of nid] State.

Record World :=
  mkW {
    localState : StateMap;
    inFlightMsgs : PacketSoup;
    trace : seq Event;
    }.

Parameter initState : StateMap.
Definition initWorld := mkW initState [::] [::].

Inductive reliable_step (w w' : World) : Prop :=
| Idle of w = w'

| Deliver (p : Packet) (st st' : State) (ms : ToSend) (evs : seq Event) of
      p \in inFlightMsgs w &
      p != NullPacket &
      find (dst p) (localState w) = Some st &
      procMsg st (msg p) = (st', ms, evs) &
      w' = mkW (upd (dst p) st' (localState w))
               (ms ++ seq.rem p (inFlightMsgs w))
               (trace w ++ evs)

| Intern (proc : nid) (t : InternalTransition) (st st' : State) (ms : ToSend) of
      find proc (localState w) = Some st &
      procInt st t = (st', ms) &
      w' = mkW (upd proc st' (localState w))
               (ms ++ (inFlightMsgs w))
               [::].

Definition reliable_step_star := clos_refl_trans_n1 _ reliable_step.

Definition reachable (w w' : World) := reliable_step_star w w'.