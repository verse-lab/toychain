From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
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
    }.

Inductive reliable_step (w w' : World) : Prop :=
| Idle of w = w'

| Deliver (p : Packet) (st st' : State) (ms : ToSend) of
      p \in inFlightMsgs w &
      find (dst p) (localState w) = Some st &
      procMsg st (msg p) = (st', ms) &
      w' = mkW (upd (dst p) st' (localState w))
               (ms ++ seq.rem p (inFlightMsgs w))

| Intern (proc : nid) (t : InternalTransition) (st st' : State) (ms : ToSend) of
      find proc (localState w) = Some st &
      procInt st t = (st', ms) &
      w' = mkW (upd proc st' (localState w))
               (ms ++ (inFlightMsgs w)).
