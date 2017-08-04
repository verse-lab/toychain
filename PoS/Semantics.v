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
    consumedMsgs : PacketSoup;
    }.

(* [Ilya] You might want not to remove the in-flight message, but *)
(* rather move them into a separate part of the world ("thrash-pile"). *)
(* This will give you the history information, which you need in order *)
(* to state the execution invariants, involving complex interactions *)
(* involving multiple message exchanges. so I've added this as a
component. *)

(* Also, don't you worry about uniqueness of the messages? *)

Inductive system_step (w w' : World) : Prop :=
| Idle of w = w'

| Deliver (p : Packet) (st st' : State) (ms : ToSend) of
      p \in inFlightMsgs w &
      find (dst p) (localState w) = Some st &
      procMsg st (msg p) = (st', ms) &
      w' = mkW (upd (dst p) st' (localState w))
               (ms ++ seq.rem p (inFlightMsgs w))
               (rcons (consumedMsgs w) p)

| Intern (proc : nid) (t : InternalTransition) (st st' : State) (ms : ToSend) of
      find proc (localState w) = Some st &
      procInt st t = (st', ms) &
      w' = mkW (upd proc st' (localState w))
               (ms ++ (inFlightMsgs w))
               (consumedMsgs w).

(* TODO: define a relation that "reconstructs" an "ideal" blockchain *)
(* from a given world, and prove its properties (e.g., functionality, *)
(* meaning that one world corresponds to one blobkchain *)
(* precisely). This might require to state additional "coherence" *)
(* properties of the world, such as block-trees of the majority of
involved peers are not _too different_. *)

(* What is the initial state of the system? *)