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

(* Number of nodes *)
Parameter N : nat.

(* Network semantics *)
Definition PacketSoup := seq Packet.

Definition StateMap := union_map [ordType of nid] State.
Definition initState : StateMap :=
foldr (PCM.join) (0 \\-> Init 0) (map (fun i => i \\-> Init i) (iota 1 N)).

Record World :=
  mkW {
    localState : StateMap;
    inFlightMsgs : PacketSoup;
    consumedMsgs : PacketSoup;
  }.

Definition initWorld := mkW initState [::] [::].

(* Don't you worry about uniqueness of the messages? *)
Inductive system_step (w w' : World) : Prop :=
| Idle of w = w'

| Deliver (p : Packet) (st : State) of
      p \in inFlightMsgs w &
      find (dst p) (localState w) = Some st &
      let: (st', ms) := procMsg st (msg p) in
      w' = mkW (upd (dst p) st' (localState w))
               (ms ++ seq.rem p (inFlightMsgs w))
               (rcons (consumedMsgs w) p)

| Intern (proc : nid) (t : InternalTransition) (st : State) of
      find proc (localState w) = Some st &
      let: (st', ms) := procInt st t in
      w' = mkW (upd proc st' (localState w))
               (ms ++ (inFlightMsgs w))
               (consumedMsgs w).

Definition system_step_star := clos_refl_trans_n1 _ system_step.

Definition reachable (w w' : World) := system_step_star w w'.

(* TODO: define a relation that "reconstructs" an "ideal" blockchain *)
(* from a given world, and prove its properties (e.g., functionality, *)
(* meaning that one world corresponds to one blobkchain *)
(* precisely). This might require to state additional "coherence" *)
(* properties of the world, such as block-trees of the majority of
involved peers are not _too different_. *)

Definition holds (n : nid) (w : World) (cond : State -> Prop) :=
  forall (st : State),
    find n (localState w) = Some st -> cond st.

Definition Coh (w : World) :=
  forall (n : nid),
    (* IDs match *)
    holds n w (fun st => id st == n).

Lemma Coh_init : Coh initWorld.
Proof.
rewrite /Coh /holds. move=> n st.
move=> fW. specialize (find_some fW)=> dW.
rewrite /initWorld /initState /localState in dW.
Search "um_findPt_inv".
Admitted.