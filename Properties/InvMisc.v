From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Protocol Types Chains Parameters Forests States Network Address.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************************************************************)
(* Miscellaneous definitions for blockchain system invariants.     *)
(*******************************************************************)

(* Invariants of the execution regarding the blockchain *)
(* Properties *)

Module Type InvProps (T : Types) (P : ConsensusParams T) (F : Forest T P) (A : NetAddr)
                     (Pr : ConsensusProtocol T P F A) (Ns : NetState T P F A Pr)
                     (C : ConsensusNetwork T P F A Pr Ns).
Import T P F A Pr Ns C.

Definition has_chain (bc : Blockchain) (st : State) : Prop :=
  btChain (blockTree st) == bc.

Definition has_bt (bt : BlockTree) (st : State) : Prop :=
  (blockTree st) == bt.

Definition valid_with_bc bt bc :=
  [/\ valid bt, validH bt & has_init_block bt] /\
   bc = btChain bt.

Definition blocksFor n w :=
  [seq msg_block (msg p) | p <- inFlightMsgs w & dst p == n].

Lemma b_in_blocksFor p b w :
    p \in inFlightMsgs w -> (msg p = BlockMsg b) -> b \in blocksFor (dst p) w.
Proof.
move=>iF Msg.
rewrite/blocksFor; apply/mapP; exists p.
by rewrite mem_filter eqxx.
by rewrite/msg_block Msg.
Qed.

Definition largest_chain (w : World) (bc : Blockchain) :=
   forall (n' : Address) (bc' : Blockchain),
    holds n' w (fun st => has_chain bc' st -> bc >= bc').

Definition GStable w :=
  inFlightMsgs w = [::] /\
  exists (bc : Blockchain), forall (n : Address),
      holds n w (has_chain bc).
End InvProps.

Module InvMisc (T : Types) (P : ConsensusParams T) (F : Forest T P) (A : NetAddr)
                     (Pr : ConsensusProtocol T P F A) (Ns : NetState T P F A Pr)
                     (C : ConsensusNetwork T P F A Pr Ns)
                        <: InvProps T P F A Pr Ns C.
Import T P F A Pr Ns C.

Definition has_chain (bc : Blockchain) (st : State) : Prop :=
  btChain (blockTree st) == bc.

Definition has_bt (bt : BlockTree) (st : State) : Prop :=
  (blockTree st) == bt.

Definition valid_with_bc bt bc :=
  [/\ valid bt, validH bt & has_init_block bt] /\
   bc = btChain bt.

Definition blocksFor n w :=
  [seq msg_block (msg p) | p <- inFlightMsgs w & dst p == n].

Lemma b_in_blocksFor p b w :
    p \in inFlightMsgs w -> (msg p = BlockMsg b) -> b \in blocksFor (dst p) w.
Proof.
move=>iF Msg.
rewrite/blocksFor; apply/mapP; exists p.
by rewrite mem_filter eqxx.
by rewrite/msg_block Msg.
Qed.

Definition largest_chain (w : World) (bc : Blockchain) :=
   forall (n' : Address) (bc' : Blockchain),
    holds n' w (fun st => has_chain bc' st -> bc >= bc').

Definition GStable w :=
  inFlightMsgs w = [::] /\
  exists (bc : Blockchain), forall (n : Address),
      holds n w (has_chain bc).
End InvMisc.