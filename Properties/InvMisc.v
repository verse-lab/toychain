From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
From Heaps
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Protocol Chains Blocks Forests States Network.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************************************************************)
(* Miscellaneous definitions for blockchain system invariants.     *)
(*******************************************************************)

(* Invariants of the execution regarding the blockchain *)
(* Properties *)

Definition has_chain (bc : Blockchain) (st : State) : Prop :=
  btChain (blockTree st) == bc.

Definition exists_and_holds (n : nid) (w : World) (cond : State -> Prop) :=
  exists (st : State),
    find n (localState w) = Some st /\ cond st.

Definition chain_sync_agreement (w w' : World) :=
  forall (n n' : nid) (bc bc' : Blockchain),
    holds n w (has_chain bc) ->
    reachable w w' ->
    holds n' w' (has_chain bc') ->
    size bc' == size bc ->
    bc == bc'.

Lemma has_chain_func n w (bc bc' : Blockchain):
  n \in dom (localState w) ->
  holds n w (has_chain bc) ->
  holds n w (has_chain bc') -> bc = bc'.
Proof.
case/um_eta=>st[Sf]_ nbc nbc'.
by move: (nbc st Sf) (nbc' st Sf)=>/eqP<-/eqP->.
Qed.

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
   forall (n' : nid) (bc' : Blockchain),
    holds n' w (fun st => has_chain bc' st -> bc >= bc').

Definition GStable w :=
  inFlightMsgs w = [::] /\
  exists (bc : Blockchain), forall (n : nid),
      holds n w (has_chain bc).

Definition available_rel (b : Block) (n : nid) (w : World) :=
  exists (p : Packet),
    p \in inFlightMsgs w /\
    [\/ exists (peer : nid) (sh : seq Hash),
         msg p = InvMsg sh /\ dst p = n /\ hashB b \in sh |
       exists (hash : Hash),
         msg p = GetDataMsg hash /\ src p = n /\ hashB b = hash
    ].

Definition block_for_hash n (w : World) (h : Hash) : Block :=
  if find n (localState w) is Some l
  then if find h (blockTree l) is Some b
       then b else GenesisBlock
  else GenesisBlock.
                                            