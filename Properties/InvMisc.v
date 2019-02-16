From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Protocol Chains Parameters Forests States Network.
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

Definition has_bt (bt : BlockTree) (st : State) : Prop :=
  (blockTree st) == bt.

Definition valid_with_bc bt bc :=
  [/\ valid bt, validH bt & has_init_block bt] /\
   bc = btChain bt.

Definition exists_and_holds (n : Address) (w : World) (cond : State -> Prop) :=
  exists (st : State),
    find n (localState w) = Some st /\ cond st.

Definition chain_sync_agreement (w w' : World) :=
  forall (n n' : Address) (bc bc' : Blockchain),
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
   forall (n' : Address) (bc' : Blockchain),
    holds n' w (fun st => has_chain bc' st -> bc >= bc').

Definition GStable w :=
  inFlightMsgs w = [::] /\
  exists (bc : Blockchain), forall (n : Address),
      holds n w (has_chain bc).

(* Definition all_available (n : Address) (w : World) : seq Block := *)
(*   let inv_hashes := *)
(*     flatten [seq msg_hashes (msg p) | *)
(*              p <- inFlightMsgs w & (dst p == n) && (msg_type (msg p) == MInv)] in *)
(*   let gds_hashes := *)
(*       flatten [seq msg_hashes (msg p) | *)
(*                p <- inFlightMsgs w & *)
(*                [&& (src p == n), *)
(*                 (msg_type (msg p) == MGetData) & *)
(*                 (n \in msg_from (msg p))]] in   *)
(*   undup (invs ++ gds). *)

(* Definition available b n w := hashB b \in all_available n w. *)

(*
* For simplicity, we assume all nodes are directly connected.
* This could be changed to incorporate a more realistic broadcast setting.
*)
Definition available_rel (b : Block) (n : Address) (w : World) :=
  exists (p : Packet),
    p \in inFlightMsgs w /\
    [\/ exists (peer : Address) (sh : seq Hash),
         msg p = InvMsg sh /\ dst p = n /\ hashB b \in sh |
       exists (hash : Hash),
         msg p = GetDataMsg hash /\ src p = n /\ hashB b = hash
    ].

Definition block_for_hash n (w : World) (h : Hash) : Block :=
  if find n (localState w) is Some l
  then if find h (blockTree l) is Some b
       then b else GenesisBlock
  else GenesisBlock.
                                            


(* Lemma availableP b n w : *)
(*   reflect (available_rel b n w) (available b n w). *)
(* Proof. *)
(* case A: (available b n w); [constructor 1 | constructor 2]; move: A; *)
(* rewrite/available/all_available mem_undup -flatten_cat. *)
(* move/flattenP; case=>h0; rewrite mem_cat; move/orP; case; *)
(* move/mapP; case=>p0; rewrite mem_filter; rewrite/available_rel. *)
(* - move/andP=>[]/andP[] H1 H2 H3 H4 H5; *)
(*   exists p0; split; first done. *)
(*   case Msg: (msg p0)=>[|||||pr sh|]; do? by contradict H2; rewrite/msg_type Msg. *)
(*   left. exists pr, sh. split; first done. split; first by move/eqP in H1. *)
(*   by move: H5; rewrite H4 /msg_hashes Msg. *)
(* - move/andP=>[]/andP[]/andP[] H1 H2 H3 H4 H5 H6; *)
(*   exists p0; split; first done. *)
(*   case Msg: (msg p0)=>[||||||pr h]; do? by contradict H2; rewrite/msg_type Msg. *)
(*   right. exists h. split. *)
(*   by move: H3; rewrite /msg_from Msg mem_seq1; move/eqP=><-. *)
(*   split. *)
(*   by move/eqP in H1. *)
(*   by move: H6; rewrite H5 /msg_hashes Msg mem_seq1; move/eqP. *)
(* (* available b n w = false *) *)
(* move/flattenP. apply impliesPn; constructor. *)
(* case=>p [] iF; case. *)
(* - move=>[pr] [sh] [H1] [H2] H3. exists sh; last done. *)
(*   rewrite mem_cat; apply/orP. left. *)
(*   apply/mapP. exists p. rewrite mem_filter; apply/andP; split; last done. *)
(*   apply/andP; split; by [move/eqP in H2 | rewrite/msg_type H1]. *)
(*   by rewrite /msg_hashes H1. *)
(* - move=>[hash] [H1] [H2] H3. exists [:: hash]; last first. *)
(*   by rewrite mem_seq1; move/eqP in H3. *)
(*   rewrite mem_cat; apply/orP. right. *)
(*   apply/mapP. exists p. rewrite mem_filter; apply/andP; split; last done. *)
(*   apply/andP; split. *)
(*     apply/andP; split; by [move/eqP in H2 | rewrite/msg_type H1]. *)
(*     by rewrite/msg_from H1 mem_seq1. *)
(*   by rewrite /msg_hashes H1. *)
(* Qed. *)

(* Definition availableFor n w := *)
(*   undup [seq msg_block (msg p) | p <- inFlightMsgs w & *)
(*                                  dst p == n && *)
(*                                  available (msg_block (msg p)) n w]. *)

