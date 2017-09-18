From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap.
Require Import Blockchain Protocol Semantics States BlockchainProperties SeqFacts.
Require Import InvMisc.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section InvAvailable.

(**********************************************************************)
(* Global Invariant 3: Local Eventual Consensus. *)

(* Every immediate peer n' of a to-date canonical blockchain, once all
   available and in-flight blocks are applied, get exactly the 
   canonical blockchain as well.                                      *)
(**********************************************************************)


(* TODO: instantiate *)
Variable available_blocks : forall (n : nid) (w : World), seq Block.

Definition GSyncing_local w :=
  exists (bc : Blockchain) (n : nid),
  [/\ holds n w (has_chain bc),

   (* The canonical chain is the largest in the network *)
   largest_chain w bc &

   (* Applying blocks in flight will induce either the canonical
      chain or a smaller one. *)
   forall n',
     holds n w (fun st => n' \in peers st) ->
     holds n' w (fun st =>
     let bc_blocks := foldl btExtend (blockTree st) (blocksFor n' w) in
     let bc_available := btChain (foldl btExtend bc_blocks
                                        (available_blocks n' w)) in
     bc = bc_available)].

End InvAvailable.