From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
From fcsl
Require Import ordtype unionmap.
From Toychain
Require Import Blocks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(************************************************************)
(******************* <parameters> ***************************)
(************************************************************)
Module Type ConsensusParams.
Parameter Timestamp : Type.
Parameter Hash : ordType.
Parameter VProof : eqType.
Parameter Transaction : eqType.
Parameter Address : finType.

Definition block := @Block Hash Transaction VProof.
Parameter GenesisBlock : block.

Definition Blockchain := seq block.
Definition bcLast (bc : Blockchain) := last GenesisBlock bc.
Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

Definition TxPool := seq Transaction.
(* In fact, it's a forest, as it also keeps orphan blocks *)
Definition BlockTree := union_map Hash block.


Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.
Notation "# b" := (hashB b) (at level 20).

Parameter genProof : Address -> Blockchain -> TxPool -> Timestamp -> option (TxPool * VProof).
Parameter VAF : block -> Blockchain -> TxPool -> bool.

Parameter FCR : Blockchain -> Blockchain -> bool.
Notation "A > B" := (FCR A B).
Notation "A >= B" := (A = B \/ A > B).

Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.

(************************************************************)
(*********************** <axioms> ***************************)
(************************************************************)

Axiom txValid_nil : forall t, txValid t [::].

(** VAF **)
Axiom VAF_init : VAF GenesisBlock [::] (txs GenesisBlock).

Axiom VAF_GB_first :
  forall bc, VAF GenesisBlock bc (txs GenesisBlock) -> bc = [::].


(** FCR **)
Axiom FCR_subchain :
  forall bc1 bc2, subchain bc1 bc2 -> bc2 >= bc1.

(* TODO: strengthen to only valid chains *)
Axiom FCR_ext :
  forall (bc : Blockchain) (b : block) (ext : seq block),
    bc ++ (b :: ext) > bc.

Axiom FCR_rel :
  forall (A B : Blockchain),
    A = B \/ A > B \/ B > A.

Axiom FCR_nrefl :
  forall (bc : Blockchain), bc > bc -> False.

Axiom FCR_trans :
  forall (A B C : Blockchain), A > B -> B > C -> A > C.
End ConsensusParams.
