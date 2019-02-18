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
Parameter Timestamp : Set.
Parameter Hash : Set.
Parameter VProof : Set.
Parameter Transaction : Set.

(* These need to be types that can be coerced into ordType *)
Axiom Hash_eqMixin : Equality.mixin_of Hash.
Canonical Hash_eqType := Eval hnf in EqType Hash Hash_eqMixin.
Axiom Hash_ordMixin : Ordered.mixin_of Hash_eqType.
Canonical Hash_ordType := Eval hnf in OrdType Hash Hash_ordMixin.

Axiom VProof_eqMixin : Equality.mixin_of VProof.
Canonical VProof_eqType := Eval hnf in EqType VProof VProof_eqMixin.
Axiom VProof_ordMixin : Ordered.mixin_of VProof_eqType.
Canonical VProof_ordType := Eval hnf in OrdType VProof VProof_ordMixin.

Axiom Transaction_eqMixin : Equality.mixin_of Transaction.
Canonical Transaction_eqType := Eval hnf in EqType Transaction Transaction_eqMixin.
Axiom Transaction_ordMixin : Ordered.mixin_of Transaction_eqType.
Canonical Transaction_ordType := Eval hnf in OrdType Transaction Transaction_ordMixin.


Definition block := @Block [ordType of Hash] [ordType of Transaction] [ordType of VProof].
Parameter GenesisBlock : block.

Definition Blockchain := seq block.
Definition bcLast (bc : Blockchain) := last GenesisBlock bc.
Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

Definition TxPool := seq Transaction.
(* In fact, it's a forest, as it also keeps orphan blocks *)
Definition BlockTree := union_map [ordType of Hash] block.


Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.
Notation "# b" := (hashB b) (at level 20).

Parameter genProof : Blockchain -> TxPool -> Timestamp -> option (TxPool * VProof).
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
