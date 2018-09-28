From Toychain
Require Import Blocks Canonicals.
From mathcomp.ssreflect
Require Import ssreflect eqtype seq.
From fcsl
Require Import ordtype unionmap.

Parameter Timestamp : Type.

Definition block := @Block [ordType of Hash] Transaction_eqType [eqType of VProof].

Parameter GenesisBlock : block.

Definition Blockchain := seq block.

(* In fact, it's a forest, as it also keeps orphan blocks *)
Definition BlockTree := union_map [ordType of Hash] block.

Definition TxPool := seq Transaction.

Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.

Parameter genProof : Address -> Blockchain -> TxPool -> Timestamp -> option (TxPool * VProof).

Parameter VAF : VProof -> Blockchain -> TxPool -> bool.
Parameter FCR : Blockchain -> Blockchain -> bool.

(* Transaction is valid and consistent with the given chain *)
Parameter txValid : Transaction -> Blockchain -> bool.

Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.