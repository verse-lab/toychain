From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A fomalization of a blockchain structure *)
Definition Hash := nat.
Definition VProof := nat.
Definition Transaction := nat.

Record Block :=
  mkB {
    prevBlockHash : Hash;
    txs : seq Transaction;
    proof : VProof;
  }.

Parameter hashB : Block -> Hash.
Definition eq_block b b' := hashB b == hashB b'.

Definition Blockchain := seq Block.

(* We might want to introduce a notion of time *)
Parameter VAF : VProof -> Blockchain -> bool.
Parameter blockValid : Block -> Blockchain -> bool.

Parameter CFR_gt : Blockchain -> Blockchain -> bool.
Notation "A > B" := (CFR_gt A B).

Definition BlockTree := seq Block.

Parameter btExtend : BlockTree -> Block -> BlockTree.
Parameter btChain : BlockTree -> Blockchain.

(* Axioms *)
Axiom hashB_inj : forall (b b': Block), hashB b == hashB b' -> b = b'.

Module BlockEq.
Lemma eq_blockP : Equality.axiom eq_block.
Proof.
move=> b b'. rewrite/eq_block. apply: (iffP idP).
  - by apply: hashB_inj.
  - move=> eq. by rewrite eq.
Qed.

Canonical Block_eqMixin := Eval hnf in EqMixin eq_blockP.
Canonical Block_eqType := Eval hnf in EqType Block Block_eqMixin.
End BlockEq.
Export BlockEq.

Axiom blockValid_imp_VAF :
  forall (b : Block) (bc : Blockchain),
    (blockValid b bc) -> (VAF (proof b) bc).

(* TODO: justify the need for this *)
Axiom no_proof_reuse :
  forall (b b' : Block) (bc : Blockchain),
    b <> b' -> (blockValid b bc) -> (blockValid b' bc) ->
    (proof b) <> (proof b').

Axiom CFR_strictly_increases :
  forall (bc : Blockchain) (b : Block),
    blockValid b bc -> (bc ++ [:: b]) > bc.

Axiom btExtend_preserve :
  forall (bt : BlockTree) (ob b : Block), let: bt' := btExtend bt b in
    ob \in bt -> ob \in bt'.

Axiom btExtend_withDup_noEffect :
  forall (bt : BlockTree) (b : Block), let: bt' := btExtend bt b in
    b \in bt -> bt = bt'.

(* TODO: explain *)
Axiom btExtend_withNew_sameOrBetter :
  forall (bt : BlockTree) (b : Block), let: bt' := btExtend bt b in
    b \notin bt ->
      (b \in (btChain bt') <-> (btChain bt') > (btChain bt)).
