From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A fomalization of a blockchain structure *)

Definition Address := nat.

Parameter Stake : eqType.
Parameter Hash : eqType.
Parameter VProof : eqType.
Parameter Transaction : eqType.
Parameter hashT : Transaction -> Hash.
Definition eq_tx t t' := hashT t == hashT t'.

Record Block :=
  mkB {
    height : nat;
    prevBlockHash : Hash;
    txs : seq Transaction;
    proof : VProof;
  }.
Parameter GenesisBlock : Block.

Parameter hashB : Block -> Hash.
Definition eq_block b b' := hashB b == hashB b'.

Definition Blockchain := seq Block.

Definition bcLast (bc : Blockchain) := last GenesisBlock bc.
Fixpoint bcPrev (b : Block) (bc : Blockchain) : Block :=
  match bc with
  | [::] => GenesisBlock
  | prev :: (b :: bc') => prev
  | _ :: bc' => bcPrev b bc'
  end.

Fixpoint bcSucc (b : Block) (bc : Blockchain) : option Block :=
  match bc with
  | [::] => None
  | b :: (succ :: bc') => Some succ
  | _ :: bc' => bcSucc b bc'
  end.

(* We might want to introduce a notion of time *)
Parameter VAF : VProof -> Blockchain -> bool.

Parameter stake : Address -> Blockchain -> Stake.
Parameter genProof : Stake -> option VProof.

Parameter blockValid : Block -> Blockchain -> bool.

Parameter CFR_gt : Blockchain -> Blockchain -> bool.
Notation "A > B" := (CFR_gt A B).

(* Also keeps orphan blocks *)
Definition BlockTree := seq Block.

Parameter btExtend : BlockTree -> Block -> BlockTree.
Parameter btChain : BlockTree -> Blockchain.

Definition TxPool := seq Transaction.

(* Transaction is valid and consistent with the given chain. *)
Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.

(* Axioms *)
(* Is it realistic? *)
Axiom hashB_inj : injective hashB.
Axiom hashT_inj : injective hashT.
Axiom hashBT_noCollisions :
  forall (b : Block) (t : Transaction), hashB b != hashT t.

Module BlockEq.
Lemma eq_blockP : Equality.axiom eq_block.
Proof.
move=> b b'. rewrite/eq_block. apply: (iffP idP).
- by move/eqP; apply: hashB_inj.
  - move=> eq. by rewrite eq.
Qed.

Canonical Block_eqMixin := Eval hnf in EqMixin eq_blockP.
Canonical Block_eqType := Eval hnf in EqType Block Block_eqMixin.
End BlockEq.
Export BlockEq.

Module TxEq.
Lemma eq_txP : Equality.axiom eq_tx.
Proof.
move=> t t'. rewrite/eq_tx. apply: (iffP idP).
  - by move/eqP; apply: hashT_inj.
  - by move=> eq; rewrite eq.
Qed.

Canonical Tx_eqMixin := Eval hnf in EqMixin eq_txP.
Canonical Tx_eqType := Eval hnf in EqType Transaction Tx_eqMixin.
End TxEq.
Export TxEq.

Definition fork (bc bc' : Blockchain) : Prop :=
  exists (b : Block),
    bcSucc b bc != bcSucc b bc'.

Axiom blockValid_imp_VAF :
  forall (b : Block) (bc : Blockchain),
    (blockValid b bc) -> (VAF (proof b) bc).

(* TODO: justify the need for this *)
Axiom no_proof_reuse :
  forall (b b' : Block) (bc : Blockchain),
    b != b' -> blockValid b bc -> blockValid b' bc ->
    proof b != proof b'.

Axiom VAF_inj :
  forall (v : VProof) (bc1 bc2 : Blockchain),
    VAF v bc1 -> VAF v bc2 -> bc1 == bc2.

Axiom CFR_strictly_increases :
  forall (bc : Blockchain) (b : Block),
    blockValid b bc -> rcons bc b > bc.

Axiom btChain_mem :
  forall (bt : BlockTree) (b : Block),
    b \notin bt -> b \notin btChain bt.

Axiom btChain_seq :
  forall (bt : BlockTree) (bc : Blockchain),
    btChain bt = bc ->
    forall (b : Block),
      b != GenesisBlock ->
      b \in bc == (prevBlockHash b == hashB (bcPrev b bc)).

Axiom btChain_extend :
  forall (bt : BlockTree) (bc : Blockchain) (b extension : Block),
    btChain bt = bc ->
    b \notin bc ->
    prevBlockHash extension == hashB (bcLast bc) ->
    btChain (btExtend bt b) = rcons bc extension.

Axiom btChain_fork :
  forall (bt : BlockTree) (bc : Blockchain) (b : Block),
  let: bc' := btChain (btExtend bt b) in
    btChain bt = bc ->
    b \notin bc ->
    prevBlockHash (bcLast bc') != hashB (bcLast bc) ->
    fork bc bc'.

Axiom btExtend_preserve :
  forall (bt : BlockTree) (ob b : Block),
    let: bt' := btExtend bt b in
    ob \in bt -> ob \in bt'.

Axiom btExtend_withDup_noEffect :
  forall (bt : BlockTree) (b : Block),
    let: bt' := btExtend bt b in
    b \in bt -> bt = bt'.

(* TODO: explain *)
Axiom btExtend_withNew_sameOrBetter :
  forall (bt : BlockTree) (b : Block), let: bt' := btExtend bt b in
    b \notin bt ->
      b \in btChain bt' = (btChain bt' > btChain bt).

Axiom tpExtend_validAndConsistent :
  forall (bt : BlockTree) (pool : TxPool) (tx : Transaction),
    tx \in (tpExtend pool bt tx) -> (txValid tx (btChain bt)).

Axiom tpExtend_withDup_noEffect :
  forall (bt : BlockTree) (pool : TxPool) (tx : Transaction),
    tx \in pool -> (tpExtend pool bt tx) = pool.

(* Caller must ensure bc' is longer *)
Fixpoint prefix_diff (bc bc' : Blockchain) :=
  match bc, bc' with
  | x :: xs, y :: ys => if x == y then prefix_diff xs ys else y :: ys
  | _, ys => ys
  end.
