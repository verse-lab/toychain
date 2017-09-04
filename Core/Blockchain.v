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
Definition Timestamp := nat.

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

(* We might want to introduce a notion of time *)
Parameter VAF : VProof -> Timestamp -> Blockchain -> bool.

Parameter stake : Address -> Blockchain -> Stake.
Parameter genProof : Stake -> option VProof.

Parameter blockValid : Block -> Blockchain -> bool.

Parameter CFR_gt : Blockchain -> Blockchain -> bool.
Notation "A > B" := (CFR_gt A B).
Notation "A >= B" := (A = B \/ A > B).

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

Fixpoint bcPrev (b : Block) (bc : Blockchain) : Block :=
  match bc with
  | [::] => GenesisBlock
  | prev :: ((b' :: bc') as bcc) =>
    if b' == b then prev else bcPrev b bcc
  | _ :: bc' => bcPrev b bc'
  end.

Fixpoint bcSucc (b : Block) (bc : Blockchain) : option Block :=
  match bc with
  | [::] => None
  | b' :: ((succ :: bc') as bcc) =>
    if b' == b then Some succ else bcSucc b bcc
  | _ :: bc' => bcSucc b bc'
  end.

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

Axiom VAF_inj :
  forall (v v' : VProof) (ts : Timestamp) (bc1 bc2 : Blockchain),
    VAF v ts bc1 -> VAF v' ts bc2 -> v == v' /\ bc1 == bc2.

Axiom CFR_ext :
  forall (bc : Blockchain) (b : Block) (ext : seq Block),
    bc ++ (b :: ext) > bc.

Axiom CFR_nrefl :
  forall (bc : Blockchain), bc > bc -> False.

Axiom CFR_trans :
  forall (A B C : Blockchain),
    A > B -> B > C -> A > C.

Lemma CFR_excl :
  forall (bc bc' : Blockchain),
    bc > bc' -> bc' > bc -> False.
Proof.
by move=>bc bc' H1 H2; move: (CFR_trans H1 H2); apply CFR_nrefl.
Qed.

Axiom btChain_mem :
  forall (bt : BlockTree) (b : Block),
    b \notin bt -> b \notin btChain bt.

Axiom btChain_mem2 :
  forall (bt : BlockTree) (b : Block),
    b \in btChain bt -> b \in bt.

Axiom btChain_seq :
  forall (bt : BlockTree) (bc : Blockchain),
    btChain bt = bc ->
    forall (b : Block),
      b != GenesisBlock ->
      b \in bc == (prevBlockHash b == hashB (bcPrev b bc)).

Axiom btChain_extend :
  forall (bt : BlockTree) (b extension : Block),
    let bc := (btChain bt) in
    b \notin bc ->
    prevBlockHash extension == hashB (bcLast bc) ->
    btChain (btExtend bt b) = rcons bc extension.

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

Axiom btExtend_withNew_mem :
  forall (bt : BlockTree) (b : Block),
    let bc := btChain bt in
    let: bc' := btChain (btExtend bt b) in
    b \notin bc ->
    bc != bc' = (b \in bc').

Lemma btExtend_not_worse :
  forall (bt : BlockTree) (b : Block),
    ~ (btChain bt > btChain (btExtend bt b)).
Proof.
move=>bt b; case H: (b \in bt).
by move: (btExtend_withDup_noEffect H)=><-; apply: CFR_nrefl.
have: (btChain (btExtend bt b) > btChain bt).
move/negP/negP in H; move: (btExtend_withNew_sameOrBetter H)=><-.
move: (btExtend_withNew_mem (btChain_mem H))=><-.
(* This is essentially a new axiom; it's probably time to just write
    a blocktree implementation and prove these facts about it.
 *)
Admitted.

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

(* Caller must ensure bc' is longer *)
Definition bc_diff (bc bc' : Blockchain) := [seq b <- bc' | b \notin bc].

(* Facts *)
Lemma bc_succ_mem b bc:
  forall (sb : Block),
    (bcSucc b bc = Some sb) ->
    (b \in bc) = true /\ (sb \in bc) = true.
Proof.
elim: bc=>[|h t Hi]/=; do? by [].
move=> sb. specialize (Hi sb). case E: (h == b); last first.
case: {1}t.
- move=>Ex. move: (Hi Ex). elim. move=> bbc sbbc. clear Hi Ex. split.
  by rewrite in_cons bbc; apply Bool.orb_true_r.
  by rewrite in_cons sbbc; apply Bool.orb_true_r.
- move=>_ _ Ex. move: (Hi Ex). elim. move=> bbc sbbc. clear Hi Ex. split.
  by rewrite in_cons bbc; apply Bool.orb_true_r.
  by rewrite in_cons sbbc; apply Bool.orb_true_r.
case: t Hi; do? by [].
move=> succ tail Hi eq. case: eq=>eq. rewrite -eq in Hi. split.
 + by rewrite in_cons; move/eqP in E; rewrite E eq_refl; apply Bool.orb_true_l.
 + by rewrite eq; rewrite !in_cons; rewrite eqxx=>/=; apply Bool.orb_true_r.
Qed.