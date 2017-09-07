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
Definition Hash := [ordType of nat].

Parameter Stake : eqType.
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


(*****************************
 *  BlockTree implementation *
 *****************************)

(* Also keeps orphan blocks *)
Definition BlockTree := union_map Hash Block.
Definition btHasBlock (bt : BlockTree) (b : Block) := hashB b \in dom bt.

(* How can we assert there are no cycles? *)
Definition btExtend :=
  fun (bt : BlockTree) (b : Block) => bt \+ (hashB b \\-> b).

(* How to show this terminates?
 * Sylvain suggested removing top from bt before passing it
 *  into the recursive call. Not sure if it will work.
 *)

Section BlockTreeProperties.

Variable bt: BlockTree.

(* b' is the previous of b in bt *)
Definition is_prev_in b : pred Block :=
  [pred b' | (hashB b' == prevBlockHash b) && (hashB b' \in dom bt)].

(* Genesis block is in the beginning *)
(* Are these basic conditions *)
Definition is_valid_chain_from b bc : Prop :=
  [/\ path is_prev_in b bc,
   (exists bc', bc = rcons bc' GenesisBlock) &
   uniq (map hashB bc)].

(* Fixpoint build_chain_from b := *)
  

(* Now state what does it mean for a BlockTree to be valid:

- define a total function (non-option-retur) to get a chain from a block

- establish that for any block in BT its chain is valid

 *)

Definition valid_bt : Prop :=
  [/\ find (hashB GenesisBlock) bt = Some (GenesisBlock),
   forall h b, find h bt = Some b -> h = hashB b &
   (* TODO: Add more *)                                  
   True                                  
  ].

End BlockTreeProperties.


Fixpoint _chain_from' (bt : BlockTree) (cur : Block) (n : nat) :
  option Blockchain :=
  match find (prevBlockHash cur) bt with
  | None => None
  | Some prev =>
    if n is n'.+1 then
      (* It's not really important whether you remove top or not
           since you only give some constant amount of "fuel" to your function. *)
      let pv := _chain_from' (free (hashB cur) bt) prev n' in
      (* let pv := _chain_from' bt prev n' in *)
      match pv with
      | None => None
      | Some chain => Some (rcons chain prev)
      end
    else None (* Out of fuel *)
  end.

Definition _chain_from bt cur :=
  if cur == GenesisBlock
  then Some [:: cur] 
  else match _chain_from' bt cur (size (keys_of bt)) with
       | None => None
       | Some chain => (Some (rcons chain cur))
       end.

(* You will probably need to assert that there is no cycles in this, *)
(* i.e., BlockTree is a tree -- let me know if you need help with
   this. *)
   

(* btChain:
 *  - find all possible tops: ~ exists b, b \in bt -> prevBlockHash b == top
 *  - compute _chain_from all tops
 *  - return greatest such chain (according to CFR)
 *)

Parameter btChain : BlockTree -> BlockChain.

(**************************
 *  TxPool implementation *
 **************************)
Definition TxPool := seq Transaction.

(* Transaction is valid and consistent with the given chain. *)
Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.



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

Axiom btExtend_btChain_not_worse :
  forall (bt : BlockTree) (b : Block),
    ~ (btChain bt > btChain (btExtend bt b)).

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