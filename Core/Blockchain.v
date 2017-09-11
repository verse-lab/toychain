From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding.
Require Import SeqFacts.
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

Axiom btExtend_comm :
  forall (bt : BlockTree) (b1 b2 : Block),
    btExtend (btExtend bt b1) b2 = btExtend (btExtend bt b2) b1.

Lemma btExtend_fold_comm :
  forall (bt : BlockTree) (bs bs' : seq Block),
    foldl btExtend (foldl btExtend bt bs) bs' =
    foldl btExtend (foldl btExtend bt bs') bs.
Proof.
move=>bt bs bs'.
elim/last_ind: bs'=>[|xs x Hi]/=; first done.
rewrite -cats1 !foldl_cat Hi=>/=; clear Hi.
elim/last_ind: bs=>[|ys y Hi]/=; first done.
by rewrite -cats1 !foldl_cat -Hi/=; apply btExtend_comm.
Qed.

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

Axiom btExtend_sameOrBetter :
  forall (bt : BlockTree) (b : Block),
    btChain (btExtend bt b) >= btChain bt.

Lemma btExtend_fold_sameOrBetter:
  forall (bt :BlockTree) (bs : seq Block),
    btChain (foldl btExtend bt bs) >= btChain bt.
Proof.
move=>bt bs; elim/last_ind: bs=>[|xs x Hi]/=; first by left.
rewrite -cats1 foldl_cat /=.
(have: (btChain (btExtend (foldl btExtend bt xs) x)
       >= btChain (foldl btExtend bt xs)) by apply btExtend_sameOrBetter)=>H.
case: Hi; case: H.
by move=>->->; left.
by move=>H1 H2; rewrite H2 in H1; right.
by move=>->; right.
by move=>H1 H2; move: (CFR_trans H1 H2); right.
Qed.

(* monotonicity of (btChain (foldl btExtend bt bs)) wrt. bs *)
Lemma btExtend_monotone_btChain :
  forall (bs ext : seq Block) (bt : BlockTree),
    btChain (foldl btExtend bt (bs ++ ext)) >= btChain (foldl btExtend bt bs).
Proof.
move=>bs ext bt; elim/last_ind: ext=>[|xs x H]/=.
by rewrite foldl_cat; left.
rewrite -cats1.
(* Behold this monstrosity, thankfully handled by rewrite !foldl_cat *)
move: (btExtend_fold_sameOrBetter (foldl btExtend bt (bs ++ xs)) [:: x])=>H'.
case: H; case: H'; rewrite !foldl_cat.
by move=>->->; left.
by move=>H1 H2; rewrite H2 in H1; right.
by move=>->; right.
by move=>H1 H2; move: (CFR_trans H1 H2); right.
Qed.

Lemma btExtend_not_worse :
  forall (bt : BlockTree) (b : Block),
    ~ (btChain bt > btChain (btExtend bt b)).
Proof.
move=>bt b; move: (btExtend_sameOrBetter bt b); case.
by move=>->; apply: (CFR_nrefl).
move=>H; case X: (btChain bt > btChain (btExtend bt b)); last done.
by move: (CFR_nrefl (CFR_trans H X)).
Qed.

Lemma btExtend_fold_not_worse :
  forall (bt : BlockTree) (bs : seq Block),
    ~ (btChain bt > btChain (foldl btExtend bt bs)).
Proof.
move=>bt bs; case: (btExtend_fold_sameOrBetter bt bs).
by move=><-; apply: CFR_nrefl.
by apply: CFR_excl.
Qed.

Lemma btExtend_seq_same :
  forall (bt : BlockTree) (b : Block) (bs : seq Block),
    b \in bs -> btChain bt = btChain (foldl btExtend bt bs) ->
    btChain bt = btChain (btExtend bt b).
Proof.
move=>bt b bs H1.
move: (in_seq H1)=>[bf] [af] H2; rewrite H2.
move=>H; clear H1 H2.
move: (btExtend_fold_sameOrBetter bt [:: b])=>H1.
case: H1; first by move/eqP; rewrite eq_sym=>/eqP.
rewrite -cat1s in H.
by move=>/=Con; rewrite H in Con; clear H; contradict Con;
   rewrite foldl_cat btExtend_fold_comm foldl_cat /= -foldl_cat;
   apply btExtend_fold_not_worse.
Qed.

Lemma btExtend_seq_sameOrBetter :
  forall (bt : BlockTree) (b : Block) (bs : seq Block),
    b \in bs -> btChain bt >= btChain (foldl btExtend bt bs) ->
    btChain bt >= btChain (btExtend bt b).
Proof.
move=>bt b bs H1; case.
by move=>H2; left; apply (btExtend_seq_same H1 H2).
by move=>Con; contradict Con; apply btExtend_fold_not_worse.
Qed.

Lemma btExtend_seq_sameOrBetter_fref :
  forall (bc : Blockchain) (bt : BlockTree) (b : Block) (bs : seq Block),
    b \in bs -> bc >= btChain bt ->
    bc >= btChain (foldl btExtend bt bs) ->
    bc >= btChain (btExtend bt b).
Proof.
move=> bc bt b bs H HGt HGt'.
move: (in_seq H)=>[bf] [af] H'; rewrite H' in HGt'; clear H H'.
move: (btExtend_sameOrBetter bt b)=>H.
move: (btExtend_fold_sameOrBetter bt (bf ++ b :: af)).
rewrite -cat1s foldl_cat btExtend_fold_comm foldl_cat /= -foldl_cat in HGt' *.
move=>H'; case: HGt; case: HGt'; case: H; case: H'; move=>h0 h1 h2 h3.
- by left; rewrite h1 h3.
- by rewrite h3 in h2; rewrite h2 in h0; contradict h0; apply: CFR_nrefl.
- by rewrite -h0 in h1; contradict h1; apply btExtend_fold_not_worse.
- by rewrite -h2 h3 in h0; contradict h0; apply: CFR_nrefl.
- by left; apply/eqP; rewrite eq_sym; rewrite -h3 in h1; apply/eqP.
- by rewrite -h3 in h1; rewrite -h1 in h2;
  contradict h2; apply btExtend_fold_not_worse.
- by rewrite -h3 in h0; rewrite h0 in h2; contradict h2; apply: CFR_nrefl.
- by rewrite h3 in h2; move: (CFR_trans h0 h2)=>C;
  contradict C; apply: CFR_nrefl.
- by right; rewrite h1.
- by right; rewrite h1.
- by rewrite -h0 in h1; contradict h1; apply btExtend_fold_not_worse.
- by subst bc; apply btExtend_fold_sameOrBetter.
- by right; rewrite -h1 in h3.
- by right; rewrite -h1 in h3.
- rewrite -h0 in h1; contradict h1; apply btExtend_fold_not_worse.
have: (btChain (foldl btExtend (btExtend bt b) (af ++ bf))
        >= btChain (btExtend bt b)) by apply: btExtend_fold_sameOrBetter.
case=>[|H].
by move=><-; right.
by right; move: (CFR_trans h2 H).
Qed.

Axiom btExtend_withNew_mem :
  forall (bt : BlockTree) (b : Block),
    let bc := btChain bt in
    let: bc' := btChain (btExtend bt b) in
    b \notin bc ->
    bc != bc' = (b \in bc').

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