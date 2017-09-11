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

Definition btHasBlock (bt : BlockTree) (b : Block) :=
  hashB b \in dom bt.

Notation "# bt" := (hashB bt) (at level 20).
Notation "## bt" := (hashB bt \\-> tt) (at level 70).

Definition valid_block b : bool :=
   prevBlockHash b != #b.

(* How can we assert there are no cycles? *)
(* You only add "fresh blocks" *)
Definition btExtend (bt : BlockTree) (b : Block) :=
  if #b \in dom bt then bt else #b \\-> b \+ bt.

(* Baisc property commutativity of additions *)

Lemma btExtend_dom bt b :
  valid bt -> {subset dom bt <= dom (btExtend bt b)}.
Proof.
move=>V z; rewrite /btExtend.
case:ifP=>C//=D.
by rewrite domUn inE andbC/= gen_validPtUn/= V D/= C orbC.
Qed.

 Lemma byExtend_in bt b :
  valid bt -> hashB b \in dom (btExtend bt b).
Proof.
move=>V; rewrite /btExtend/=; case: ifP=>//= N.
by rewrite domUn inE um_domPt !inE eqxx andbC/= gen_validPtUn/= V N.
Qed.

Lemma byExtend_idemp bt b :
  valid bt -> btExtend bt b = btExtend (btExtend bt b) b.
Proof. by move=>V; rewrite {2}/btExtend byExtend_in. Qed.

Lemma btExtend_comm bt b1 b2 :
  valid bt ->
  btExtend (btExtend bt b1) b2 = btExtend (btExtend bt b2) b1.
Proof.
move=>V.
case C1 : (hashB b1 \in dom bt).
- by rewrite ![btExtend _ b1]/btExtend C1 (btExtend_dom b2 V C1).  
case C2 : (hashB b2 \in dom bt).
- by rewrite ![btExtend _ b2]/btExtend C2 (btExtend_dom b1 V C2).
case B: (hashB b1 == hashB b2); first by move/eqP/hashB_inj: B=>B; subst b2.
have D1: hashB b2 \in dom (btExtend bt b1) = false.
- by rewrite /btExtend C1/= domUn !inE C2/= um_domPt inE B andbC/=.
have D2: hashB b1 \in dom (btExtend bt b2) = false.
- by rewrite /btExtend C2/= domUn !inE C1/= um_domPt inE eq_sym B andbC/=.
rewrite /btExtend D1 D2 C1 C2/= !joinA.
by rewrite -!(joinC bt) (joinC (# b2 \\-> b2)).
Qed.

(* How to show this terminates?
 * Sylvain suggested removing top from bt before passing it
 *  into the recursive call. Not sure if it will work.
 *)

Section BlockTreeProperties.

Variable bt: BlockTree.

Notation bm := (bmap bt).
Notation tps := (tops bt).

(* b is the previous of b' in bt: 
.... b <-- b' ....
*)
Definition next_of b : pred Block :=
  [pred b' | (hashB b == prevBlockHash b') && (hashB b' \in dom bm)].

(* All paths/chains should start with the GenesisBlock *)
Fixpoint compute_chain' (b : Block) (n : nat) : Blockchain :=
  if n is n'.+1
  then match find (prevBlockHash b) bm with
       | None => [:: b]
       | Some prev => rcons (compute_chain' prev n') prev
       end
  else [::].

Definition compute_chain b := compute_chain' b (size (keys_of bm)).  

(* Genesis block is in the beginning *)
(* Are these basic conditions? *)
Definition valid_chain bc : Prop :=
  [/\
   (* Evey chain is a path in bt.bm starting from GenesisBlock *)
   path next_of GenesisBlock bc,
   (* Every block in the chain is also in bm *)
   forall b, b \in bc -> find (hashB b) bm = Some b &
   (* Every block/hash in the chain is unique *)                      
   uniq (map hashB bc)].

Definition valid_bt : Prop :=
  [/\
   (* The map has a genesis block *)
   find (hashB GenesisBlock) bm = Some (GenesisBlock),
   (* Every key in bm is a hash *)
   forall h b, find h bm = Some b -> h = hashB b,
   (* A chain from every block is a valid one *)
   forall h b, find h bm = Some b -> valid_chain (compute_chain b) &
   (* Tops are indeed on top *)                                    
   forall b, b \in tps ->
     forall h' b', find h' bm = Some b' -> prevBlockHash b' != hashB b].

(* TODO: provide "getter" lemmas to extract specific conjuncts *)

Definition btChain : Blockchain :=
  let all_top_chains := [seq compute_chain top | top <- tps] in
  foldl (fun bc1 bc2 => if bc2 > bc1 then bc2 else bc1)
        [::] all_top_chains.

End BlockTreeProperties.

(* Facts about BlockTree manipulations *)

Lemma btExtend_valid bt b :
  let dm := (dom (bmap bt)) in 
  valid_bt bt -> (hashB b) \notin dm ->
  prevBlockHash b \in dm -> valid_bt (btExtend bt b).
Proof.
move=>/=V H1 H2; rewrite /btExtend; split=>//.
Admitted.

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