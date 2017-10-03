From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding.
Require Import SeqFacts BlockchainProperties.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A fomalization of a blockchain structure *)

(* TODO: Rename me into something more appropriate, e.g., BlockTrees.v  *)

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

Definition subchain (bc1 bc2 : Blockchain) :=
  exists p q, bc2 = p ++ bc1 ++ q.

(* Axioms *)
(* Is it realistic? *)
Axiom CFR_subchain : forall bc1 bc2, subchain bc1 bc2 -> bc2 >= bc1.
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


Axiom VAF_inj :
  forall (v v' : VProof) (ts : Timestamp) (bc1 bc2 : Blockchain),
    VAF v ts bc1 -> VAF v' ts bc2 -> v == v' /\ bc1 == bc2.

Axiom CFR_ext :
  forall (bc : Blockchain) (b : Block) (ext : seq Block),
    bc ++ (b :: ext) > bc.

Axiom CFR_rel :
  forall (A B : Blockchain),
    A = B \/ A > B \/ B > A.

Axiom CFR_nrefl :
  forall (bc : Blockchain), bc > bc -> False.

Axiom CFR_trans :
  forall (A B C : Blockchain),
    A > B -> B > C -> A > C.

Lemma CFR_trans_eq (A B C : Blockchain):
    A >= B -> B >= C -> A >= C.
Proof.
case=>H1[]H2.
- by subst C B; left.
- by subst B; right.
- by subst C; right.
by right; apply: (CFR_trans H1).
Qed.

Lemma CFR_trans_eq1 (A B C : Blockchain):
    A >= B -> B > C -> A > C.
Proof. by move=>[]H1 H2; [by subst B|]; apply: (CFR_trans H1). Qed.

Lemma CFR_trans_eq2 (A B C : Blockchain):
    A > B -> B >= C -> A > C.
Proof. by move=>H1[]H2; [by subst B|]; apply: (CFR_trans H1). Qed.

Lemma CFR_dual :
  forall (A B : Blockchain),
    (A > B = false) <-> (B >= A).
Proof.
split=>H.
* move: (CFR_rel A B); rewrite H; case; case; do? by [|right];
  by move=>/eqP H'; left; apply/eqP; rewrite eq_sym.
* case: H.
  by move=>->; case X: (A > A); by [|move: (CFR_nrefl X)].
  by move=>H; case X: (A > B); by [|move: (CFR_nrefl (CFR_trans H X))].
Qed.

Lemma Geq_trans :
  forall (A B C : Blockchain),
  A >= B -> B >= C -> A >= C.
Proof.
move=> A B C H1 H2; case: H1; case: H2.
by move=><- <-; left.
by move=>H ->; right.
by move=><-; right.
by move=>H1 H2; move: (CFR_trans H2 H1); right.
Qed.

Lemma CFR_excl :
  forall (bc bc' : Blockchain),
    bc > bc' -> bc' > bc -> False.
Proof.
by move=>bc bc' H1 H2; move: (CFR_trans H1 H2); apply CFR_nrefl.
Qed.


(*****************************
 *  BlockTree implementation *
 *****************************)

(* Also keeps orphan blocks *)
Definition BlockTree := union_map Hash Block.

Notation "# b" := (hashB b) (at level 20).
Notation "## b" := (hashB b \\-> tt) (at level 80).

Definition btHasBlock (bt : BlockTree) (b : Block) :=
  #b \in dom bt.

(* Genesis block's predecessor is itself *)
Hypothesis init_hash : (prevBlockHash GenesisBlock) = #GenesisBlock.

Notation "b ∈ bt" := (btHasBlock bt b) (at level 70).
Notation "b ∉ bt" := (~~ btHasBlock bt b) (at level 70).

Definition valid_block b : bool :=
  prevBlockHash b != #b.

(* TODO: Make this a part of BT validity, in addition to validH! *)
Definition has_init_block (bt : BlockTree) :=
  find (# GenesisBlock) bt = Some GenesisBlock.

Definition validH (bt : BlockTree) :=
  forall h b, find h bt = Some b -> h = hashB b.

Lemma validH_free bt (b : Block) :
  validH bt -> validH (free (# b) bt).
Proof. by move=>Vh h c; rewrite findF;case: ifP=>//_ /Vh. Qed.

(* How can we assert there are no cycles? *)
(* You only add "fresh blocks" *)
Definition btExtend (bt : BlockTree) (b : Block) :=
  if #b \in dom bt then bt else #b \\-> b \+ bt.

Lemma btExtendH bt b : valid bt -> validH bt -> validH (btExtend bt b).
Proof.
move=>V H z c; rewrite /btExtend.
case: ifP=>X; first by move/H.
rewrite findUnL ?gen_validPtUn ?V ?X//.
case: ifP=>Y; last by move/H.
rewrite um_domPt inE in Y; move/eqP: Y=>Y; subst z.
by rewrite um_findPt; case=>->.
Qed.

Lemma btExtendV bt b : valid bt = valid (btExtend bt b).
Proof.
rewrite /btExtend; case: ifP=>//N.
by rewrite gen_validPtUn/= N andbC.
Qed.

Lemma btExtendV_fold bt bs : valid bt = valid (foldl btExtend bt bs).
Proof.
elim/last_ind: bs=>[|xs x Hi]; first done.
by rewrite -cats1 foldl_cat /= Hi; apply btExtendV.
Qed.

Lemma btExtendH_fold bt bs : valid bt -> validH bt -> validH (foldl btExtend bt bs).
Proof.
move=>V Vh; elim/last_ind: bs=>[|xs x Hi]; first done.
rewrite (btExtendV_fold bt xs) in V.
by rewrite -cats1 foldl_cat /=; apply btExtendH.
Qed.

Lemma btExtendIB bt b :
  valid bt -> validH bt -> has_init_block bt ->
  has_init_block (btExtend bt b).
Proof.
move=>V H; rewrite /btExtend/has_init_block=>Ib.
case: ifP=>X; first done.
rewrite findUnL ?gen_validPtUn ?V ?X//.
case: ifP=>Y; last done.
rewrite um_domPt inE in Y; move/eqP: Y=>Y.
by specialize (hashB_inj Y)=><-; rewrite Y um_findPt.
Qed.

Lemma btExtendIB_fold bt bs :
  valid bt -> validH bt -> has_init_block bt ->
  has_init_block (foldl btExtend bt bs).
Proof.
move=>V H; rewrite/has_init_block=>iB.
elim/last_ind: bs=>[|xs x Hi]; first done.
rewrite -cats1 foldl_cat /= {1}/btExtend; case: ifP=>//=.
move=>X; rewrite um_findPtUn2.
case: ifP=>// /eqP E.
by move: (hashB_inj E)=><-.
by rewrite gen_validPtUn /= X andbC /= -btExtendV_fold.
Qed.

(* Baisc property commutativity of additions *)

Lemma btExtend_dom bt b :
  valid bt -> {subset dom bt <= dom (btExtend bt b)}.
Proof.
move=>V z; rewrite/btExtend.
case:ifP=>C//=D.
by rewrite domUn inE andbC/= gen_validPtUn/= V D/= C orbC.
Qed.

Lemma btExtend_find bt z b :
  valid bt -> find (#b) bt = Some b -> find (#b) (btExtend bt z) = Some b.
Proof.
move=>V F; rewrite/btExtend.
case:ifP=>C //.
by rewrite findUnR ?gen_validPtUn ?V ?C //; move: (find_some F)=>->.
Qed.

Lemma btExtend_dom_fold bt bs :
  valid bt -> {subset dom bt <= dom (foldl btExtend bt bs)}.
Proof.
move=>V z; elim/last_ind: bs=>[|xs x Hi]=>//.
by move=>In; move: (Hi In); rewrite -cats1 foldl_cat /=;
   apply btExtend_dom; rewrite -(btExtendV_fold _ xs).
Qed.

Lemma btExtend_find_fold bt b bs :
  valid bt -> find (#b) bt = Some b -> find (#b) (foldl btExtend bt bs) = Some b.
Proof.
move=>V F; elim/last_ind: bs=>[|xs x Hi]=>//.
rewrite -cats1 foldl_cat /=; apply btExtend_find=>//.
by rewrite -(btExtendV_fold _ xs).
Qed.

Lemma btExtend_in bt b :
  valid bt -> hashB b \in dom (btExtend bt b).
Proof.
move=>V; rewrite /btExtend/=; case: ifP=>//= N.
by rewrite domUn inE um_domPt !inE eqxx andbC/= gen_validPtUn/= V N.
Qed.

Lemma btExtend_in_either bt b b' :
  valid bt ->  b ∈ btExtend bt b' -> b ∈ bt \/ b == b'.
Proof.
move=>V; rewrite /btExtend/=; case: ifP=>//= N.
by left.
rewrite/btHasBlock domUn inE um_domPt gen_validPtUn V N /=;
move/orP; case.
by rewrite inE=>/eqP Eq; move: (hashB_inj Eq)=>->; right.
by left.
Qed.

Lemma btExtend_idemp bt b :
  valid bt -> btExtend bt b = btExtend (btExtend bt b) b.
Proof. by move=>V; rewrite {2}/btExtend btExtend_in. Qed.

(* Just a reformulation *)
Lemma btExtend_preserve (bt : BlockTree) (ob b : Block) :
  valid bt ->
  hashB ob \in (dom bt) -> hashB ob \in dom (btExtend bt b).
Proof. by move=>V/(btExtend_dom b V). Qed.

Lemma btExtend_withDup_noEffect (bt : BlockTree) (b : Block):
  hashB b \in dom bt -> bt = (btExtend bt b).
Proof. by rewrite /btExtend=>->. Qed.

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

Section BlockTreeProperties.

(* b is the previous of b' in bt:
.... b <-- b' ....
*)
Definition next_of (bt : BlockTree) b : pred Block :=
  [pred b' | (hashB b == prevBlockHash b') && (hashB b' \in dom bt)].

(* All paths/chains should start with the GenesisBlock *)
Fixpoint compute_chain' (bt : BlockTree) b remaining n : Blockchain :=
  (* Preventing cycles in chains *)
  if (hashB b) \in remaining
  then
    let rest := seq.rem (hashB b) remaining in
    (* Supporting primitive inductions *)
    if n is n'.+1 then
      match find (prevBlockHash b) bt with
      (* No parent *)
      | None => [:: b]
      (* Build chain prefix recursively *)
      | Some prev =>
        rcons (nosimpl (compute_chain' (free (hashB b) bt) prev rest n')) b
      end
    else [::]
  else [::].

(* Compute chain from the block *)
Definition compute_chain bt b :=
  compute_chain' bt b (keys_of bt) (size (keys_of bt)).

(* Total get_block function *)
Definition get_block (bt : BlockTree) k : Block :=
  if find k bt is Some b then b else GenesisBlock.

(* Collect all blocks *)
Definition all_blocks (bt : BlockTree) := [seq get_block bt k | k <- keys_of bt].

Definition is_block_in (bt : BlockTree) b := exists k, find k bt = Some b.

(* A certificate for all_blocks *)
Lemma all_blocksP bt b : reflect (is_block_in bt b) (b \in all_blocks bt).
Proof.
case B : (b \in all_blocks bt); [constructor 1|constructor 2].
- move: B; rewrite /all_blocks; case/mapP=>k Ik->{b}.
  rewrite keys_dom in Ik; move/gen_eta: Ik=>[b]/=[E H].
  by exists k; rewrite /get_block E.
case=>k F; move/negP: B=>B; apply: B.
rewrite /all_blocks; apply/mapP.
exists k; last by rewrite /get_block F.
by rewrite keys_dom; move/find_some: F.
Qed.

Lemma all_blocksP' bt b : validH bt -> reflect (b ∈ bt) (b \in all_blocks bt).
Proof.
move=>Vh.
case B : (b \in all_blocks bt); [constructor 1|constructor 2].
- move: B; rewrite /all_blocks; case/mapP=>k Ik->{b}.
  rewrite keys_dom in Ik; move/gen_eta: Ik=>[b]/=[E H].
  rewrite/get_block E /btHasBlock; specialize (Vh _ _ E); subst k.
  by move: (find_some E).
case=>H; rewrite/btHasBlock; move/negP: B=>B; apply: B.
rewrite /all_blocks; apply/mapP.
exists (#b); first by rewrite keys_dom.
rewrite/btHasBlock in H; rewrite/get_block.
case X: (find _ _)=>[b'|].
by move: (Vh _  _ X); move/hashB_inj.
by contradict H; move: (find_none X)=>H; apply/negP.
Qed.

(* All chains from the given tree *)
Definition good_chain (bc : Blockchain) :=
  if bc is h :: _ then h == GenesisBlock else false.

Definition all_chains bt := [seq compute_chain bt b | b <- all_blocks bt].

Definition good_chains bt := [seq ch <- all_chains bt | good_chain ch].

(* Get the blockchain *)
Definition take_better_bc bc2 bc1 := if (good_chain bc2) && (bc2 > bc1) then bc2 else bc1.

Definition btChain bt : Blockchain :=
  foldr take_better_bc [:: GenesisBlock] (all_chains bt).

End BlockTreeProperties.


(**********************************************************)

Section BtChainProperties.

Lemma btExtend_blocks (bt : BlockTree) (b : Block) : valid bt ->
  {subset all_blocks bt <= all_blocks (btExtend bt b)}.
Proof.
move=>V z/all_blocksP=>[[k]F]; apply/all_blocksP.
exists k; rewrite/btExtend; case:ifP=>// N.
rewrite findUnR ?N/=; last by rewrite gen_validPtUn/= V N.
by move/find_some: (F)=>->.
Qed.

Lemma compute_chain_no_block' bt (pb : Block) (hs : seq Hash) n :
  # pb \notin hs -> compute_chain' bt pb hs n = [::].
Proof. by case: n=>//=[|?]; move/negbTE=>->. Qed.

Lemma size_free n h (bt : BlockTree):
  valid bt -> n.+1 = size (keys_of bt) ->
  h \in keys_of bt -> n = size (keys_of (free h bt)).
Proof.
move=>V S K; rewrite keys_dom in K.
case: (gen_eta K)=>b[F]E; rewrite E in S V.
rewrite (keysUn_size V) um_keysPt/= addnC addn1 in S.
by case: S.
Qed.

Lemma compute_chain_equiv  bt (pb : Block) (hs1 hs2 : seq Hash) n :
  uniq hs1 -> uniq hs2 -> hs1 =i hs2 ->
  compute_chain' bt pb hs1 n = compute_chain' bt pb hs2 n.
Proof.
elim: n pb bt hs1 hs2=>//=[|n Hi] pb bt hs1 hs2 U1 U2 D; rewrite -D//.
case: ifP=>//G; case: (find (prevBlockHash pb) bt)=>[v|]=>//.
suff X: seq.rem (# pb) hs1 =i seq.rem (# pb) hs2.
- by rewrite (Hi v (free (# pb) bt) (seq.rem (# pb) hs1)
             (seq.rem (# pb) hs2) (rem_uniq _ U1) (rem_uniq _ U2) X).
by move=>z; rewrite (mem_rem_uniq _ U2) (mem_rem_uniq _ U1) !inE D.
Qed.

Lemma keys_rem1 (bt : BlockTree) h1 h2 a :
  valid (h1 \\-> a \+ bt) -> (h2 == h1) = false ->
  seq.rem h2 (keys_of (h1 \\-> a \+ bt)) =i keys_of (h1 \\-> a \+ free h2 bt).
Proof.
move=>V N z.
have X: h1 \\-> a \+ free h2 bt = free h2 (h1 \\-> a \+ bt)
  by rewrite um_freePtUn2// N.
rewrite X keys_dom domF !inE.
case B: (z == h2).
- by move/eqP:B=>B; subst h2; rewrite rem_filter ?(keys_uniq _)// mem_filter/= eqxx.
move/negbT: (B)=>B'.
case C: (z \in keys_of (h1 \\-> a \+ bt)).
- by rewrite (rem_neq B' C) eq_sym -keys_dom; move/negbTE:B'=>->.
by rewrite eq_sym B -keys_dom C; apply/negP=>/mem_rem=>E; rewrite E in C.
Qed.

Lemma keys_rem2 h (bt : BlockTree) : seq.rem h (keys_of bt) =i keys_of (free h bt).
Proof.
move=>z; case B: (z == h).
- move/eqP:B=>B; subst h.
  rewrite (rem_filter _ (@keys_uniq _ _ _ bt)) /predC1 mem_filter !keys_dom domF/=.
  by rewrite inE eqxx.
move/negbT: (B)=>B'; rewrite keys_dom domF inE eq_sym B -keys_dom.
case C: (z \in keys_of bt); first by rewrite (rem_neq B' C).
by apply/negP=>/mem_rem=>E; rewrite E in C.
Qed.

Lemma compute_chain_notin' bt (b b' : Block) (hs : seq Hash) n :
  valid bt -> (# b) \notin hs -> b \notin compute_chain' bt b' hs n.
Proof.
elim: n b b' bt hs=>[|n Hi] b b' bt hs V B/=; first by case:ifP.
case: ifP=>//B'.
case D1: (prevBlockHash b' \in dom bt); case: dom_find (D1)=>//; last first.
- by move=>->_; rewrite inE; apply/negbT/negP=>/eqP Z; subst b; rewrite B' in B.
move=>pb->_ _; rewrite -cats1 mem_cat !inE; apply/negP=>/orP[]; last first.
- by move/eqP=>Z; subst b'; rewrite B' in B.
apply/negP; apply: (Hi b pb (free (# b') bt) (seq.rem (# b') hs)).
- by rewrite validF V.
by apply/negP=>/mem_rem; apply/negP.
Qed.

(* The computed chain has no cycles *)
Lemma compute_chain_uniq bt b :
  valid bt -> uniq (compute_chain bt b).
Proof.
move=>V; rewrite /compute_chain.
have Ek: keys_of bt = keys_of bt by [].
have Es: size (keys_of bt) = size (keys_of bt) by [].
move: {-2}(size (keys_of bt)) Es=>n.
move: {-2}(keys_of bt) Ek=>hs Es En.
elim: n b bt V hs Es En=>[|n Hi] b bt V hs Es En/=; first by case:ifP.
case: ifP=>//B.
case D1: (prevBlockHash b \in dom bt); case: dom_find (D1)=>//;last by move=>->.
move=>pb->Eb _; rewrite rcons_uniq; subst hs.
have H1: valid (free (# b) bt) by rewrite validF.
have H3: n = size (keys_of (free (# b) bt)) by apply: size_free.
move: (Hi pb _ H1 _ (erefl _) H3)=>U.
rewrite -(compute_chain_equiv (free (# b) bt) pb n (rem_uniq _ (keys_uniq _))
          (keys_uniq (free (# b) bt)) (keys_rem2 _ _)) in U.
rewrite U andbC=>/={U}.
have X : (#b) \notin seq.rem (# b) (keys_of bt).
- elim: (keys_of bt) (keys_uniq bt)=>//=h t Gi/andP[]N/Gi{Gi}G.
  by case:ifP; [by move/eqP=><-| by rewrite inE eq_sym=>->].
by apply: (compute_chain_notin' _ _ _ X).
Qed.

(* Every block in a blockchain is also in the BlockTree *)
Lemma block_in_chain bt b0 b :
  valid bt ->
  b \in compute_chain bt b0 -> b ∈ bt.
Proof.
move=>V; rewrite /compute_chain.
have Ek: keys_of bt = keys_of bt by [].
have Es: size (keys_of bt) = size (keys_of bt) by [].
move: {-2}(size (keys_of bt)) Es=>n.
move: {-2}(keys_of bt) Ek=>hs Es En.
elim: n b0 bt hs Es En V=>[|n Hi] b0 bt hs Es En V/=; first by case:ifP.
case: ifP=>//B.
case D1: (prevBlockHash b0 \in dom bt); case: dom_find (D1)=>//; last first.
- by move=>->_; rewrite inE/==>/eqP Z; subst b0 hs; rewrite /btHasBlock -keys_dom.
move=>pb->Eb _; rewrite mem_rcons; subst hs.
have H1: valid (free (# b0) bt) by rewrite validF.
have H3: n = size (keys_of (free (# b0) bt)) by apply: size_free=>//.
move: (Hi pb _ _ (erefl _) H3 H1)=>H.
rewrite inE=>/orP[]=>[/eqP Z|]; first by subst b0; rewrite /btHasBlock -keys_dom.
rewrite -(compute_chain_equiv (free (# b0) bt) pb n (rem_uniq _ (keys_uniq _))
          (keys_uniq (free (# b0) bt)) (keys_rem2 _ _)) in H.
by move/H; rewrite /btHasBlock; rewrite domF !inE; case:ifP.
Qed.

Lemma btExtend_chain_prefix bt a b :
  valid bt -> validH bt ->
  exists p, p ++ (compute_chain bt b) = compute_chain (btExtend bt a) b .
Proof.
(* TODO: This existential is sooper-annoying. Can we have a better
   proof principle for this? *)
move=>V Vh.
case B: (#a \in dom bt); rewrite /btExtend B; first by exists [::].
rewrite /compute_chain.
(* Massaging the goal, for doing the induction on the size of (keys_of bt). *)
have Ek: keys_of bt = keys_of bt by [].
have Es: size (keys_of bt) = size (keys_of bt) by [].
move: {-2}(size (keys_of bt)) Es=>n.
move: {-2}(keys_of bt) Ek=>hs Es En.
rewrite keysUn_size ?gen_validPtUn ?V ?B// um_keysPt-!Es-En [_ + _] addnC addn1.
elim: n b bt V Vh B hs Es En=>[|n Hi] b bt V Vh B hs Es En.
- rewrite {1}/compute_chain'; move/esym/size0nil: En=>->.
  by move: (compute_chain' _ _ _ 1)=>c/=; exists c; rewrite cats0.
have V': valid (# a \\-> a \+ bt) by rewrite gen_validPtUn V B.
rewrite {2}/compute_chain' -!/compute_chain'.
case: ifP=>Bb; last first.
- exists [::]; rewrite compute_chain_no_block'//.
  apply/negbT/negP=>I1; move/negP:Bb=>Bb; apply: Bb; subst hs.
  by rewrite !keys_dom in I1 *; rewrite domUn inE V' I1 orbC.
rewrite {1}/compute_chain' -!/compute_chain'.
case: ifP=>X; last first.
- by eexists (match _ with | Some prev => rcons _ b | None => [:: b] end); rewrite cats0.
rewrite !findUnR ?gen_validPtUn ?V ?B//.
case D1: (prevBlockHash b \in dom bt); case: dom_find (D1)=>//; last first.
+ move=>->_; case D2: (prevBlockHash b \in dom (# a \\-> a));
  case: dom_find (D2)=>//; last by move=>->_; exists [::].
  move=>pb->/=.
  rewrite um_domPt inE in D2; move/eqP:D2=>D2; rewrite !D2 in B V' *.
  rewrite um_freePt2//eqxx -um_ptsU=> E _; move:(um_cancelPt E)=>{E B}E; subst a.
  by eexists _; rewrite -cats1.
move=>pb Hf; rewrite updF Hf eqxx -(Vh _ _ Hf)=>Eb _.
have Bn' : # b == # a = false by apply/negbTE/negP=>/eqP=>E;
           rewrite -E -keys_dom -Es X in B.
rewrite (um_freePtUn2 (#b) V') !Bn' !(Vh _ _ Hf).
(** How should we fold this over-eager rewriting **)
subst hs.
(* It's time to unleash the induction hypothesis! *)
have H1: valid (free (# b) bt) by rewrite validF.
have H2: validH (free (# b) bt) by apply: validH_free.
have H3: (# a \in dom (free (# b) bt)) = false by rewrite domF inE Bn' B.
have H4: n = size (keys_of (free (# b) bt)) by apply: size_free.
case: (Hi pb (free (# b) bt) H1 H2 H3 (keys_of (free (# b) bt)) (erefl _) H4)=>q E.
exists q; rewrite -rcons_cat; congr (rcons _ b).
(* Final rewriting of with the unique lists *)
rewrite (compute_chain_equiv _ _ _ _ _ (keys_rem2 (#b) bt))
        ?(keys_uniq _) ?(rem_uniq _ (keys_uniq bt))// E.
by rewrite -(compute_chain_equiv _ _ _ _ _ (keys_rem1 V' Bn'))
           ?(keys_uniq _) ?(rem_uniq _ (keys_uniq _)).
Qed.

(* A simple lemma: any block in the result of compute_chain,
   except for probably the first one, is not self-referential *)
Lemma compute_chain_no_self_ref bt b:
  valid bt -> validH bt -> (* has_init_block bt -> *)
  compute_chain bt b = [::] \/
  exists h t, compute_chain bt b = h :: t /\
              forall c, c \in t -> prevBlockHash c != # c.
Proof.
move=>V Vh; rewrite /compute_chain.
have Ek: keys_of bt = keys_of bt by [].
have Es: size (keys_of bt) = size (keys_of bt) by [].
move: {-2}(size (keys_of bt)) Es=>n.
move: {-2}(keys_of bt) Ek=>hs Es En.
case D: ((# b) \in hs); [right|left]; last first.
- by elim: n En=>/=[|n Hi]; rewrite D.
elim: n b bt V Vh hs Es En D=>[|n Hi] b bt V Vh hs Es En D/=.
- by move/esym/size0nil: En=>Z; subst hs; rewrite Z in D.
rewrite D.
case D1: (prevBlockHash b \in dom bt);
  case: dom_find (D1)=>//; last by move=>->_; exists b, [::].
move=>pb F; move: (Vh _ _ F)=>E _ _; rewrite F; rewrite !E in F D1 *.
have H1: valid (free (# b) bt) by rewrite validF.
have H2: validH (free (# b) bt) by apply: validH_free.
have H3: n = size (keys_of (free (# b) bt)).
- by apply: size_free=>//; rewrite -Es//.
have Uh: uniq hs by rewrite Es keys_uniq.
case Eh: (#pb == #b).
- have Eb: pb = b by apply/hashB_inj/eqP.
  subst pb; exists b, [::]; clear Hi H3 En; move/eqP: Eh=>Eh.
  by elim: n=>//=[|? _]; rewrite rem_filter//=; rewrite mem_filter/=eqxx/=.
have D2: #pb \in seq.rem (# b) (keys_of bt).
- apply: rem_neq; [by apply/negbT |by rewrite keys_dom].
have H4: # pb \in keys_of (free (# b) bt) by rewrite -keys_rem2.
case: (Hi pb _ H1 H2 _ (erefl _) H3 H4)=>{Hi D2 H4 H3 H2 H1}h[t][H1 H2].
rewrite Es (compute_chain_equiv (free (# b) bt) pb n (rem_uniq _ (keys_uniq _))
      (keys_uniq (free (# b) bt)) (keys_rem2 _ _)) H1.
exists h, (rcons t b); rewrite rcons_cons; split=>//.
move=>c; rewrite mem_rcons inE=>/orP[]; last by apply H2.
by move/eqP=>?; subst c; rewrite E; apply/negbT.
Qed.

Lemma btExtend_compute_chain bt a b :
  valid bt -> validH bt -> has_init_block bt ->
  good_chain (compute_chain bt b) ->
  (compute_chain (btExtend bt a) b) = compute_chain bt b.
Proof.
move=>V Vh Ib G.
move: (@btExtendH _ a V Vh)=>Vh'.
move: (V);  rewrite (btExtendV bt a) =>V'.
move: (btExtendIB a V Vh Ib)=>Ib'.
case: (btExtend_chain_prefix a b V Vh)
      (compute_chain_no_self_ref b V' Vh')=>p<- H.
suff X: p = [::] by subst p.
case: H; first by elim: p=>//.
case=>h[t][E]H; case:p E=>//=x xs[]->{x}Z; subst t.
have X: GenesisBlock \in xs ++ compute_chain bt b.
- rewrite mem_cat orbC; rewrite /good_chain in G.
  by case: (compute_chain bt b) G=>//??/eqP->; rewrite inE eqxx.
by move/H: X; rewrite init_hash; move/negbTE; rewrite eqxx.
Qed.

(* Chains from blocks are only growing as BT is extended *)
Lemma btExtend_chain_grows bt a b :
  valid bt -> validH bt ->
  compute_chain (btExtend bt a) b >= compute_chain bt b.
Proof.
move=>V H; apply: CFR_subchain.
by case: (btExtend_chain_prefix a b V H)=>p<-; exists p, [::]; rewrite cats0.
Qed.

Lemma init_chain bt :
  has_init_block bt ->
  compute_chain bt GenesisBlock = [:: GenesisBlock].
Proof.
rewrite /compute_chain.
have Ek: keys_of bt = keys_of bt by [].
have Es: size (keys_of bt) = size (keys_of bt) by [].
move: {-2}(size (keys_of bt)) Es=>n.
move: {-2}(keys_of bt) Ek=>hs Es En.
elim: n bt hs Es En=>[|n Hi] bt hs Es En Ib=>/=;
subst hs; move/find_some: (Ib); rewrite -keys_dom.
- by move/esym/size0nil:En=>->.
move=>->; rewrite init_hash Ib compute_chain_no_block'//.
rewrite mem_rem_uniq; last by apply: keys_uniq.
by rewrite inE eqxx.
Qed.

Lemma all_chains_init bt :
  has_init_block bt -> [:: GenesisBlock] \in all_chains bt.
Proof.
move=>H; rewrite /all_chains; apply/mapP.
exists GenesisBlock; last by rewrite (init_chain H).
by apply/mapP; exists (# GenesisBlock);
[by rewrite keys_dom; move/find_some: H|by rewrite /get_block H].
Qed.

(* Important lemma: btChain indeed delivers a chain in bt *)
Lemma btChain_in_bt bt :
  has_init_block bt ->
  btChain bt \in all_chains bt.
Proof.
rewrite /btChain=>H; move: (all_chains_init H)=>Ha.
move:(all_chains bt) Ha=>acs.
elim: acs=>//=bc rest Hi Ha.
case/orP: Ha=>G.
- move/eqP:G=>G; subst bc; rewrite /take_better_bc/=.
  case: ifP=>X; first by rewrite inE eqxx.
  rewrite -/take_better_bc; clear Hi X H.
  elim: rest=>//=; rewrite ?inE ?eqxx//.
  move=> bc rest Hi/=; rewrite {1}/take_better_bc.
  case:ifP=>_; first by rewrite !inE eqxx orbC.
  by rewrite !inE in Hi *; case/orP: Hi=>->//; rewrite ![_||true]orbC.
move/Hi: G=>{Hi}; rewrite inE.
move: (foldr take_better_bc [:: GenesisBlock] rest)=>l.
rewrite /take_better_bc/=.
case: ifP=>_; first by rewrite eqxx.
elim: rest=>//=; rewrite ?inE ?eqxx//.
move=> bc' rest Hi/=. rewrite inE=>/orP[].
- by move=>/eqP=>Z; subst bc'; rewrite eqxx orbC.
by case/Hi/orP=>->//; rewrite ![_||true]orbC.
Qed.

Lemma btChain_mem2 (bt : BlockTree) (b : Block) :
  valid bt -> has_init_block bt ->
  b \in btChain bt -> b ∈ bt.
Proof.
move=>V H.
move: (btChain_in_bt H); move: (btChain bt)=>bc H2 H1; clear H.
case/mapP:H2=>b0 _ Z; subst bc.
by apply: (@block_in_chain _ b0).
Qed.

Lemma btChain_mem (bt : BlockTree) (b : Block) :
  valid bt -> has_init_block bt ->
  b ∉ bt -> b \notin btChain bt.
Proof.
move=>V H.
by move/negP=>B; apply/negP=>G; apply: B; apply: (btChain_mem2 V H).
Qed.

Definition bc_fun bt := fun x =>
   [eta take_better_bc (([eta compute_chain bt] \o
   [eta get_block bt]) x)].

Lemma good_init bc :
  good_chain bc -> [:: GenesisBlock] > bc = false.
Proof.
rewrite /good_chain. case: bc=>//h t/eqP->.
by apply/CFR_dual; apply: CFR_subchain; exists [::], t.
Qed.

(* This is going to be used for proving X1 in btExtend_sameOrBetter *)
Lemma better_chains1 bt b :
  valid (# b \\-> b \+ bt) ->
  # b \notin dom bt -> validH bt -> has_init_block bt ->
  let f := bc_fun bt in
  let f' := bc_fun (# b \\-> b \+ bt) in
  forall h bc' bc,
    bc' >= bc ->
    good_chain bc' ->
    good_chain bc ->
    f' h bc' >= f h bc.
Proof.
move=>V B Vh H/=h bc' bc Gt Gb' Gb; rewrite /bc_fun/=.
set bc2 := compute_chain (# b \\-> b \+ bt) b.
case E: (#b == h).
- move/eqP:E=>Z; subst h.
  rewrite /get_block !um_findPtUn//.
  have X: find (# b) bt = None.
  + case: validUn V=>//_ _/(_ (# b)); rewrite um_domPt inE eqxx.
    by move/(_ is_true_true); case : dom_find=>//.
  rewrite !X init_chain//; clear X; rewrite /take_better_bc/=.
  case: ifP=>[/andP[X1 X2]|X]/=; rewrite (good_init Gb) andbC//=.
  + by right; apply: (CFR_trans_eq2 X2).
(* Now check if h \in dom bt *)
case D: (h \in dom bt); last first.
- rewrite /get_block (findUnL _ V) um_domPt inE E.
  case: dom_find D=>//->_{E h}.
  rewrite /take_better_bc/= !init_chain//; last first.
  + by move: (btExtendIB b (validR V) Vh H); rewrite/btExtend(negbTE B).
  by rewrite !(good_init Gb)!(good_init Gb') -(andbC false)/=.
case: dom_find D=>//c F _ _.
rewrite /get_block (findUnL _ V) um_domPt inE E !F.
move: (Vh h _ F); move/find_some: F=>D ?{E bc2}; subst h.
have P : exists p, p ++ (compute_chain bt c) = compute_chain (# b \\-> b \+ bt) c.
- by move: (btExtend_chain_prefix b c (validR V)Vh); rewrite /btExtend(negbTE B).
case:P=>p E; rewrite /take_better_bc.
case G1: (good_chain (compute_chain bt c))=>/=; last first.
- case G2: (good_chain (compute_chain (# b \\-> b \+ bt) c))=>//=.
  by case: ifP=>//X; right; apply: (CFR_trans_eq2 X).
(* Now need a fact about goodness monotonicity *)
move: (btExtend_compute_chain b (validR V) Vh H G1).
rewrite /btExtend (negbTE B)=>->; rewrite G1/=.
case:ifP=>X1; case: ifP=>X2=>//; do?[by left].
- by right; apply: (CFR_trans_eq2 X1 Gt).
by move/CFR_dual: X1.
Qed.

Lemma good_chain_foldr bt bc ks :
  good_chain bc ->
  good_chain (foldr (bc_fun bt) bc ks).
Proof.
elim: ks=>//=x xs Hi G; rewrite /bc_fun/take_better_bc/= in Hi *.
by case: ifP=>[/andP[B1 B2]|B]=>//; move/Hi: G.
Qed.

Lemma good_chain_foldr_init bt ks :
  good_chain (foldr (bc_fun bt) [:: GenesisBlock] ks).
Proof. by apply: good_chain_foldr; rewrite /good_chain eqxx. Qed.

Lemma better_chains_foldr bt b :
  valid (# b \\-> b \+ bt) ->
  # b \notin dom bt -> validH bt -> has_init_block bt ->
  let f := bc_fun bt in
  let f' := bc_fun (# b \\-> b \+ bt) in
  forall ks bc' bc,
    bc' >= bc ->
    good_chain bc' ->
    good_chain bc ->
    foldr f' bc' ks >= foldr f bc ks.
Proof.
move=>V B Vh H f f'; elim=>//h hs Hi bc' bc Gt G1 G2/=.
move: (Hi _ _ Gt G1 G2)=>{Hi}Hi.
by apply: better_chains1=>//; apply: good_chain_foldr.
Qed.

(* Monotonicity of BT => Monotonicity of btChain *)
Lemma btExtend_sameOrBetter bt b :
  valid bt -> validH bt -> has_init_block bt ->
  btChain (btExtend bt b) >= btChain bt.
Proof.
rewrite /btChain.
case B : (#b \in dom bt);
  rewrite (btExtendV bt b) /btExtend B; first by left.
move=>V Vh Ib; rewrite /all_chains/all_blocks -!seq.map_comp/=.
case: (keys_insert V)=>ks1[ks2][->->]; rewrite -![# b :: ks2]cat1s.
rewrite !foldr_map -/(bc_fun bt) -/(bc_fun (# b \\-> b \+ bt)) !foldr_cat.
set f := (bc_fun bt).
set f' := (bc_fun (# b \\-> b \+ bt)).
have X1: foldr f' [:: GenesisBlock] ks2 >= foldr f [:: GenesisBlock] ks2.
 - elim: ks2=>//=[|k ks Hi]; first by left.
   by apply: better_chains1; rewrite ?B ?good_chain_foldr_init//.
apply: better_chains_foldr=>//;
rewrite ?good_chain_foldr_init//; [by apply/negbT| |]; last first.
- by apply: good_chain_foldr; apply:good_chain_foldr_init.
simpl; rewrite {1 3}/f'/bc_fun/=/take_better_bc/=.
case:ifP=>///andP[B1 B2]. right.
apply: (CFR_trans_eq2 B2).
apply: better_chains_foldr=>//=; [by apply/negbT|by left].
Qed.

Lemma btExtend_fold_comm (bt : BlockTree) (bs bs' : seq Block) :
    valid bt ->
    foldl btExtend (foldl btExtend bt bs) bs' =
    foldl btExtend (foldl btExtend bt bs') bs.
Proof.
move=>V; elim/last_ind: bs'=>[|xs x Hi]/=; first done.
rewrite -cats1 !foldl_cat Hi=>/=; clear Hi.
elim/last_ind: bs=>[|ys y Hi]/=; first done.
rewrite -cats1 !foldl_cat -Hi /=; apply btExtend_comm.
by move: (btExtendV_fold bt xs) (btExtendV_fold (foldl btExtend bt xs) ys)=><-<-.
Qed.

Lemma btExtend_fold_preserve (ob : Block) bt bs:
    valid bt -> # ob \in (dom bt) ->
    # ob \in dom (foldl btExtend bt bs).
Proof.
move=>V Dom; elim/last_ind: bs=>[|xs x Hi]//.
rewrite -cats1 foldl_cat /=.
have: (valid (foldl btExtend bt xs)) by rewrite -btExtendV_fold.
by move=>V'; move: (btExtend_preserve x V' Hi).
Qed.

Lemma btExtend_fold_sameOrBetter bt bs:
  valid bt -> validH bt -> has_init_block bt ->
  btChain (foldl btExtend bt bs) >= btChain bt.
Proof.
move=>V Vh Ib; elim/last_ind: bs=>[|xs x Hi]/=; first by left.
rewrite -cats1 foldl_cat /=.
(have: (btChain (btExtend (foldl btExtend bt xs) x)
        >= btChain (foldl btExtend bt xs)) by
    apply btExtend_sameOrBetter;
    by [rewrite -btExtendV_fold|apply btExtendH_fold|apply btExtendIB_fold])=>H.
case: Hi; case: H.
by move=>->->; left.
by move=>H1 H2; rewrite H2 in H1; right.
by move=>->; right.
by move=>H1 H2; move: (CFR_trans H1 H2); right.
Qed.

(* monotonicity of (btChain (foldl btExtend bt bs)) wrt. bs *)
Lemma btExtend_monotone_btChain (bs ext : seq Block) bt:
    valid bt -> validH bt -> has_init_block bt ->
    btChain (foldl btExtend bt (bs ++ ext)) >= btChain (foldl btExtend bt bs).
Proof.
move=>V Vh Ib; elim/last_ind: ext=>[|xs x H]/=.
by rewrite foldl_cat; left.
rewrite -cats1.
(have: valid (foldl btExtend bt (bs ++ xs)) by rewrite -btExtendV_fold)=>V'.
move: (btExtend_fold_sameOrBetter [:: x] V')=>H'.
case: H; case: H'; rewrite !foldl_cat.
apply btExtendH_fold; by [rewrite -btExtendV_fold|apply btExtendH_fold].
apply btExtendIB_fold; by [rewrite -btExtendV_fold|apply btExtendH_fold|apply btExtendIB_fold].
by move=>->->; left.
by move=>H1 H2; rewrite H2 in H1; right.
apply btExtendH_fold; by [rewrite -btExtendV_fold|apply btExtendH_fold].
apply btExtendIB_fold; by [rewrite -btExtendV_fold|apply btExtendH_fold|apply btExtendIB_fold].
by move=>->; right.
by move=>H1 H2; move: (CFR_trans H1 H2); right.
Qed.

Lemma btExtend_not_worse (bt : BlockTree) (b : Block) :
    valid bt -> validH bt -> has_init_block bt ->
    ~ (btChain bt > btChain (btExtend bt b)).
Proof.
move=>V Vh Ib;
move: (btExtend_sameOrBetter b V Vh Ib); case.
by move=>->; apply: (CFR_nrefl).
move=>H; case X: (btChain bt > btChain (btExtend bt b)); last done.
by move: (CFR_nrefl (CFR_trans H X)).
Qed.

Lemma btExtend_fold_not_worse (bt : BlockTree) (bs : seq Block) :
    valid bt -> validH bt -> has_init_block bt ->
    ~ (btChain bt > btChain (foldl btExtend bt bs)).
Proof.
move=>V Vh Ib; move: (btExtend_fold_sameOrBetter bs V Vh Ib); case.
by move=><-; apply: CFR_nrefl.
by apply: CFR_excl.
Qed.

Lemma btExtend_seq_same bt b bs:
  valid bt -> validH bt -> has_init_block bt ->
  b \in bs -> btChain bt = btChain (foldl btExtend bt bs) ->
  btChain bt = btChain (btExtend bt b).
Proof.
move=>V Vh Ib H1.
move: (in_seq H1)=>[bf] [af] H2; rewrite H2.
move=>H; clear H1 H2.
move: (btExtend_fold_sameOrBetter [:: b] V Vh Ib)=>H1.
case: H1; first by move/eqP; rewrite eq_sym=>/eqP.
rewrite -cat1s in H.
move=>/=Con; rewrite H in Con; clear H; contradict Con.
rewrite foldl_cat btExtend_fold_comm. rewrite foldl_cat /= - foldl_cat.
(have: valid (btExtend bt b) by rewrite -btExtendV)=>V'.
(have: validH (btExtend bt b) by apply btExtendH)=>Vh'.
(have: has_init_block (btExtend bt b) by apply btExtendIB)=>Ib'.
by apply (btExtend_fold_not_worse V' Vh' Ib').
done.
Qed.

Lemma btExtend_seq_sameOrBetter bt b bs:
    valid bt -> validH bt -> has_init_block bt ->
    b \in bs -> btChain bt >= btChain (foldl btExtend bt bs) ->
    btChain bt >= btChain (btExtend bt b).
Proof.
move=>V Vh Ib H1; case.
by move=>H2; left; apply (btExtend_seq_same V Vh Ib H1 H2).
by move=>Con; contradict Con; apply btExtend_fold_not_worse.
Qed.

Lemma btExtend_seq_sameOrBetter_fref :
  forall (bc : Blockchain) (bt : BlockTree) (b : Block) (bs : seq Block),
    valid bt -> validH bt -> has_init_block bt ->
    b \in bs -> bc >= btChain bt ->
    bc >= btChain (foldl btExtend bt bs) ->
    bc >= btChain (btExtend bt b).
Proof.
move=> bc bt b bs V Vh Ib H HGt HGt'.
move: (in_seq H)=>[bf] [af] H'; rewrite H' in HGt'; clear H H'.
(have: valid (btExtend bt b) by rewrite -btExtendV)=>V';
(have: validH (btExtend bt b) by apply btExtendH)=>Vh';
(have: has_init_block (btExtend bt b) by apply btExtendIB)=>Ib'.
move: (btExtend_sameOrBetter b V Vh Ib)=>H.
move: (btExtend_fold_sameOrBetter (bf ++ b :: af) V Vh Ib).
rewrite -cat1s foldl_cat btExtend_fold_comm in HGt' *.
rewrite foldl_cat /= -foldl_cat in HGt' *.
move=>H'; case: HGt; case: HGt'; case: H; case: H'; move=>h0 h1 h2 h3.
- by left; rewrite h1 h3.
- rewrite h3 in h2; rewrite h2 in h0; contradict h0; apply: CFR_nrefl.
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
done. done. done.
have: (btChain (foldl btExtend (btExtend bt b) (af ++ bf))
        >= btChain (btExtend bt b)) by apply: btExtend_fold_sameOrBetter.
case=>[|H].
by move=><-; right.
by right; move: (CFR_trans h2 H).
done.
Qed.

(* Trivial sub-case of the original lemma; for convenience *)
Lemma btExtend_seq_sameOrBetter_fref' :
  forall (bc : Blockchain) (bt : BlockTree) (b : Block) (bs : seq Block),
    valid bt -> validH bt -> has_init_block bt ->
    b \in bs -> bc >= btChain bt ->
    bc = btChain (foldl btExtend bt bs) ->
    bc >= btChain (btExtend bt b).
Proof.
move=>bc bt b bs V Vh Ib iB Gt Eq.
(have: (bc >= btChain (foldl btExtend bt bs)) by left)=>GEq; clear Eq.
by move: (btExtend_seq_sameOrBetter_fref V Vh Ib iB Gt GEq).
Qed.

Lemma bc_spre_gt bc bc' :
  [bc <<< bc'] -> bc' > bc.
Proof. by case=>h; case=>t=>eq; rewrite eq; apply CFR_ext. Qed.

Lemma ohead_hash b0 (bt : seq Block) :
  b0 \in bt ->
  ohead [seq b <- bt | hashB b == hashB b0] = Some b0.
Proof.
elim: bt=>//=h bt Hi; rewrite inE; case/orP=>[/eqP Z|/Hi H]/=.
- by subst b0; rewrite eqxx.
by case: ifP=>C//=; move/eqP/hashB_inj: C=>->.
Qed.

(*************************************************************)
(************    Remaining properties   **********************)
(*************************************************************)

Lemma foldl1 {A B : Type} (f : A -> B -> A) (init : A) (val : B) :
  foldl f init [:: val] = f init val.
Proof. done. Qed.

Lemma good_chain_btExtend bt X b :
  valid bt -> validH bt -> has_init_block bt ->
  good_chain (compute_chain bt b) ->
  good_chain (compute_chain (btExtend bt X) b).
Proof.
move=>V Vh Ib Gc.
by move: (@btExtend_compute_chain _ X b V Vh Ib Gc)=>->.
Qed.

Lemma good_chain_btExtend_fold bt bs b :
  valid bt -> validH bt -> has_init_block bt ->
  good_chain (compute_chain bt b) ->
  good_chain (compute_chain (foldl btExtend bt bs) b).
Proof.
move=>V Vh Ib Gc; elim/last_ind: bs=>[|xs x Hi]//.
rewrite -cats1 foldl_cat /=; apply good_chain_btExtend.
by rewrite -(btExtendV_fold _ xs).
by move: (@btExtendH_fold _ xs V Vh).
by move: (btExtendIB_fold xs V Vh Ib).
done.
Qed.

Lemma btExtend_compute_chain_fold bt bs b :
  valid bt -> validH bt -> has_init_block bt ->
  good_chain (compute_chain bt b) ->
  (compute_chain (foldl btExtend bt bs) b) = compute_chain bt b.
Proof.
move=>V Vh Ib G; elim/last_ind: bs=>[|xs x Hi]//.
rewrite -cats1 foldl_cat /=.
move/eqP: (btExtendV_fold bt xs); rewrite V eq_sym=>/eqP V'.
move: (@btExtendH_fold _ xs V Vh)=>Vh'.
move: (btExtendIB_fold xs V Vh Ib)=>Ib'.
move: (@good_chain_btExtend_fold _ xs b V Vh Ib G)=>G'.
by move: (@btExtend_compute_chain _ x b V' Vh' Ib' G')=>->.
Qed.


(***********************************************************)
(*******      <btExtend_mint and all it needs>     *********)
(***********************************************************)

Lemma btChain_is_largest bt c :
  c \in good_chains bt -> btChain bt >= c.
Proof.
rewrite /btChain/good_chains; elim: (all_chains bt) c=>//=bc bcs Hi c.
case: ifP=>X/=; last by rewrite {1 3}/take_better_bc X=>/Hi.
rewrite inE; case/orP; last first.
- rewrite {1 3}/take_better_bc X=>/Hi=>{Hi}Hi.
  by case: ifP=>//=Y; right; apply:(CFR_trans_eq2 Y Hi).
move/eqP=>?; subst c; rewrite {1 3}/take_better_bc X/=.
by case: ifP=>//=Y; [by left|by move/CFR_dual: Y].
Qed.

Lemma btChain_good bt : good_chain (btChain bt).
Proof.
rewrite /btChain.
elim: (all_chains bt)=>[|bc bcs Hi]/=; first by rewrite eqxx.
by rewrite {1}/take_better_bc; case:ifP=>[/andP[->]|].
Qed.

Lemma btChain_in_good_chains bt :
  has_init_block bt -> btChain bt \in good_chains bt.
Proof.
move=> Ib; rewrite/good_chains mem_filter; apply/andP; split;
by [apply btChain_good | apply (btChain_in_bt Ib)].
Qed.

Lemma compute_chain_rcons bt c pc :
  valid bt -> validH bt -> #c \in dom bt ->
  find (prevBlockHash c) bt = Some pc ->
  compute_chain' bt c (keys_of bt) (size (keys_of bt)) =
  rcons (compute_chain' (free (# c) bt) pc
        (keys_of (free (# c) bt)) (size (keys_of (free (# c) bt)))) c.
Proof.
have Ek: keys_of bt = keys_of bt by [].
have Es: size (keys_of bt) = size (keys_of bt) by [].
move: {-2}(size (keys_of bt)) Es=>n.
move: {-2}(keys_of bt) Ek=>hs Es En.
elim: n c pc bt hs Es En=>[|n _]/= c pc bt hs Es En V Vh D F.
- subst hs; move/esym/size0nil: En=>Z.
  by rewrite -keys_dom Z in D.
rewrite Es keys_dom D F; congr (rcons _ _).
have U1: uniq (seq.rem (# c) hs) by rewrite rem_uniq// Es keys_uniq.
have U2: uniq (keys_of (free (#c) bt)) by rewrite keys_uniq.
have N: n = (size (keys_of (free (# c) bt))).
- apply: size_free=>//; rewrite -?Es//.
  by subst hs; rewrite keys_dom.
rewrite -N; clear N.
rewrite -(compute_chain_equiv (free (# c) bt) pc n U1 U2) Es//.
by apply: keys_rem2.
Qed.

Lemma compute_chain_noblock bt b c :
  valid bt -> validH bt ->
  #b \in dom bt ->
  b \notin compute_chain bt c ->
  compute_chain bt c = compute_chain (free (#b) bt) c.
Proof.
rewrite /compute_chain.
have Ek: keys_of bt = keys_of bt by [].
have Es: size (keys_of bt) = size (keys_of bt) by [].
move: {-2}(size (keys_of bt)) Es=>n.
move: {-2}(keys_of bt) Ek=>hs Es En.
elim: n c b bt hs Es En=>[|n Hi]/= c b bt hs Es En V Vh Hb.
- suff X: size (keys_of (free (# b) bt)) = 0
    by rewrite X=>/=_; case:ifP=>_; case:ifP.
  suff X: bt = Unit by subst bt; rewrite free0 keys0.
  subst hs; move/esym/size0nil: En=>Z.
  by apply/dom0E=>//z/=; rewrite -keys_dom Z inE.
(* These two seem to always appear in these proofs... *)
have H1: valid (free (# b) bt) by rewrite validF.
have H3: n = size (keys_of (free (# b) bt)).
- apply: size_free=>//; [by rewrite Es in En|by rewrite keys_dom].
case: ifP=>[X|X _]; rewrite Es keys_dom in X; last first.
- rewrite -H3; clear Hi En H3; case:n=>//=[|n]; first by case:ifP.
  by rewrite keys_dom domF inE X; case:ifP; case: ifP.
case: dom_find X=>// prev F _ _; move/Vh/hashB_inj: (F)=>Z; subst prev.
case D: ((prevBlockHash c) \in dom bt); last first.
- case: dom_find (D)=>//->_; rewrite inE=>N; rewrite -H3.
  clear Hi; elim: n En H3=>/=[|n _]En H3; last first.
  + have X: #b == #c = false
      by apply/negP=>/eqP/hashB_inj?; subst c; rewrite eqxx in N.
  + have Y: find (prevBlockHash c) (free (# b) bt) = None.
    * suff D': (prevBlockHash c) \notin dom (free (# b) bt) by case: dom_find D'.
      by rewrite domF inE D; case:ifP.
    rewrite Y; clear Y.
    suff K : #c \in dom (free (# b) bt) by rewrite keys_dom K.
    by rewrite domF inE X (find_some F).
  (* Now need to derive a contradiction from H3 *)
  rewrite Es in En.
  have X: #c \in keys_of (free (# b) bt).
  + rewrite keys_dom domF inE.
    case: ifP=>C; last by apply: (find_some F).
    by move/eqP/hashB_inj : C N=>->; rewrite eqxx.
  by move/esym/size0nil: H3=>E; rewrite E in X.

(* Now an interesting, inductive, case *)
case: dom_find D=>//pc F' _ _; rewrite F'=>Hn; rewrite -H3.
rewrite mem_rcons inE in Hn; case/norP: Hn=>/negbTE N Hn.
have Dc: #c \in keys_of (free (# b) bt).
  + rewrite keys_dom domF inE.
    case: ifP=>C; last by apply: (find_some F).
    by move/eqP/hashB_inj : C N=>->; rewrite eqxx.

(* Now need to unfold massage the RHS of the goal with compute_chain', so
   it would match the Hi with (bt := free (# c) bt, c := pc) etc *)
have X: compute_chain' (free (# b) bt) c
                       (keys_of (free (# b) bt))
                       (size (keys_of (free (# b) bt))) =
        rcons (compute_chain' (free (# b) (free (# c) bt)) pc
                              (keys_of (free (# b) (free (# c) bt)))
                              (size (keys_of (free (# b) (free (# c) bt))))) c.
- rewrite freeF.
  have Z: (#b == #c) = false
    by apply/negP=>/eqP/hashB_inj=>?; subst c; rewrite eqxx in N.
  rewrite Z.
  (* Given everything in the context, this should be a trivial lemma,
     please extract it and prove (takig bt' = free (# b) bt) *)
  apply: compute_chain_rcons=>//; rewrite ?validF//.
  + by apply: validH_free.
  + by rewrite domF inE Z (find_some F).
  suff X: prevBlockHash c == # b = false by rewrite findF X.
  apply/negP=>/eqP Y; rewrite -Y in Z.
  move/Vh: (F')=>E'. rewrite E' in Y Z F'.
  move/hashB_inj : Y=>?; subst pc.
  have T: exists m, n = m.+1.
  + rewrite Es in En.
    clear Hn Hi E' En H1 Vh; subst hs.
    case: n H3=>//[|n]; last by exists n.
    by move/esym/size0nil=>E; rewrite E in Dc.
  case: T=>m Zn; rewrite Zn/= in Hn.
  rewrite Es in Hn.
  have X: # b \in seq.rem (# c) (keys_of bt)
    by apply: rem_neq; rewrite ?keys_dom//; apply/negbT.
  rewrite X in Hn.
  case: (find _ _) Hn=>[?|]; last by rewrite inE eqxx.
  by rewrite mem_rcons inE eqxx.

(* The interesting inductive case! *)
rewrite H3 X; congr (rcons)=>//.
have U1: uniq (seq.rem (# c) hs) by rewrite rem_uniq// Es keys_uniq.
have U2: uniq (keys_of (free (#c) bt)) by rewrite keys_uniq.
rewrite -(Hi pc b (free (#c) bt) (keys_of (free (# c) bt)) (erefl _)) ?validF//.
- rewrite -H3.
  rewrite ((compute_chain_equiv (free (# c) bt) pc n) U1 U2)//.
  by rewrite Es; apply: keys_rem2.
- (* prove out of H3 and N *)
  rewrite Es in En; apply: (size_free V En).
  by rewrite keys_dom; apply:(find_some F).
- by apply: validH_free.
- rewrite domF inE eq_sym Hb.
  by case:ifP=>///eqP/hashB_inj?; subst c; rewrite eqxx in N.
rewrite -(compute_chain_equiv (free (# c) bt) pc n U1 U2)//.
by rewrite Es; apply: keys_rem2.
Qed.

Lemma compute_chain_prev bt b pb :
  valid bt -> validH bt -> #b \in dom bt ->
  prevBlockHash b = # pb ->
  b \notin (compute_chain bt pb) ->
  compute_chain bt b = rcons (compute_chain bt pb) b.
Proof.
move=>V Vh D Hp Nh.
rewrite (compute_chain_noblock V Vh D Nh).
rewrite /compute_chain.
have Ek: keys_of bt = keys_of bt by [].
have Es: size (keys_of bt) = size (keys_of bt) by [].
move: {-2}(size (keys_of bt)) Es=>n.
move: {-2}(keys_of bt) Ek=>hs Es En.
elim: n b bt hs Es En V Vh D Hp Nh=>[|n Hi] b bt hs Es En V Vh D Hp Nh/=.
- by rewrite -keys_dom -Es in D; move/esym/size0nil: En=>Z; rewrite Z in D.
rewrite {1}Es keys_dom D Hp.
have H1: valid (free (# b) bt) by rewrite validF.
have H3: n = size (keys_of (free (# b) bt)).
- by apply: size_free=>//;[by rewrite Es in En|by rewrite keys_dom].
case B: (#pb \in dom bt); last first.
- case: dom_find (B)=>//F _; rewrite F.
  rewrite -H3; clear Hi En H3; case:n=>//=[|n]; first by case:ifP.
  by rewrite keys_dom domF inE B; case:ifP; case: ifP.
case: dom_find B=>// prev F _ _; rewrite F; congr (rcons _ _).
move/Vh/hashB_inj: F=>?; subst prev.
rewrite H3.
have U1: uniq (seq.rem (# b) hs) by rewrite Es rem_uniq// keys_uniq.
have U2: uniq (keys_of (free (# b) bt)) by rewrite keys_uniq.
rewrite (compute_chain_equiv (free (#b) bt) pb
                 (size (keys_of (free (# b) bt))) U1 U2)//.
by rewrite Es; apply: keys_rem2.
Qed.

(* This axiom seems reasonable: it shouldn't be possible
   to generate a block _from_ the chain it is supposed to tail. *)
Axiom VAF_no_cycle :
  forall b ts bc, VAF (proof b) ts bc -> b \notin bc.

Lemma btExtend_mint_ext bt bc b ts :
  let pb := last GenesisBlock bc in
  valid bt -> validH bt -> has_init_block bt ->
  bc = compute_chain bt pb ->
  good_chain bc ->
  prevBlockHash b = #pb ->
  VAF (proof b) ts bc ->
  compute_chain (btExtend bt b) b = rcons bc b.
Proof.
move=>pb V Vh Ib E HGood Hp Hv.
suff X: compute_chain (btExtend bt b) b =
        rcons (compute_chain (btExtend bt b) pb) b.
- rewrite E in HGood.
  rewrite (btExtend_compute_chain b V Vh Ib HGood) in X.
  by rewrite X -E.
have V': valid (btExtend bt b) by rewrite -(btExtendV bt b).
have Vh': validH (btExtend bt b) by apply:btExtendH.
have D: #b \in dom (btExtend bt b).
- move: V'; rewrite /btExtend; case:ifP=>X V'//.
  by rewrite um_domPtUn inE V' eqxx.
apply: compute_chain_prev=>//.
move: (VAF_no_cycle Hv); rewrite E in HGood.
by rewrite (btExtend_compute_chain b V Vh Ib HGood) E.
Qed.

Lemma chain_from_last bt c :
  valid bt -> validH bt -> has_init_block bt ->
  c \in all_chains bt -> c = compute_chain bt (last GenesisBlock c).
Proof.
move=>V Vh Ib/mapP[b] H1 H2.
suff X: (last GenesisBlock (compute_chain bt b)) = b.
- by rewrite -H2 in X; rewrite X.
move/mapP:H1=>[h]; rewrite keys_dom=>D.
case: dom_find (D)=>//b' F _ _; move/Vh: (F)=>?; subst h.
rewrite /get_block F=>?; subst b'.
rewrite /compute_chain; clear H2 V Vh Ib.
have Ek: keys_of bt = keys_of bt by [].
have Es: size (keys_of bt) = size (keys_of bt) by [].
move: {-2}(size (keys_of bt)) Es=>n.
move: {-2}(keys_of bt) Ek=>hs Es En.
elim: n b bt hs Es En D F=>[|n Hi] b bt hs Es En D F/=.
- by rewrite -keys_dom -Es in D; move/esym/size0nil: En=>Z; rewrite Z in D.
by rewrite Es keys_dom D; case (find _ _)=>[?|]//; rewrite last_rcons.
Qed.

Lemma btExtend_mint_good bt b ts :
  let bc := btChain bt in
  let pb := last GenesisBlock bc in
  valid bt -> validH bt -> has_init_block bt ->
  good_chain bc ->
  prevBlockHash b = #pb ->
  VAF (proof b) ts bc ->
  good_chain (compute_chain (btExtend bt b) b).
Proof.
move=>bc pb V Vh Ib Gc Hp Hv.
(have: bc \in all_chains bt by move: (btChain_in_bt Ib))=>InC.
(have: bc = compute_chain bt pb by move: (chain_from_last V Vh Ib InC))=>C.
move: (btExtend_mint_ext V Vh Ib C Gc Hp Hv)=>->; subst bc.
rewrite/good_chain. case X: (rcons _ _)=>[|x xs].
contradict X; elim: (btChain bt)=>//.
have: (good_chain (btChain bt) = true)by [].
rewrite/good_chain/=; case X': (btChain _)=>[|h t]; first done.
by move/eqP=>Eq; subst h; rewrite X' rcons_cons in X; case: X=>-> _.
Qed.

Lemma btExtend_mint bt b ts :
  let pb := last GenesisBlock (btChain bt) in
  valid bt -> validH bt -> has_init_block bt ->
  prevBlockHash b = # pb ->
  VAF (proof b) ts (btChain bt) = true ->
  btChain (btExtend bt b) > btChain bt.
Proof.
move=>lst V Vh Ib mint Hv.
have HGood: good_chain (rcons (btChain bt) b).
- by move: (btChain_good bt); rewrite {1}/good_chain; case (btChain bt).
have E: compute_chain (btExtend bt b) b = rcons (btChain bt) b.
- apply: (@btExtend_mint_ext _ (btChain bt) b _ V Vh
                             Ib _ (btChain_good bt) mint Hv).
  by move/(chain_from_last V Vh Ib): (btChain_in_bt Ib).
have HIn : rcons (btChain bt) b \in
           filter good_chain (all_chains (btExtend bt b)).
- rewrite mem_filter HGood/=-E/all_chains; apply/mapP.
  have V' : valid (btExtend bt b) by rewrite -btExtendV.
  exists b=>//; rewrite /all_blocks/btExtend in V'*; apply/mapP; exists (#b).
  + by rewrite keys_dom; case:ifP V'=>X V'//; rewrite um_domPtUn inE eqxx andbC.
  rewrite /get_block; case:ifP V'=>X V'; last by rewrite um_findPtUn.
  case: dom_find X=>//b' F _ _; move/Vh/hashB_inj :(F)=> ?.
  by subst b'; rewrite F.
move/btChain_is_largest: HIn=>H; apply: (CFR_trans_eq1 H).
by rewrite -cats1; apply: CFR_ext.
Qed.

(***********************************************************)
(*******      </btExtend_mint and all it needs>     ********)
(***********************************************************)

Lemma good_chains_in_superset cbt bt bs :
  valid cbt -> validH cbt -> has_init_block cbt ->
  valid bt -> validH bt -> has_init_block bt ->
  cbt = foldl btExtend bt bs ->
  {subset good_chains bt <= good_chains cbt }.
Proof.
move=>V Vh Ib V' Vh' Ib' Ext; move: (btExtend_dom_fold bs V')=>Sub;
rewrite/good_chains; move=>ch; rewrite !mem_filter; move/andP=>[Gc] HCh.
apply/andP; split=>//.
move: HCh; move/mapP=>[z] IBt Ch; apply/mapP.
exists z.
- apply/all_blocksP; move/all_blocksP: IBt; rewrite/is_block_in;
  move=>[h] F; move: (Vh' _ _ F)=>Eq; exists h; subst h;
  by rewrite Ext; move: (@btExtend_find_fold _ _ bs V' F).
- rewrite Ch in Gc *; rewrite Ext.
  by move: (@btExtend_compute_chain_fold _ bs z V' Vh' Ib' Gc).
Qed.

Definition good_bt bt :=
  forall b, b \in all_blocks bt -> good_chain (compute_chain bt b).

Lemma btExtend_good_chains_fold  bt bs:
  valid bt -> validH bt -> has_init_block bt ->
  {subset good_chains bt <= good_chains (foldl btExtend bt bs) }.
Proof.
move=>V Vh Hib c; rewrite !mem_filter=>/andP[G]; rewrite G/=.
rewrite/good_chains/all_chains=>/mapP[b]H1 H2; apply/mapP; exists b.
- apply/mapP; exists (#b).
  + rewrite keys_dom; apply/(btExtend_dom_fold bs V).
    case/mapP: H1=>z; rewrite keys_dom=>D.
    rewrite /get_block; case: (@dom_find _ _ _ z) (D)=>//b' F _ _.
    by rewrite F=>Z; subst b'; move/Vh: F=><-.
  case/mapP: H1=>z; rewrite keys_dom=>D.
  move/(btExtend_dom_fold bs V): (D)=>D'.
  rewrite {1}/get_block; case:dom_find (D)=>//b' F _ _.
  rewrite F=>?; subst b'. move/Vh: F=>?; subst z.
  rewrite /get_block; case:dom_find (D')=>//b' F _ _.
  by rewrite F; move/(@btExtendH_fold _ bs V Vh): F=>/hashB_inj.
by rewrite btExtend_compute_chain_fold=>//; rewrite -H2.
Qed.

Lemma good_chains_subset bt :
  { subset good_chains bt <= all_chains bt }.
Proof. by move=>ch; rewrite mem_filter; move/andP=>[]. Qed.

Lemma btExtnend_new_block cbt b :
  valid cbt ->
  # b \notin dom cbt ->
  b \in all_blocks (btExtend cbt b).
Proof.
move=>V N; move: (V); rewrite (btExtendV _ b)=>V'.
move/negbTE: N=>N.
rewrite /btExtend !N in V' *.
case:(@keys_insert _ _ (#b) b cbt V')=>ks1[ks2][_].
rewrite /all_blocks=>->.
apply/mapP; exists (#b); last first.
- by rewrite /get_block findUnL// um_domPt inE eqxx um_findPt.
by rewrite mem_cat orbC inE eqxx.
Qed.

Lemma btExtend_get_block bt b k :
  valid bt -> #b \notin dom bt -> k != #b ->
  get_block (btExtend bt b) k = get_block bt k.
Proof.
move=>V D N; rewrite /get_block/btExtend (negbTE D).
rewrite findUnL; last by move: (btExtendV bt b); rewrite /btExtend(negbTE D)=><-.
by rewrite um_domPt inE eq_sym (negbTE N).
Qed.

Lemma btExtend_good_split cbt b :
  valid cbt -> validH cbt -> has_init_block cbt ->
  good_bt cbt -> #b \notin dom cbt -> good_bt (btExtend cbt b) ->
  exists cs1 cs2, 
    good_chains cbt = cs1 ++ cs2 /\
    good_chains (btExtend cbt b) = cs1 ++ [:: compute_chain (btExtend cbt b) b] ++ cs2.
Proof.
move=>V Vh Hib Hg N Hg'.
have G: good_chain (compute_chain (btExtend cbt b) b).
- by apply: (Hg' b); apply: btExtnend_new_block=>//.
have Eb: btExtend cbt b = (#b \\-> b \+ cbt) by rewrite /btExtend (negbTE N).  
move: (V); rewrite (btExtendV _ b)=>V'; rewrite !Eb in V' *.
move: (@keys_insert _ _ (#b) b cbt V')=>[ks1][ks2][Ek]Ek'.
(* Massaging the left part *)
set get_chain := [eta compute_chain cbt] \o [eta get_block cbt].
rewrite /good_chains{1}/all_chains/all_blocks -!seq.map_comp Ek map_cat filter_cat.
rewrite -/get_chain.
exists [seq c <- [seq get_chain i | i <- ks1] | good_chain c],
       [seq c <- [seq get_chain i | i <- ks2] | good_chain c]; split=>//.
rewrite /all_chains/all_blocks Ek' /= -cat1s.
have [N1 N2] : (#b \notin ks1) /\ (#b \notin ks2).
- have U : uniq (ks1 ++ # b :: ks2) by rewrite -Ek'; apply:keys_uniq. 
  rewrite cat_uniq/= in U; case/andP: U=>_/andP[]H1 H2.
  case/andP:H2=>->_; split=>//; by case/norP: H1.
have [D1 D2] : {subset ks1 <= dom cbt} /\ {subset ks2 <= dom cbt}.
- by split=>k; rewrite -keys_dom Ek mem_cat=>->//; rewrite orbC.  
rewrite !map_cat !filter_cat ; congr (_ ++ _); clear Ek Ek'.
- rewrite -!Eb;elim: ks1 N1 D1=>//k ks Hi/= N1 D1.
  have Dk: k \in dom cbt by apply: (D1 k); rewrite inE eqxx.
  have Nk: k != #b by apply/negbT/negP=>/eqP=>?; subst k; rewrite inE eqxx in N1 .
  rewrite !(btExtend_get_block V N Nk); rewrite /get_chain/=.
  set bk := (get_block cbt k).
  have Gk: good_chain (compute_chain cbt bk).
  apply: Hg; apply/mapP; exists k=>//; by rewrite keys_dom.
  rewrite !(btExtend_compute_chain b V Vh Hib Gk) !Gk/=.
  congr (_ :: _); apply: Hi; first by rewrite inE in N1; case/norP:N1.
  by move=>z=>D; apply: D1; rewrite inE D orbC.
rewrite -[(compute_chain _ b) :: _]cat1s; congr (_ ++ _)=>/=; rewrite -!Eb.
- suff D: (get_block (btExtend cbt b) (# b)) = b by rewrite D G. 
  by rewrite /get_block/btExtend (negbTE N) findUnL ?V'// um_domPt inE eqxx um_findPt. 
elim: ks2 N2 D2=>//k ks Hi/= N2 D2.
have Dk: k \in dom cbt by apply: (D2 k); rewrite inE eqxx.
have Nk: k != #b by apply/negbT/negP=>/eqP=>?; subst k; rewrite inE eqxx in N2.
rewrite !(btExtend_get_block V N Nk); rewrite /get_chain/=.
set bk := (get_block cbt k).
have Gk: good_chain (compute_chain cbt bk).
apply: Hg; apply/mapP; exists k=>//; by rewrite keys_dom.
rewrite !(btExtend_compute_chain b V Vh Hib Gk) !Gk/=.
congr (_ :: _); apply: Hi; first by rewrite inE in N2; case/norP:N2.
by move=>z=>D; apply: D2; rewrite inE D orbC.  
Qed.

Definition take_better_alt bc2 bc1 := if (bc2 > bc1) then bc2 else bc1.

(* Alternative definition of btChain, more convenient to work with *)
(* only good chains. *)
Lemma btChain_alt bt:
  btChain bt =
  foldr take_better_alt [:: GenesisBlock] (good_chains bt).
Proof.
rewrite /btChain/take_better_bc/take_better_alt/good_chains.
elim: (all_chains bt)=>//c cs/= Hi.
by case C: (good_chain c)=>//=; rewrite !Hi.
Qed.

Lemma best_chain_in cs :
  foldr take_better_alt [:: GenesisBlock] cs = [:: GenesisBlock] \/
  foldr take_better_alt [:: GenesisBlock] cs \in cs.
Proof.
elim: cs=>[|c cs Hi]; [by left|]. 
rewrite /take_better_alt/=; case:ifP; rewrite -/take_better_alt=>X.
- by right; rewrite inE eqxx.
case/CFR_dual: X=>X.
- by rewrite !X in Hi *; right; rewrite inE eqxx.
by case: Hi=>H; [left| right]=>//; rewrite inE orbC H.
Qed.  

Lemma foldr_better_mono bc cs : foldr take_better_alt bc cs >= bc.
Proof.
elim: cs=>//=[|c cs Hi/=]; first by left.
rewrite {1 3}/take_better_alt; case: ifP=>G//.
by right; apply:(CFR_trans_eq2 G Hi).
Qed.

Lemma best_element_in bc cs1 cs2 bc' :
  bc > [:: GenesisBlock] ->
  bc > foldr take_better_alt [:: GenesisBlock] (cs1 ++ cs2) ->
  bc \in cs1 ++ [:: bc'] ++ cs2 ->
  bc = foldr take_better_alt [:: GenesisBlock] (cs1 ++ [:: bc'] ++ cs2).       
Proof.
move=>Gt H1 H2.
have G: forall c, c \in cs1 ++ cs2 -> bc > c.
- elim: (cs1 ++ cs2) H1=>//=c cs Hi H z.
  rewrite {1}/take_better_alt in H; move: H.
  case:ifP=>//G1 G2.
  + rewrite inE; case/orP; first by move/eqP=>?; subst z.
    by move/Hi: (CFR_trans G2 G1)=>G3; move/G3.
  rewrite inE; case/orP; last by move/(Hi G2).
  move/eqP=>?; subst z; case/CFR_dual: G1=>G1; first by rewrite !G1 in G2.  
  by apply: (CFR_trans G2 G1).
have [G1 G2]: ((forall z, z \in cs1 -> bc > z) /\
               forall z, z \in cs2 -> bc > z).
- split=>z H; move: (G z); rewrite mem_cat H/=; first by move/(_ is_true_true).
  by rewrite orbC; move/(_ is_true_true).
clear G.
have Z: bc = bc'.
- suff C: bc \in [:: bc'] ++ cs2.
  + elim: (cs2) C G2=>//=[|c cs Hi C G2]; first by rewrite inE=>/eqP.
    rewrite inE in C; case/orP:C; first by move/eqP.
    by move/G2; move/CFR_nrefl.
  elim: (cs1) G1 H2=>//=c cs Hi G1 H2.
  rewrite inE in H2; case/orP: H2.
  + move/eqP=>Z; subst c; move: (G1 bc).
    by rewrite inE eqxx/==>/(_ is_true_true)/CFR_nrefl.
  rewrite mem_cat; case/orP=>// G.  
  by move: (G1 bc); rewrite inE orbC G/==>/(_ is_true_true)/CFR_nrefl.
subst bc'; clear H1 H2.  
(* Ok, here comes the final blow *)
suff C: bc = foldr take_better_alt [:: GenesisBlock] ([:: bc] ++ cs2).
- rewrite foldr_cat -C; clear C.
  elim: cs1 G1=>//c cs Hi G1; rewrite /take_better_alt/=-/take_better_alt. 
  case: ifP=>G.
  - move: (CFR_trans_eq2 G (foldr_better_mono bc cs))=>G'.
    move: (G1 c). rewrite inE eqxx/==>/(_ is_true_true) G3.
    by move: (CFR_nrefl (CFR_trans G' G3)).
  by case/CFR_dual: G=>G;
     apply: Hi=>z T; move: (G1 z); rewrite inE T orbC/=;
     by move/(_ is_true_true).
clear G1 cs1.
simpl; rewrite {1}/take_better_alt.
suff C: bc > foldr take_better_alt [:: GenesisBlock] cs2 by rewrite C.
elim: cs2 G2=>//=c cs Hi G. 
rewrite {1}/take_better_alt; case: ifP=>C.
- by move: (G c); rewrite inE eqxx/=; move/(_ is_true_true).
apply: Hi=>z T; move: (G z); rewrite inE T orbC/=.
by move/(_ is_true_true).
Qed.

Lemma complete_bt_extend_gt' cbt bt bs b :
  valid cbt -> validH cbt -> has_init_block cbt ->
  valid bt -> validH bt -> has_init_block bt ->
  good_bt cbt -> #b \notin dom cbt -> good_bt (btExtend cbt b) ->
  btChain (btExtend bt b) > btChain cbt ->
  cbt = foldl btExtend bt bs ->
  btChain (btExtend bt b) = btChain (btExtend cbt b).
Proof.
move=>V Vh Hib Vl Vhl Hil Hg Nb Hg' Gt Ec.
have H1: btChain (btExtend bt b) \in good_chains (btExtend cbt b).
- rewrite Ec; move: (btExtend_fold_comm bs [::b] Vl)=>/=->.
  apply: btExtend_good_chains_fold=>//;[by rewrite -(btExtendV bt b)| | |].
  + by apply: (btExtendH Vl Vhl).
  + by apply: (btExtendIB b Vl Vhl Hil).
  by apply: btChain_in_good_chains; apply: btExtendIB.
set bc := btChain (btExtend bt b) in H1 Gt *.
have Gt' : bc > [::GenesisBlock].
- rewrite /good_chains mem_filter in H1.
  case/andP:H1; move/good_init/CFR_dual; case=>//H _.
  subst bc. rewrite H in Gt. Check good_init.
  move: (btChain_in_good_chains Hib); rewrite /good_chains mem_filter.
  by case/andP=>/good_init; rewrite Gt.
clear Vl Vhl Hil Ec. (* Let's forget about bt. *)
case: (btExtend_good_split V Vh Hib Hg Nb Hg')=>cs1[cs2][E1]E2.
rewrite !btChain_alt in Gt *; rewrite E1 in Gt; rewrite !E2 in H1 *.
have I: [:: GenesisBlock] \in cs1 ++ cs2.
- by rewrite -E1 mem_filter/= eqxx; apply:all_chains_init.
by apply: best_element_in.
Qed.

Lemma complete_bt_extend_eq cbt bt bs b :
  valid cbt -> validH cbt -> has_init_block cbt ->
  valid bt -> validH bt -> has_init_block bt ->
  good_bt cbt -> good_bt (btExtend cbt b) ->
  btChain (btExtend bt b) > btChain cbt ->
  cbt = foldl btExtend bt bs ->
  btChain (btExtend bt b) = btChain (btExtend cbt b).
Proof.
move=>V Vh Hib Vl Vhl Hil Hg Hg' Gt Ec.
case Nb: (#b \in dom cbt); last first.
- move/negbT: Nb=>Nb.
  by apply: (complete_bt_extend_gt' V Vh Hib Vl Vhl Hil Hg Nb Hg' Gt Ec).
have Q : cbt = btExtend cbt b by rewrite /btExtend Nb.
rewrite Q Ec in Gt.
move: (btExtend_fold_comm bs [::b] Vl)=>/==>Z; rewrite Z in Gt.

(* Boring stuff *)
have G1 : valid (btExtend bt b) by rewrite -(btExtendV bt b).
have G2 : validH (btExtend bt b) by apply: (btExtendH Vl Vhl).
have G3 : has_init_block (btExtend bt b) by apply: (btExtendIB b Vl Vhl Hil).
by move/CFR_dual: (btExtend_fold_sameOrBetter bs G1 G2 G3); rewrite Gt.
Qed.

Lemma good_chains_subset_geq bt bt':
  valid bt -> validH bt -> has_init_block bt ->
  valid bt' -> validH bt' -> has_init_block bt' ->
  {subset good_chains bt <= good_chains bt' } ->
  btChain bt' >= btChain bt.
Proof.
move=>V Vh Ib V' Vh' Ib' S.
by specialize (S (btChain bt) (btChain_in_good_chains Ib));
   apply btChain_is_largest.
Qed.

(* This is likely to be missing some important assumptions,
   but the proof shouldn't be that different from complete_bt_extend_eq  *)
Lemma btExtend_within cbt bt b bs:
  valid cbt -> validH cbt -> has_init_block cbt ->
  valid bt -> validH bt -> has_init_block bt ->
  good_bt cbt -> good_bt (btExtend cbt b) ->
  btChain cbt >= btChain (btExtend bt b) ->
  (* A new block added, so the new gain will be also a good chain,
     and the largest in btExtend bt b *)
  prevBlockHash b = # last GenesisBlock (btChain bt) ->
  cbt = foldl btExtend bt bs ->
  btChain (btExtend cbt b) > btChain cbt -> False.
Proof.
move=>V Vh Hib Vl Vhl Hil Hg Hg' Gt P Ec Cont.
(* We need to show that adding this block to cbt cannot provoke 
   a blockchain larger than it already had and has. In other words,
   either this block is already in the cbt, or now, but isn't
   contributing, due to goodness of the final tree. *)
case Nb: (#b \in dom cbt); first by rewrite /btExtend Nb in Cont; apply: CFR_nrefl Cont.

(* Ok, somebody minted a block, which does not contribute to cbt' *)
(* blockchain, only to the local one. *)

(* I see the following strategy:

Due to goodnes of cbt and it being a superset of bt, any good chain in
bt has the same one in cbt. The only new chain obtained in cbt by
adding b, due to goodness, is the one that ends with b.

But, amongst other good chains that cbt got, there was already one
that is larger than the one ending with b (or any super-chain of it in
bt, as b could "plug a hole" in it), so this chain will be larger than
the largest good chain in (btExtend bt b), and, hence, larger than the
only one new added chain in (bcExtend cbt b).

Use the chain-splitting lemma `btExtend_good_split` to inspect
individual elements in cbt.

*)

Admitted.


End BtChainProperties.

(**************************
 *  TxPool implementation *
 **************************)
Definition TxPool := seq Transaction.

(* (* Transaction is valid and consistent with the given chain. *) *)
Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.

(* (* Axioms and other properties *) *)
(* Axiom tpExtend_validAndConsistent : *)
(*   forall (bt : BlockTree) (pool : TxPool) (tx : Transaction), *)
(*     tx \in (tpExtend pool bt tx) -> (txValid tx (btChain bt)). *)

(* Axiom tpExtend_withDup_noEffect : *)
(*   forall (bt : BlockTree) (pool : TxPool) (tx : Transaction), *)
(*     tx \in pool -> (tpExtend pool bt tx) = pool. *)
