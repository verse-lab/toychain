From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Chains Blocks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A formalization of a block forests *)

(************************************************************)
(******************* <parameters> ***************************)
(************************************************************)

Parameter Timestamp : Type.
Parameter Hash : ordType.
Parameter VProof : eqType.
Parameter Transaction : eqType.
Parameter Address : finType.

Definition block := @Block Hash Transaction VProof.

Parameter GenesisBlock : block.

Definition Blockchain := seq block.

(* In fact, it's a forest, as it also keeps orphan blocks *)
Definition BlockTree := union_map Hash block.

(* Transaction pools *)
Definition TxPool := seq Transaction.

Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.
Parameter genProof : Address -> Blockchain -> TxPool -> Timestamp -> option (TxPool * VProof).
Parameter VAF : VProof -> Blockchain -> TxPool -> bool.
Parameter FCR : Blockchain -> Blockchain -> bool.

(* Transaction is valid and consistent with the given chain *)
Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.

(************************************************************)
(********************* </parameters> ************************)
(************************************************************)

Notation "A > B" := (FCR A B).
Notation "A >= B" := (A = B \/ A > B).
Notation "# b" := (hashB b) (at level 20).

Definition bcLast (bc : Blockchain) := last GenesisBlock bc.

Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

(************************************************************)
(*********************** <axioms> ***************************)
(************************************************************)

(* 1.  Genesis block properties *)

Axiom init_hash : prevBlockHash GenesisBlock = #GenesisBlock.

(* 2.  Transaction validation *)

Axiom txValid_nil : forall t, txValid t [::].

(* 3.  Hashes *)

Axiom hashB_inj : injective hashB.

Axiom hashT_inj : injective hashT.

(* 4.  VAF *)

(* This axiom seems reasonable: it shouldn't be possible
   to generate a block _from_ the chain it is supposed to tail.  *)
Axiom VAF_nocycle :
  forall (b : block) (bc : Blockchain), VAF (proof b) bc (txs b) -> b \notin bc.

(* 2. FCR *)

Axiom FCR_subchain :
  forall bc1 bc2, subchain bc1 bc2 -> bc2 >= bc1.

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

Axiom genProof_subseq :
  forall (a : Address) (bc : Blockchain) (txs : TxPool) (ts : Timestamp) (txs' : TxPool) (pf : VProof),
    genProof a bc txs ts = Some (txs', pf) ->
    subseq txs txs'.

(************************************************************)
(*********************** </axioms> **************************)
(************************************************************)

Lemma FCR_trans_eq (A B C : Blockchain):
    A >= B -> B >= C -> A >= C.
Proof.
case=>H1[]H2.
- by subst C B; left.
- by subst B; right.
- by subst C; right.
by right; apply: (FCR_trans H1).
Qed.

Lemma FCR_trans_eq1 (A B C : Blockchain):
    A >= B -> B > C -> A > C.
Proof. by move=>[]H1 H2; [by subst B|]; apply: (FCR_trans H1). Qed.

Lemma FCR_trans_eq2 (A B C : Blockchain):
    A > B -> B >= C -> A > C.
Proof. by move=>H1[]H2; [by subst B|]; apply: (FCR_trans H1). Qed.

Lemma FCR_dual :
  forall (A B : Blockchain),
    (A > B = false) <-> (B >= A).
Proof.
split=>H.
* move: (FCR_rel A B); rewrite H; case; case; do? by [|right];
  by move=>/eqP H'; left; apply/eqP; rewrite eq_sym.
* case: H.
  by move=>->; case X: (A > A); by [|move: (FCR_nrefl X)].
  by move=>H; case X: (A > B); by [|move: (FCR_nrefl (FCR_trans H X))].
Qed.

Lemma Geq_trans :
  forall (A B C : Blockchain),
  A >= B -> B >= C -> A >= C.
Proof.
move=> A B C H1 H2; case: H1; case: H2.
by move=><- <-; left.
by move=>H ->; right.
by move=><-; right.
by move=>H1 H2; move: (FCR_trans H2 H1); right.
Qed.

Lemma FCR_excl :
  forall (bc bc' : Blockchain),
    bc > bc' -> bc' > bc -> False.
Proof.
by move=>bc bc' H1 H2; move: (FCR_trans H1 H2); apply FCR_nrefl.
Qed.


(******************************************************************)
(*                BlockTree implementation                        *)
(******************************************************************)

Definition btHasBlock (bt : BlockTree) (b : block) := #b \in dom bt.

Notation "b ∈ bt" := (btHasBlock bt b) (at level 70).
Notation "b ∉ bt" := (~~ btHasBlock bt b) (at level 70).

Definition valid_block b : bool :=
  prevBlockHash b != #b.

Definition has_init_block (bt : BlockTree) :=
  find (# GenesisBlock) bt = Some GenesisBlock.

Definition validH (bt : BlockTree) :=
  forall h b, find h bt = Some b -> h = hashB b.

Lemma validH_free bt (b : block) :
  validH bt -> validH (free (# b) bt).
Proof. by move=>Vh h c; rewrite findF;case: ifP=>//_ /Vh. Qed.

(* We only add "fresh blocks" *)
Definition btExtend (bt : BlockTree) (b : block) :=
  if #b \in dom bt then bt else #b \\-> b \+ bt.

Lemma btExtendH bt b : valid bt -> validH bt -> validH (btExtend bt b).
Proof.
move=>V H z c; rewrite /btExtend.
case: ifP=>X; first by move/H.
rewrite findUnL ?validPtUn ?V ?X//.
case: ifP=>Y; last by move/H.
rewrite domPtK inE in Y; move/eqP: Y=>Y; subst z.
by rewrite findPt; case=>->.
Qed.

Lemma btExtendV bt b : valid bt = valid (btExtend bt b).
Proof.
rewrite /btExtend; case: ifP=>//N.
by rewrite validPtUn/= N andbC.
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
rewrite findUnL ?validPtUn ?V ?X//.
case: ifP=>Y; last done.
rewrite domPtK inE in Y; move/eqP: Y=>Y.
by specialize (hashB_inj Y)=><-; rewrite Y findPt.
Qed.

Lemma btExtendIB_fold bt bs :
  valid bt -> validH bt -> has_init_block bt ->
  has_init_block (foldl btExtend bt bs).
Proof.
move=>V H; rewrite/has_init_block=>iB.
elim/last_ind: bs=>[|xs x Hi]; first done.
rewrite -cats1 foldl_cat /= {1}/btExtend; case: ifP=>//=.
move=>X; rewrite findPtUn2.
case: ifP=>// /eqP E.
by move: (hashB_inj E)=><-.
by rewrite validPtUn /= X andbC /= -btExtendV_fold.
Qed.

(* Baisc property commutativity of additions *)

Lemma btExtend_dom bt b :
  valid bt -> {subset dom bt <= dom (btExtend bt b)}.
Proof.
move=>V z; rewrite/btExtend.
case:ifP=>C//=D.
by rewrite domUn inE andbC/= validPtUn/= V D/= C orbC.
Qed.

Lemma btExtend_find bt z b :
  valid bt -> find (#b) bt = Some b -> find (#b) (btExtend bt z) = Some b.
Proof.
move=>V F; rewrite/btExtend.
case:ifP=>C //.
by rewrite findUnR ?validPtUn ?V ?C //; move: (find_some F)=>->.
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
by rewrite domUn inE domPtK !inE eqxx andbC/= validPtUn/= V N.
Qed.

Lemma btExtend_in_either bt b b' :
  valid bt ->  b ∈ btExtend bt b' -> b ∈ bt \/ b == b'.
Proof.
move=>V; rewrite /btExtend/=; case: ifP=>//= N.
by left.
rewrite/btHasBlock domUn inE domPtK validPtUn V N /=;
move/orP; case.
by rewrite inE=>/eqP Eq; move: (hashB_inj Eq)=>->; right.
by left.
Qed.

Lemma btExtend_idemp bt b :
  valid bt -> btExtend bt b = btExtend (btExtend bt b) b.
Proof. by move=>V; rewrite {2}/btExtend btExtend_in. Qed.

(* Just a reformulation *)
Lemma btExtend_preserve (bt : BlockTree) (ob b : block) :
  valid bt ->
  hashB ob \in (dom bt) -> hashB ob \in dom (btExtend bt b).
Proof. by move=>V/(btExtend_dom b V). Qed.

Lemma btExtend_withDup_noEffect (bt : BlockTree) (b : block):
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
- by rewrite /btExtend C1/= domUn !inE C2/= domPt inE B andbC/=.
have D2: hashB b1 \in dom (btExtend bt b2) = false.
- by rewrite /btExtend C2/= domUn !inE C1/= domPt inE eq_sym B andbC/=.
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
  compute_chain' bt b (dom bt) (size (dom bt)).

(* Total get_block function *)
Definition get_block (bt : BlockTree) k : Block :=
  if find k bt is Some b then b else GenesisBlock.

(* Collect all blocks *)
Definition all_blocks (bt : BlockTree) := [seq get_block bt k | k <- dom bt].

Definition is_block_in (bt : BlockTree) b := exists k, find k bt = Some b.

(* A certificate for all_blocks *)
Lemma all_blocksP bt b : reflect (is_block_in bt b) (b \in all_blocks bt).
Proof.
case B : (b \in all_blocks bt); [constructor 1|constructor 2].
- move: B; rewrite /all_blocks; case/mapP=>k Ik->{b}.
  move/um_eta: Ik=>[b]/=[E H].
  by exists k; rewrite /get_block E.
case=>k F; move/negP: B=>B; apply: B.
rewrite /all_blocks; apply/mapP.
exists k; last by rewrite /get_block F.
by move/find_some: F.
Qed.

Lemma all_blocksP' bt b : validH bt -> reflect (b ∈ bt) (b \in all_blocks bt).
Proof.
move=>Vh.
case B : (b \in all_blocks bt); [constructor 1|constructor 2].
- move: B; rewrite /all_blocks; case/mapP=>k Ik->{b}.
  move/um_eta: Ik=>[b]/=[E H].
  rewrite/get_block E /btHasBlock; specialize (Vh _ _ E); subst k.
  by move: (find_some E).
case=>H; rewrite/btHasBlock; move/negP: B=>B; apply: B.
rewrite /all_blocks; apply/mapP.
exists (#b) => //.
rewrite/btHasBlock in H; rewrite/get_block.
case X: (find _ _)=>[b'|].
by move: (Vh _  _ X); move/hashB_inj.
by contradict H; move: (find_none X)=>H; apply/negP.
Qed.

(* All chains from the given tree *)
Definition good_chain (bc : Blockchain) :=
  if bc is h :: _ then h == GenesisBlock else false.

(* Transaction validity *)
Fixpoint tx_valid_chain' (bc prefix : seq block) :=
  if bc is b :: bc'
  then [&& all [pred t | txValid t prefix] (txs b) &
        tx_valid_chain' bc' (rcons prefix b)]
  else true.

Definition tx_valid_chain bc := tx_valid_chain' bc [::].

Definition all_chains bt := [seq compute_chain bt b | b <- all_blocks bt].

Definition good_chains bt := [seq c <- all_chains bt | good_chain c && tx_valid_chain c].

(* Get the blockchain *)
Definition take_better_bc bc2 bc1 :=
  if (good_chain bc2 && tx_valid_chain bc2) && (bc2 > bc1) then bc2 else bc1.

Definition btChain bt : Blockchain :=
  foldr take_better_bc [:: GenesisBlock] (all_chains bt).

End BlockTreeProperties.


(**********************************************************)

Section BtChainProperties.

Lemma btExtend_blocks (bt : BlockTree) (b : block) : valid bt ->
  {subset all_blocks bt <= all_blocks (btExtend bt b)}.
Proof.
move=>V z/all_blocksP=>[[k]F]; apply/all_blocksP.
exists k; rewrite/btExtend; case:ifP=>// N.
rewrite findUnR ?N/=; last by rewrite validPtUn/= V N.
by move/find_some: (F)=>->.
Qed.

Lemma compute_chain_no_block' bt (pb : block) (hs : seq Hash) n :
  # pb \notin hs -> compute_chain' bt pb hs n = [::].
Proof. by case: n=>//=[|?]; move/negbTE=>->. Qed.

Lemma size_free n h (bt : BlockTree):
  valid bt -> n.+1 = size (dom bt) ->
  h \in dom bt -> n = size (dom (free h bt)).
Proof.
move=>V S K.
case: (um_eta K)=>b[F]E; rewrite E in S V.
rewrite (size_domUn V) domPtK/= addnC addn1 in S.
by case: S.
Qed.

Lemma compute_chain_equiv  bt (pb : block) (hs1 hs2 : seq Hash) n :
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

Lemma dom_rem1 (bt : BlockTree) h1 h2 a :
  valid (h1 \\-> a \+ bt) -> (h2 == h1) = false ->
  seq.rem h2 (dom (h1 \\-> a \+ bt)) =i dom (h1 \\-> a \+ free h2 bt).
Proof.
move=>V N z.
have X: h1 \\-> a \+ free h2 bt = free h2 (h1 \\-> a \+ bt)
  by rewrite freePtUn2// N.
rewrite X domF !inE.
case B: (z == h2).
- by move/eqP:B=>B; subst h2; rewrite rem_filter ?(dom_uniq _)// mem_filter/= eqxx.
move/negbT: (B)=>B'.
case C: (z \in dom (h1 \\-> a \+ bt)).
- by rewrite (rem_neq B' C) eq_sym; move/negbTE:B'=>->.
by rewrite eq_sym B; apply/negP=>/mem_rem=>E; rewrite E in C.
Qed.

Lemma dom_rem2 h (bt : BlockTree) : seq.rem h (dom bt) =i dom (free h bt).
Proof.
move=>z; case B: (z == h).
- move/eqP:B=>B; subst h.
  rewrite (rem_filter _ (@uniq_dom _ _ _ bt)) /predC1 mem_filter domF/=.
  by rewrite inE eqxx.
move/negbT: (B)=>B'; rewrite domF inE eq_sym B.
case C: (z \in dom bt); first by rewrite (rem_neq B' C).
by apply/negP=>/mem_rem=>E; rewrite E in C.
Qed.

Lemma compute_chain_notin' bt (b b' : block) (hs : seq Hash) n :
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
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n b bt V hs Es En=>[|n Hi] b bt V hs Es En/=; first by case:ifP.
case: ifP=>//B.
case D1: (prevBlockHash b \in dom bt); case: dom_find (D1)=>//;last by move=>->.
move=>pb->Eb _; rewrite rcons_uniq; subst hs.
have H1: valid (free (# b) bt) by rewrite validF.
have H3: n = size (dom (free (# b) bt)) by apply: size_free.
move: (Hi pb _ H1 _ (erefl _) H3)=>U.
rewrite -(compute_chain_equiv (free (# b) bt) pb n (rem_uniq _ (uniq_dom _))
          (uniq_dom (free (# b) bt)) (dom_rem2 _ _)) in U.
rewrite U andbC=>/={U}.
have X : (#b) \notin seq.rem (# b) (dom bt).
- elim: (dom bt) (uniq_dom bt)=>//=h t Gi/andP[]N/Gi{Gi}G.
  by case:ifP; [by move/eqP=><-| by rewrite inE eq_sym=>->].
by apply: (compute_chain_notin' _ _ _ X).
Qed.

(* Every block in a blockchain is also in the BlockTree *)
Lemma block_in_chain bt b0 b :
  valid bt ->
  b \in compute_chain bt b0 -> b ∈ bt.
Proof.
move=>V; rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n b0 bt hs Es En V=>[|n Hi] b0 bt hs Es En V/=; first by case:ifP.
case: ifP=>//B.
case D1: (prevBlockHash b0 \in dom bt); case: dom_find (D1)=>//; last first.
- by move=>->_; rewrite inE/==>/eqP Z; subst b0 hs; rewrite /btHasBlock.
move=>pb->Eb _; rewrite mem_rcons; subst hs.
have H1: valid (free (# b0) bt) by rewrite validF.
have H3: n = size (dom (free (# b0) bt)) by apply: size_free=>//.
move: (Hi pb _ _ (erefl _) H3 H1)=>H.
rewrite inE=>/orP[]=>[/eqP Z|]; first by subst b0; rewrite /btHasBlock.
rewrite -(compute_chain_equiv (free (# b0) bt) pb n (rem_uniq _ (uniq_dom _))
          (uniq_dom (free (# b0) bt)) (dom_rem2 _ _)) in H.
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
(* Massaging the goal, for doing the induction on the size of (dom bt). *)
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
rewrite size_domUn ?validPtUn ?V ?B// domPtK-!Es-En [_ + _] addnC addn1.
elim: n b bt V Vh B hs Es En=>[|n Hi] b bt V Vh B hs Es En.
- rewrite {1}/compute_chain'; move/esym/size0nil: En=>->.
  by move: (compute_chain' _ _ _ 1)=>c/=; exists c; rewrite cats0.
have V': valid (# a \\-> a \+ bt) by rewrite validPtUn V B.
rewrite {2}/compute_chain' -!/compute_chain'.
case: ifP=>Bb; last first.
- exists [::]; rewrite compute_chain_no_block'//.
  apply/negbT/negP=>I1; move/negP:Bb=>Bb; apply: Bb; subst hs.
  by rewrite domUn inE V' I1 orbC.
rewrite {1}/compute_chain' -!/compute_chain'.
case: ifP=>X; last first.
- by eexists (match _ with | Some prev => rcons _ b | None => [:: b] end); rewrite cats0.
rewrite !findUnR ?validPtUn ?V ?B//.
case D1: (prevBlockHash b \in dom bt); case: dom_find (D1)=>//; last first.
+ move=>->_; case D2: (prevBlockHash b \in dom (# a \\-> a));
  case: dom_find (D2)=>//; last by move=>->_; exists [::].
  move=>pb->/=.
  rewrite domPtK inE in D2; move/eqP:D2=>D2; rewrite !D2 in B V' *.
  rewrite freePt2//eqxx -ptsU=> E _.
  have H_v: valid (# a \\-> a) by apply (@dom_valid _ _ _ (# a)); rewrite domPtK /= inE.
  move:(cancelPt H_v E)=>{E B}E; subst a.
  by eexists _; rewrite -cats1.
move=>pb Hf; rewrite updF Hf eqxx -(Vh _ _ Hf)=>Eb _.
have Bn' : # b == # a = false by apply/negbTE/negP=>/eqP=>E;
           rewrite -E -Es X in B.
rewrite (freePtUn2 (#b) V') !Bn' !(Vh _ _ Hf).
(** How should we fold this over-eager rewriting **)
subst hs.
(* It's time to unleash the induction hypothesis! *)
have H1: valid (free (# b) bt) by rewrite validF.
have H2: validH (free (# b) bt) by apply: validH_free.
have H3: (# a \in dom (free (# b) bt)) = false by rewrite domF inE Bn' B.
have H4: n = size (dom (free (# b) bt)) by apply: size_free.
case: (Hi pb (free (# b) bt) H1 H2 H3 (dom (free (# b) bt)) (erefl _) H4)=>q E.
exists q; rewrite -rcons_cat; congr (rcons _ b).
(* Final rewriting of with the unique lists *)
rewrite (compute_chain_equiv _ _ _ _ _ (dom_rem2 (#b) bt))
        ?(uniq_dom _) ?(rem_uniq _ (uniq_dom bt))// E.
by rewrite -(compute_chain_equiv _ _ _ _ _ (dom_rem1 V' Bn'))
           ?(uniq_dom _) ?(rem_uniq _ (uniq_dom _)).
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
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
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
have H3: n = size (dom (free (# b) bt)).
- by apply: size_free=>//; rewrite -Es//.
have Uh: uniq hs by rewrite Es uniq_dom.
case Eh: (#pb == #b).
- have Eb: pb = b by apply/hashB_inj/eqP.
  subst pb; exists b, [::]; clear Hi H3 En; move/eqP: Eh=>Eh.
  by elim: n=>//=[|? _]; rewrite rem_filter//=; rewrite mem_filter/=eqxx/=.
have D2: #pb \in seq.rem (# b) (dom bt).
- apply: rem_neq; [by apply/negbT |by []].
have H4: # pb \in dom (free (# b) bt) by rewrite -dom_rem2.
case: (Hi pb _ H1 H2 _ (erefl _) H3 H4)=>{Hi D2 H4 H3 H2 H1}h[t][H1 H2].
rewrite Es (compute_chain_equiv (free (# b) bt) pb n (rem_uniq _ (uniq_dom _))
      (uniq_dom (free (# b) bt)) (dom_rem2 _ _)) H1.
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
move=>V H; apply: FCR_subchain.
by case: (btExtend_chain_prefix a b V H)=>p<-; exists p, [::]; rewrite cats0.
Qed.

Lemma init_chain bt :
  has_init_block bt ->
  compute_chain bt GenesisBlock = [:: GenesisBlock].
Proof.
rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n bt hs Es En=>[|n Hi] bt hs Es En Ib=>/=;
subst hs; move/find_some: (Ib).
- by move/esym/size0nil:En=>->.
move=>->; rewrite init_hash Ib compute_chain_no_block'//.
rewrite mem_rem_uniq; last by apply: uniq_dom.
by rewrite inE eqxx.
Qed.

Lemma all_chains_init bt :
  has_init_block bt -> [:: GenesisBlock] \in all_chains bt.
Proof.
move=>H; rewrite /all_chains; apply/mapP.
exists GenesisBlock; last by rewrite (init_chain H).
by apply/mapP; exists (# GenesisBlock);
[by move/find_some: H|by rewrite /get_block H].
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

Lemma btChain_mem2 (bt : BlockTree) (b : block) :
  valid bt -> has_init_block bt ->
  b \in btChain bt -> b ∈ bt.
Proof.
move=>V H.
move: (btChain_in_bt H); move: (btChain bt)=>bc H2 H1; clear H.
case/mapP:H2=>b0 _ Z; subst bc.
by apply: (@block_in_chain _ b0).
Qed.

Lemma btChain_mem (bt : BlockTree) (b : block) :
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
by apply/FCR_dual; apply: FCR_subchain; exists [::], t.
Qed.

(* This is going to be used for proving X1 in btExtend_sameOrBetter *)
Lemma better_chains1 bt b :
  valid (# b \\-> b \+ bt) ->
  # b \notin dom bt -> validH bt -> has_init_block bt ->
  let f := bc_fun bt in
  let f' := bc_fun (# b \\-> b \+ bt) in
  forall h bc' bc,
    bc' >= bc ->
    tx_valid_chain bc' /\ good_chain bc' ->
    tx_valid_chain bc /\ good_chain bc ->
    f' h bc' >= f h bc.
Proof.
move=>V B Vh H/=h bc' bc Gt [T' Gb'] [T Gb]; rewrite /bc_fun/=.
set bc2 := compute_chain (# b \\-> b \+ bt) b.
case E: (#b == h).
- move/eqP:E=>Z; subst h.
  rewrite /get_block !findPtUn//.
  have X: find (# b) bt = None.
  + case: validUn V=>//_ _/(_ (# b)); rewrite domPtK inE eqxx.
    by move/(_ is_true_true); case : dom_find=>//.
  rewrite !X init_chain//; clear X; rewrite /take_better_bc/=.
  case: ifP=>[/andP[X1 X2]|X]/=; rewrite (good_init Gb) andbC//=.
  + by right; apply: (FCR_trans_eq2 X2).
(* Now check if h \in dom bt *)
case D: (h \in dom bt); last first.
- rewrite /get_block (findUnL _ V) domPtK inE.
  case: ifP; first by case/negP; move/eqP => H_eq; move/negP: E; rewrite H_eq.
  move => H_eq {H_eq}.
  case: dom_find D=>//->_{E h}.
  rewrite /take_better_bc/= !init_chain//; last first.
  + by move: (btExtendIB b (validR V) Vh H); rewrite/btExtend(negbTE B).
  by rewrite !(good_init Gb)!(good_init Gb') -(andbC false)/=.
case: dom_find D=>//c F _ _.
rewrite /get_block (findUnL _ V) domPtK inE.
case: ifP; first by case/negP; move/eqP => H_eq; move/negP: E; rewrite H_eq.
move => H_eq {H_eq}.
rewrite !F.
move: (Vh h _ F); move/find_some: F=>D ?{E bc2}; subst h.
have P : exists p, p ++ (compute_chain bt c) = compute_chain (# b \\-> b \+ bt) c.
- by move: (btExtend_chain_prefix b c (validR V)Vh); rewrite /btExtend(negbTE B).
case:P=>p E; rewrite /take_better_bc.
case G1: (good_chain (compute_chain bt c))=>/=; last first.
- case G2: (good_chain (compute_chain (# b \\-> b \+ bt) c))=>//=.
  by case: ifP=>///andP[_ X]; right; apply: (FCR_trans_eq2 X).
(* Now need a fact about goodness monotonicity *)
move: (btExtend_compute_chain b (validR V) Vh H G1).
rewrite /btExtend (negbTE B)=>->; rewrite G1/=.
case:ifP=>[/andP[X1' X1]|X1]; case: ifP=>[/andP[X2' X2]|X2]=>//; do?[by left].
- by right; apply: (FCR_trans_eq2 X1 Gt).
by rewrite X2'/= in X1; move/FCR_dual: X1. 
Qed.

Lemma tx_valid_init : all [pred t | txValid t [::]] (txs GenesisBlock).
Proof.
elim: (txs GenesisBlock) => //= tx txs IH.
apply/andP; split => //.
exact: txValid_nil.
Qed.

Lemma tx_valid_chain_init : tx_valid_chain [:: GenesisBlock].
Proof.
rewrite /tx_valid_chain/=; apply/andP; split => //.
exact: tx_valid_init.
Qed.

Lemma good_chain_foldr bt bc ks :
  tx_valid_chain bc -> good_chain bc ->
  tx_valid_chain (foldr (bc_fun bt) bc ks) /\
  good_chain (foldr (bc_fun bt) bc ks).
Proof.
elim: ks=>//=x xs Hi T G; rewrite /bc_fun/take_better_bc/= in Hi *.
case: ifP=>[/andP[B1 B2]|B]; first by rewrite andbC in B1; move/andP: B1.
by apply: Hi. 
Qed.

Lemma good_chain_foldr_init bt ks :
  tx_valid_chain (foldr (bc_fun bt) [:: GenesisBlock] ks) /\
  good_chain (foldr (bc_fun bt) [:: GenesisBlock] ks).
Proof.
move: (@good_chain_foldr bt [:: GenesisBlock] ks tx_valid_chain_init)=>/=.
by rewrite eqxx=>/(_ is_true_true); case.
Qed.

Lemma good_foldr_init bt ks : good_chain (foldr (bc_fun bt) [:: GenesisBlock] ks).
Proof. by case: (good_chain_foldr_init bt ks). Qed.

Lemma tx_valid_foldr_init bt ks : tx_valid_chain (foldr (bc_fun bt) [:: GenesisBlock] ks).
Proof. by case: (good_chain_foldr_init bt ks). Qed.

Lemma better_chains_foldr bt b :
  valid (# b \\-> b \+ bt) ->
  # b \notin dom bt -> validH bt -> has_init_block bt ->
  let f := bc_fun bt in
  let f' := bc_fun (# b \\-> b \+ bt) in
  forall ks bc' bc,
    bc' >= bc ->
    tx_valid_chain bc' /\ good_chain bc' ->
    tx_valid_chain bc /\ good_chain bc ->
    foldr f' bc' ks >= foldr f bc ks.
Proof.
move=>V B Vh H f f'; elim=>//h hs Hi bc' bc Gt TG1 TG2 /=.
move: (Hi _ _ Gt TG1 TG2)=>{Hi}Hi.
case: TG1 TG2=>??[??].
by apply: better_chains1=>//; apply: good_chain_foldr=>//. 
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
case: (dom_insert V)=>ks1[ks2][->->]; rewrite -![# b :: ks2]cat1s.
rewrite !foldr_map -/(bc_fun bt) -/(bc_fun (# b \\-> b \+ bt)) !foldr_cat.
set f := (bc_fun bt).
set f' := (bc_fun (# b \\-> b \+ bt)).
have X1: foldr f' [:: GenesisBlock] ks2 >= foldr f [:: GenesisBlock] ks2.
 - elim: ks2=>//=[|k ks Hi]; first by left.
   by apply: better_chains1 ; rewrite ?B; do? [apply: good_chain_foldr_init]=>//.
apply: better_chains_foldr=>//;
do? [apply good_chain_foldr_init=>//]; [by apply/negbT| |]; last first.
- apply: good_chain_foldr; rewrite ?good_foldr_init ?tx_valid_foldr_init//.
simpl; rewrite {1 3}/f'/bc_fun/=/take_better_bc/=.
case:ifP=>///andP[B1 B2]. right.
apply: (FCR_trans_eq2 B2).
by apply: better_chains_foldr=>//=; [by apply/negbT|by left | |]; do?[rewrite ?tx_valid_chain_init ?eqxx//].
Qed.

Lemma btExtend_fold_comm (bt : BlockTree) (bs bs' : seq block) :
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

Lemma btExtend_fold_preserve (ob : block) bt bs:
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
by move=>H1 H2; move: (FCR_trans H1 H2); right.
Qed.

(* monotonicity of (btChain (foldl btExtend bt bs)) wrt. bs *)
Lemma btExtend_monotone_btChain (bs ext : seq block) bt:
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
by move=>H1 H2; move: (FCR_trans H1 H2); right.
Qed.

Lemma btExtend_not_worse (bt : BlockTree) (b : block) :
    valid bt -> validH bt -> has_init_block bt ->
    ~ (btChain bt > btChain (btExtend bt b)).
Proof.
move=>V Vh Ib;
move: (btExtend_sameOrBetter b V Vh Ib); case.
by move=>->; apply: (FCR_nrefl).
move=>H; case X: (btChain bt > btChain (btExtend bt b)); last done.
by move: (FCR_nrefl (FCR_trans H X)).
Qed.

Lemma btExtend_fold_not_worse (bt : BlockTree) (bs : seq block) :
    valid bt -> validH bt -> has_init_block bt ->
    ~ (btChain bt > btChain (foldl btExtend bt bs)).
Proof.
move=>V Vh Ib; move: (btExtend_fold_sameOrBetter bs V Vh Ib); case.
by move=><-; apply: FCR_nrefl.
by apply: FCR_excl.
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
  forall (bc : Blockchain) (bt : BlockTree) (b : block) (bs : seq block),
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
- rewrite h3 in h2; rewrite h2 in h0; contradict h0; apply: FCR_nrefl.
- by rewrite -h0 in h1; contradict h1; apply btExtend_fold_not_worse.
- by rewrite -h2 h3 in h0; contradict h0; apply: FCR_nrefl.
- by left; apply/eqP; rewrite eq_sym; rewrite -h3 in h1; apply/eqP.
- by rewrite -h3 in h1; rewrite -h1 in h2;
  contradict h2; apply btExtend_fold_not_worse.
- by rewrite -h3 in h0; rewrite h0 in h2; contradict h2; apply: FCR_nrefl.
- by rewrite h3 in h2; move: (FCR_trans h0 h2)=>C;
  contradict C; apply: FCR_nrefl.
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
by right; move: (FCR_trans h2 H).
done.
Qed.

(* Trivial sub-case of the original lemma; for convenience *)
Lemma btExtend_seq_sameOrBetter_fref' :
  forall (bc : Blockchain) (bt : BlockTree) (b : block) (bs : seq block),
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
Proof. by case=>h; case=>t=>eq; rewrite eq; apply FCR_ext. Qed.

Lemma ohead_hash b0 (bt : seq block) :
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

Lemma foldr1 {A B : Type} (f : A -> B -> B) (fin : B) (val : A) :
  foldr f fin [:: val] = f val fin.
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
  by case: ifP=>//=Y; right; apply:(FCR_trans_eq2 Y Hi).
move/eqP=>?; subst c; rewrite {1 3}/take_better_bc X/=.
by case: ifP=>//=Y; [by left|by move/FCR_dual: Y].
Qed.

Lemma btChain_good bt : good_chain (btChain bt).
Proof.
rewrite /btChain.
elim: (all_chains bt)=>[|bc bcs Hi]/=; first by rewrite eqxx.
rewrite {1}/take_better_bc; case:ifP=>//.
by case/andP=>/andP[->].
Qed.

Lemma btChain_tx_valid bt : tx_valid_chain (btChain bt).
Proof.
rewrite /btChain.
elim: (all_chains bt)=>[|bc bcs Hi]/=;first by rewrite tx_valid_chain_init.
rewrite {1}/take_better_bc; case:ifP=>//.
by case/andP=>/andP[_ ->].
Qed.

Lemma btChain_in_good_chains bt :
  has_init_block bt -> btChain bt \in good_chains bt.
Proof.
move=> Ib; rewrite/good_chains mem_filter; apply/andP; split;
by [rewrite btChain_good btChain_tx_valid | apply (btChain_in_bt Ib)].
Qed.

Lemma compute_chain_rcons bt c pc :
  valid bt -> validH bt -> #c \in dom bt ->
  find (prevBlockHash c) bt = Some pc ->
  compute_chain' bt c (dom bt) (size (dom bt)) =
  rcons (compute_chain' (free (# c) bt) pc
        (dom (free (# c) bt)) (size (dom (free (# c) bt)))) c.
Proof.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n c pc bt hs Es En=>[|n _]/= c pc bt hs Es En V Vh D F.
- subst hs; move/esym/size0nil: En=>Z.
  by rewrite Z in D.
rewrite D Es F; congr (rcons _ _).
have U1: uniq (seq.rem (# c) hs) by rewrite rem_uniq// Es uniq_dom.
have U2: uniq (dom (free (#c) bt)) by rewrite uniq_dom.
have N: n = (size (dom (free (# c) bt))).
- by apply: size_free=>//; rewrite -?Es//.
rewrite -N; clear N.
rewrite -(compute_chain_equiv (free (# c) bt) pc n U1 U2) Es//.
by apply: dom_rem2.
Qed.

Lemma compute_chain_noblock bt b c :
  valid bt -> validH bt ->
  #b \in dom bt ->
  b \notin compute_chain bt c ->
  compute_chain bt c = compute_chain (free (#b) bt) c.
Proof.
rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n c b bt hs Es En=>[|n Hi]/= c b bt hs Es En V Vh Hb.
- suff X: size (dom (free (# b) bt)) = 0
    by rewrite X=>/=_; case:ifP=>_; case:ifP.
  suff X: bt = Unit by subst bt; rewrite free0 dom0.
  subst hs; move/esym/size0nil: En=>Z.
  by apply/dom0E=>//z/=; rewrite Z inE.
(* These two seem to always appear in these proofs... *)
have H1: valid (free (# b) bt) by rewrite validF.
have H3: n = size (dom (free (# b) bt)).
- apply: size_free=>//; [by rewrite Es in En|by rewrite -Es].
case: ifP=>[X|X _]; rewrite Es in X; last first.
- rewrite -H3; clear Hi En H3; case:n=>//=[|n]; first by case:ifP.
  by rewrite domF inE X; case:ifP; case: ifP.
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
    suff K : #c \in dom (free (# b) bt) by rewrite K.
    by rewrite domF inE X (find_some F).
  (* Now need to derive a contradiction from H3 *)
  rewrite Es in En.
  have X: #c \in dom (free (# b) bt).
  + rewrite domF inE.
    case: ifP=>C; last by apply: (find_some F).
    by move/eqP/hashB_inj : C N=>->; rewrite eqxx.
  by move/esym/size0nil: H3=>E; rewrite E in X.

(* Now an interesting, inductive, case *)
case: dom_find D=>//pc F' _ _; rewrite F'=>Hn; rewrite -H3.
rewrite mem_rcons inE in Hn; case/norP: Hn=>/negbTE N Hn.
have Dc: #c \in dom (free (# b) bt).
  + rewrite domF inE.
    case: ifP=>C; last by apply: (find_some F).
    by move/eqP/hashB_inj : C N=>->; rewrite eqxx.

(* Now need to unfold massage the RHS of the goal with compute_chain', so
   it would match the Hi with (bt := free (# c) bt, c := pc) etc *)
have X: compute_chain' (free (# b) bt) c
                       (dom (free (# b) bt))
                       (size (dom (free (# b) bt))) =
        rcons (compute_chain' (free (# b) (free (# c) bt)) pc
                              (dom (free (# b) (free (# c) bt)))
                              (size (dom (free (# b) (free (# c) bt))))) c.
- rewrite freeF.
  have Z: (#b == #c) = false
    by apply/negP=>/eqP/hashB_inj=>?; subst c; rewrite eqxx in N.
  rewrite Z.
  (* Given everything in the context, this should be a trivial lemma,
     please extract it and prove (takig bt' = free (# b) bt) *)
  apply: compute_chain_rcons=>//; rewrite ?validF//.
  + by apply: validH_free.
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
  have X: # b \in seq.rem (# c) (dom bt).
    apply: rem_neq; last by rewrite -Es.
    by apply/negP => H_eq; by case/negP: Z.
  rewrite X in Hn.
  case: (find _ _) Hn=>[?|]; last by rewrite inE eqxx.
  by rewrite mem_rcons inE eqxx.
(* The interesting inductive case! *)
rewrite H3 X; congr (rcons)=>//.
have U1: uniq (seq.rem (# c) hs) by rewrite rem_uniq// Es uniq_dom.
have U2: uniq (dom (free (#c) bt)) by rewrite uniq_dom.
rewrite -(Hi pc b (free (#c) bt) (dom (free (# c) bt)) (erefl _)) ?validF//.
- rewrite -H3.
  rewrite ((compute_chain_equiv (free (# c) bt) pc n) U1 U2)//.
  by rewrite Es; apply: dom_rem2.
- (* prove out of H3 and N *)
  rewrite Es in En; apply: (size_free V En).
  by apply:(find_some F).
- by apply: validH_free.
- rewrite Es in Hb.
  rewrite domF inE eq_sym Hb.
  by case:ifP=>///eqP/hashB_inj?; subst c; rewrite eqxx in N.
rewrite -(compute_chain_equiv (free (# c) bt) pc n U1 U2)//.
by rewrite Es; apply: dom_rem2.
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
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n b bt hs Es En V Vh D Hp Nh=>[|n Hi] b bt hs Es En V Vh D Hp Nh/=.
- by rewrite -Es in D; move/esym/size0nil: En=>Z; rewrite Z in D.
rewrite {1}Es D Hp.
have H1: valid (free (# b) bt) by rewrite validF.
have H3: n = size (dom (free (# b) bt)).
- by apply: size_free=>//; rewrite Es in En.
case B: (#pb \in dom bt); last first.
- case: dom_find (B)=>//F _; rewrite F.
  rewrite -H3; clear Hi En H3; case:n=>//=[|n]; first by case:ifP.
  by rewrite domF inE B; case:ifP; case: ifP.
case: dom_find B=>// prev F _ _; rewrite F; congr (rcons _ _).
move/Vh/hashB_inj: F=>?; subst prev.
rewrite H3.
have U1: uniq (seq.rem (# b) hs) by rewrite Es rem_uniq// uniq_dom.
have U2: uniq (dom (free (# b) bt)) by rewrite uniq_dom.
rewrite (compute_chain_equiv (free (#b) bt) pb
                 (size (dom (free (# b) bt))) U1 U2)//.
by rewrite Es; apply: dom_rem2.
Qed.

Lemma btExtend_mint_ext bt bc b :
  let pb := last GenesisBlock bc in
  valid bt -> validH bt -> has_init_block bt ->
  bc = compute_chain bt pb ->
  good_chain bc ->
  prevBlockHash b = #pb ->
  VAF (proof b) bc (txs b) ->
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
  by rewrite domPtUn inE V' eqxx.
apply: compute_chain_prev=>//.
move: (VAF_nocycle Hv); rewrite E in HGood.
by rewrite (btExtend_compute_chain b V Vh Ib HGood) E.
Qed.

Lemma chain_from_last bt c :
  valid bt -> validH bt -> has_init_block bt ->
  c \in all_chains bt -> c = compute_chain bt (last GenesisBlock c).
Proof.
move=>V Vh Ib/mapP[b] H1 H2.
suff X: (last GenesisBlock (compute_chain bt b)) = b.
- by rewrite -H2 in X; rewrite X.
move/mapP:H1=>[h]; move =>D.
case: dom_find (D)=>//b' F _ _; move/Vh: (F)=>?; subst h.
rewrite /get_block F=>?; subst b'.
rewrite /compute_chain; clear H2 V Vh Ib.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n b bt hs Es En D F=>[|n Hi] b bt hs Es En D F/=.
- by rewrite -Es in D; move/esym/size0nil: En=>Z; rewrite Z in D.
by rewrite Es D; case (find _ _)=>[?|]//; rewrite last_rcons.
Qed.

Definition tx_valid_block bc (b : block) := all [pred t | txValid t bc] (txs b).

Lemma tx_valid_last_ind c b prefix:
  all [pred t | txValid t prefix] (txs b) ->
  tx_valid_chain' c (rcons prefix b) ->
  tx_valid_chain' (b :: c) prefix.
Proof. by move=>/=->->. Qed.

Lemma tx_valid_last c b :
  tx_valid_block c b -> tx_valid_chain c -> tx_valid_chain (rcons c b).
Proof.
move=>H1.
have P : all [pred t | txValid t c] (txs b) by [].
have Z: c = [::] ++ c by rewrite ?cats0 ?cat0s.
rewrite Z in P; rewrite /tx_valid_chain; clear Z.
move: [::] P => p.
elim: {-1}c p H1.
- by move=>p _ /= A _; rewrite cats0 in A; rewrite A.
move=>x xs Hi p T A/=/andP[Z1 Z2]; rewrite Z1//=.
by apply: (Hi (rcons p x) T _ Z2); rewrite cat_rcons.
Qed.

Lemma btExtend_mint_good_valid bt b :
  let bc := btChain bt in
  let pb := last GenesisBlock bc in
  valid bt -> validH bt -> has_init_block bt ->
  tx_valid_block bc b ->
  good_chain bc ->
  prevBlockHash b = #pb ->
  VAF (proof b) bc (txs b) ->
  good_chain (compute_chain (btExtend bt b) b) /\
  tx_valid_chain (compute_chain (btExtend bt b) b).
Proof.
move=>bc pb V Vh Ib Tb Gc Hp Hv.
(have: bc \in all_chains bt by move: (btChain_in_bt Ib))=>InC.
(have: bc = compute_chain bt pb by move: (chain_from_last V Vh Ib InC))=>C.
move: (btExtend_mint_ext V Vh Ib C Gc Hp Hv)=>->; subst bc.
rewrite/good_chain. case X: (rcons _ _)=>[|x xs].
contradict X; elim: (btChain bt)=>//.
have: (good_chain (btChain bt) = true)by [].
rewrite/good_chain/=; case X': (btChain _)=>[|h t]; first done.
move/eqP=>Eq; subst h; rewrite X' rcons_cons in X; case: X=> ??.
subst x xs; split=>//.
move: (btChain_tx_valid bt)=>Tc.
rewrite !X' in Tb Tc; rewrite -rcons_cons.
by apply: tx_valid_last.
Qed.

Lemma btExtend_mint bt b :
  let pb := last GenesisBlock (btChain bt) in
  valid bt -> validH bt -> has_init_block bt ->
  tx_valid_block (btChain bt) b ->
  prevBlockHash b = # pb ->
  VAF (proof b) (btChain bt) (txs b) = true ->
  btChain (btExtend bt b) > btChain bt.
Proof.
move=>lst V Vh Ib T mint Hv.
have HGood: good_chain (rcons (btChain bt) b).
- by move: (btChain_good bt); rewrite {1}/good_chain; case (btChain bt).
have Hvalid: tx_valid_chain (rcons (btChain bt) b).
- by move: (btChain_tx_valid bt); apply: tx_valid_last. 
have E: compute_chain (btExtend bt b) b = rcons (btChain bt) b.
- apply: (@btExtend_mint_ext _ (btChain bt) b V Vh
                             Ib _ (btChain_good bt) mint Hv).
  by move/(chain_from_last V Vh Ib): (btChain_in_bt Ib).
have HIn : rcons (btChain bt) b \in
           filter (fun c => good_chain c && tx_valid_chain c) (all_chains (btExtend bt b)).
- rewrite mem_filter HGood Hvalid/=-E/all_chains; apply/mapP.
  have V' : valid (btExtend bt b) by rewrite -btExtendV.
  exists b=>//; rewrite /all_blocks/btExtend in V'*; apply/mapP; exists (#b).
  + by case:ifP V'=>X V'//; rewrite domPtUn inE eqxx andbC.
  rewrite /get_block; case:ifP V'=>X V'; last by rewrite findPtUn.
  case: dom_find X=>//b' F _ _; move/Vh/hashB_inj :(F)=> ?.
  by subst b'; rewrite F.
move/btChain_is_largest: HIn=>H; apply: (FCR_trans_eq1 H).
by rewrite -cats1; apply: FCR_ext.
Qed.

(***********************************************************)
(*******      </btExtend_mint and all it needs>     ********)
(***********************************************************)

Definition good_bt bt :=
  forall b, b \in all_blocks bt ->
            good_chain (compute_chain bt b) && tx_valid_chain (compute_chain bt b).

Lemma btExtend_good_chains_fold  bt bs:
  valid bt -> validH bt -> has_init_block bt ->
  {subset good_chains bt <= good_chains (foldl btExtend bt bs) }.
Proof.
move=>V Vh Hib c; rewrite !mem_filter=>/andP[G]; rewrite G/=.
rewrite/good_chains/all_chains=>/mapP[b]H1 H2; apply/mapP; exists b.
- apply/mapP; exists (#b).
  + apply/(btExtend_dom_fold bs V).
    case/mapP: H1=>z; move=>D.
    rewrite /get_block; case: (@dom_find _ _ _ z) (D)=>//b' F _ _.
    by rewrite F=>Z; subst b'; move/Vh: F=><-.
  case/mapP: H1=>z; move=>D.
  move/(btExtend_dom_fold bs V): (D)=>D'.
  rewrite {1}/get_block; case:dom_find (D)=>//b' F _ _.
  rewrite F=>?; subst b'. move/Vh: F=>?; subst z.
  rewrite /get_block; case:dom_find (D')=>//b' F _ _.
  by rewrite F; move/(@btExtendH_fold _ bs V Vh): F=>/hashB_inj.
rewrite btExtend_compute_chain_fold=>//; rewrite -H2.
by case/andP: G.
Qed.

Lemma good_chains_subset bt :
  { subset good_chains bt <= all_chains bt }.
Proof. by move=>ch; rewrite mem_filter; move/andP=>[]. Qed.

Lemma btExtend_new_block cbt b :
  valid cbt ->
  # b \notin dom cbt ->
  b \in all_blocks (btExtend cbt b).
Proof.
move=>V N; move: (V); rewrite (btExtendV _ b)=>V'.
move/negbTE: N=>N.
rewrite /btExtend !N in V' *.
case:(@dom_insert _ _ (#b) b cbt V')=>ks1[ks2][_].
rewrite /all_blocks=>->.
apply/mapP; exists (#b); last first.
- by rewrite /get_block findUnL// domPt inE eqxx findPt.
by rewrite mem_cat orbC inE eqxx.
Qed.

Lemma btExtend_get_block bt b k :
  valid bt -> #b \notin dom bt -> k != #b ->
  get_block (btExtend bt b) k = get_block bt k.
Proof.
move=>V D N; rewrite /get_block/btExtend (negbTE D).
rewrite findUnL; last by move: (btExtendV bt b); rewrite /btExtend(negbTE D)=><-.
by rewrite domPt inE eq_sym (negbTE N).
Qed.

Lemma good_chain_rcons bc b :
  good_chain bc -> good_chain (rcons bc b).
Proof. by move=>Gc; elim: bc Gc=>//. Qed.

Lemma btExtend_good_split cbt b :
  valid cbt -> validH cbt -> has_init_block cbt ->
  good_bt cbt -> #b \notin dom cbt -> good_bt (btExtend cbt b) ->
  exists cs1 cs2,
    good_chains cbt = cs1 ++ cs2 /\
    good_chains (btExtend cbt b) = cs1 ++ [:: compute_chain (btExtend cbt b) b] ++ cs2.
Proof.
move=>V Vh Hib Hg N Hg'.
have G: good_chain (compute_chain (btExtend cbt b) b).
- by case/andP: (Hg' b (btExtend_new_block V N)).
have T: tx_valid_chain (compute_chain (btExtend cbt b) b).
- by case/andP: (Hg' b (btExtend_new_block V N)).
have Eb: btExtend cbt b = (#b \\-> b \+ cbt) by rewrite /btExtend (negbTE N).
move: (V); rewrite (btExtendV _ b)=>V'; rewrite !Eb in V' *.
move: (@dom_insert _ _ (#b) b cbt V')=>[ks1][ks2][Ek]Ek'.
(* Massaging the left part *)
set get_chain := [eta compute_chain cbt] \o [eta get_block cbt].
rewrite /good_chains{1}/all_chains/all_blocks -!seq.map_comp Ek map_cat filter_cat.
rewrite -/get_chain.
exists [seq c <- [seq get_chain i | i <- ks1] | good_chain c & tx_valid_chain c],
       [seq c <- [seq get_chain i | i <- ks2] | good_chain c & tx_valid_chain c]; split=>//.
rewrite /all_chains/all_blocks Ek' /= -cat1s.
have [N1 N2] : (#b \notin ks1) /\ (#b \notin ks2).
- have U : uniq (ks1 ++ # b :: ks2) by rewrite -Ek'; apply:uniq_dom.
  rewrite cat_uniq/= in U; case/andP: U=>_/andP[]H1 H2.
  case/andP:H2=>->_; split=>//; by case/norP: H1.
have [D1 D2] : {subset ks1 <= dom cbt} /\ {subset ks2 <= dom cbt}.
- by split=>k; rewrite Ek mem_cat=>->//; rewrite orbC.
rewrite !map_cat !filter_cat ; congr (_ ++ _); clear Ek Ek'.
- rewrite -!Eb;elim: ks1 N1 D1=>//k ks Hi/= N1 D1.
  have Dk: k \in dom cbt by apply: (D1 k); rewrite inE eqxx.
  have Nk: k != #b by apply/negbT/negP=>/eqP=>?; subst k; rewrite inE eqxx in N1 .
  rewrite !(btExtend_get_block V N Nk); rewrite /get_chain/=.
  set bk := (get_block cbt k).
  have Gk: good_chain (compute_chain cbt bk) && tx_valid_chain (compute_chain cbt bk).
  - by apply: Hg; apply/mapP; exists k.
  case/andP: (Gk)=>Gg Gt.
  rewrite !(btExtend_compute_chain b V Vh Hib Gg) !Gk/=.
  congr (_ :: _); apply: Hi; first by rewrite inE in N1; case/norP:N1.
  by move=>z=>D; apply: D1; rewrite inE D orbC.
rewrite -[(compute_chain _ b) :: _]cat1s; congr (_ ++ _)=>/=; rewrite -!Eb.
- suff D: (get_block (btExtend cbt b) (# b)) = b by rewrite D G T.
  by rewrite /get_block/btExtend (negbTE N) findUnL ?V'// domPt inE eqxx findPt.
elim: ks2 N2 D2=>//k ks Hi/= N2 D2.
have Dk: k \in dom cbt by apply: (D2 k); rewrite inE eqxx.
have Nk: k != #b by apply/negbT/negP=>/eqP=>?; subst k; rewrite inE eqxx in N2.
rewrite !(btExtend_get_block V N Nk); rewrite /get_chain/=.
set bk := (get_block cbt k).
have Gk: good_chain (compute_chain cbt bk) && tx_valid_chain (compute_chain cbt bk).
- by apply: Hg; apply/mapP; exists k.
case/andP: (Gk)=>Gg Gt.  
rewrite !(btExtend_compute_chain b V Vh Hib Gg) !Gk/=.
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
by case C: (good_chain c && tx_valid_chain c)=>//=; rewrite !Hi.
Qed.

Lemma best_chain_in cs :
  foldr take_better_alt [:: GenesisBlock] cs = [:: GenesisBlock] \/
  foldr take_better_alt [:: GenesisBlock] cs \in cs.
Proof.
elim: cs=>[|c cs Hi]; [by left|].
rewrite /take_better_alt/=; case:ifP; rewrite -/take_better_alt=>X.
- by right; rewrite inE eqxx.
case/FCR_dual: X=>X.
- by rewrite !X in Hi *; right; rewrite inE eqxx.
by case: Hi=>H; [left| right]=>//; rewrite inE orbC H.
Qed.

Lemma foldr_better_mono bc cs : foldr take_better_alt bc cs >= bc.
Proof.
elim: cs=>//=[|c cs Hi/=]; first by left.
rewrite {1 3}/take_better_alt; case: ifP=>G//.
by right; apply:(FCR_trans_eq2 G Hi).
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
    by move/Hi: (FCR_trans G2 G1)=>G3; move/G3.
  rewrite inE; case/orP; last by move/(Hi G2).
  move/eqP=>?; subst z; case/FCR_dual: G1=>G1; first by rewrite !G1 in G2.
  by apply: (FCR_trans G2 G1).
have [G1 G2]: ((forall z, z \in cs1 -> bc > z) /\
               forall z, z \in cs2 -> bc > z).
- split=>z H; move: (G z); rewrite mem_cat H/=; first by move/(_ is_true_true).
  by rewrite orbC; move/(_ is_true_true).
clear G.
have Z: bc = bc'.
- suff C: bc \in [:: bc'] ++ cs2.
  + elim: (cs2) C G2=>//=[|c cs Hi C G2]; first by rewrite inE=>/eqP.
    rewrite inE in C; case/orP:C; first by move/eqP.
    by move/G2; move/FCR_nrefl.
  elim: (cs1) G1 H2=>//=c cs Hi G1 H2.
  rewrite inE in H2; case/orP: H2.
  + move/eqP=>Z; subst c; move: (G1 bc).
    by rewrite inE eqxx/==>/(_ is_true_true)/FCR_nrefl.
  rewrite mem_cat; case/orP=>// G.
  by move: (G1 bc); rewrite inE orbC G/==>/(_ is_true_true)/FCR_nrefl.
subst bc'; clear H1 H2.
(* Ok, here comes the final blow *)
suff C: bc = foldr take_better_alt [:: GenesisBlock] ([:: bc] ++ cs2).
- rewrite foldr_cat -C; clear C.
  elim: cs1 G1=>//c cs Hi G1; rewrite /take_better_alt/=-/take_better_alt.
  case: ifP=>G.
  - move: (FCR_trans_eq2 G (foldr_better_mono bc cs))=>G'.
    move: (G1 c). rewrite inE eqxx/==>/(_ is_true_true) G3.
    by move: (FCR_nrefl (FCR_trans G' G3)).
  by case/FCR_dual: G=>G;
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

Lemma better_comm bc x y :
  take_better_alt (take_better_alt bc x) y =
  take_better_alt (take_better_alt bc y) x.
Proof.
rewrite/take_better_alt.
case X: (bc > x); case Y: (bc > y).
  by rewrite X.
case/FCR_dual: Y=>H.
  by subst bc; rewrite X.
  by move: (FCR_trans H X)=>->.
case/FCR_dual: X=>H.
  by subst bc; rewrite Y; case: ifP=>//=.
  by move: (FCR_trans H Y)=>->; case: ifP=>//=;
     move=>H'; move: (FCR_nrefl (FCR_trans H H')).
case/FCR_dual: X; case/FCR_dual: Y.
  by move=>->->; case: ifP=>//=.
  by move=>H Eq; subst bc; rewrite H; case: ifP=>//=;
     move=>H'; move: (FCR_nrefl (FCR_trans H H')).
  by move=>-> H; rewrite H; case: ifP=>//=;
     move=>H'; move: (FCR_nrefl (FCR_trans H H')).
case: ifP; case: ifP=>//=.
  by move=>H H'; move: (FCR_nrefl (FCR_trans H H')).
case/FCR_dual=>X; case/FCR_dual=>Y//.
  by move: (FCR_nrefl (FCR_trans X Y)).
Qed.

Lemma better_comm' x y :
  take_better_alt x y = take_better_alt y x.
Proof.
rewrite/take_better_alt; case: ifP; case: ifP; do? by [].
by move=>H1 H2; move: (FCR_nrefl (FCR_trans H1 H2)).
move/FCR_dual=>H1/FCR_dual H2; case: H1; case: H2; do? by [].
by move=>H1 H2; move: (FCR_nrefl (FCR_trans H1 H2)).
Qed.

Lemma foldl_better_comm bc cs1 cs2 :
  foldl take_better_alt (foldl take_better_alt bc cs1)
    cs2 =
  foldl take_better_alt (foldl take_better_alt bc cs2)
    cs1.
Proof.
elim/last_ind: cs1=>[|xs x Hi]/=; first done.
rewrite -cats1 !foldl_cat -Hi; clear Hi.
elim/last_ind: cs2=>[|ys y Hi]/=; first done.
rewrite -cats1 !foldl_cat Hi /=; apply better_comm.
Qed.

Lemma foldl_better_comm_cat bc cs1 cs2 :
  foldl take_better_alt bc (cs1 ++ cs2) =
  foldl take_better_alt bc (cs2 ++ cs1).
Proof. by rewrite !foldl_cat; apply foldl_better_comm. Qed.

Lemma foldl_foldr_better bc cs :
  foldr take_better_alt bc cs =
  foldl take_better_alt bc cs.
Proof.
elim: cs=>//[x xs Hi].
rewrite -(@cat1s _ x xs) foldr_cat foldl_cat /=.
rewrite better_comm' -(@foldl1 _ _ _ bc x).
by rewrite -foldr1 foldl_better_comm /= Hi.
Qed.

Lemma foldl_better_reduce bc cs :
  bc > [:: GenesisBlock] ->
  foldl take_better_alt bc cs =
  take_better_alt bc (foldl take_better_alt [:: GenesisBlock] cs).
Proof.
move=>Gt; elim/last_ind: cs=>/=[|cs c Hi].
  by rewrite/take_better_alt Gt.
rewrite -cats1 !foldl_cat /= Hi.
rewrite{1 2 4}/take_better_alt.
case X: (bc > foldl take_better_alt [:: GenesisBlock] cs).
- case: ifP.
  by move=>Y; rewrite{1}/take_better_alt; case: ifP=>//=;
     case: ifP; do? by [rewrite X|rewrite Y].
  case/FCR_dual=>Y.
    by subst c; rewrite{1 3}/take_better_alt; case: ifP=>//=;
       case: ifP=>//= Y; move: (FCR_nrefl (FCR_trans X Y)).
    rewrite{1 3}/take_better_alt; case: ifP.
      by case: ifP=>//= Z;
         [move: (FCR_nrefl (FCR_trans X (FCR_trans Z Y))) |
          move=>Y'; move: (FCR_nrefl (FCR_trans Y Y'))].
      case: ifP=>//=.
        by move=>Z; move: (FCR_nrefl (FCR_trans X (FCR_trans Z Y))).
- case/FCR_dual: X=>H.
  by rewrite H; case: ifP=>//= X;
     rewrite/take_better_alt X /=; case: ifP=>//=; by rewrite X.
  case: ifP.
  * move=>X; case: ifP=>//=.
      by rewrite{1}/take_better_alt X=>H'; move: (FCR_nrefl (FCR_trans H H')).
  * rewrite{1}/take_better_alt X /=; case/FCR_dual=>Y.
      by subst bc; move: (FCR_nrefl H).
      by rewrite{2}/take_better_alt X /=.
  case/FCR_dual=>X;
  rewrite{1 3}/take_better_alt; case: ifP; case: ifP=>//=.
    by rewrite X; move=>Y; move: (FCR_nrefl Y).
    by rewrite X; move=>_ H'; move: (FCR_nrefl (FCR_trans H H')).
    by move=>X'; move: (FCR_nrefl (FCR_trans X X')).
    by move=>_ H'; move: (FCR_nrefl (FCR_trans H (FCR_trans H' X))).
  by move=>X'; move: (FCR_nrefl (FCR_trans X X')).
Qed.

Lemma foldl_better_extract bc cs1 cs2 :
  foldl take_better_alt [:: GenesisBlock] (cs1 ++ [:: bc] ++ cs2) =
  foldl take_better_alt [:: GenesisBlock] (cs1 ++ cs2 ++ [:: bc]).
Proof.
rewrite (@foldl_better_comm_cat [:: GenesisBlock] cs1 ([:: bc] ++ cs2)).
move: (@foldl_better_comm_cat [:: GenesisBlock] (cs1 ++ cs2) [:: bc]).
by rewrite -!catA; move=>->/=; apply foldl_better_comm_cat.
Qed.

Lemma lesser_elim bc cs1 cs2 :
  bc > [:: GenesisBlock] ->
  foldr take_better_alt [:: GenesisBlock] (cs1 ++ cs2) > bc ->
  foldr take_better_alt [:: GenesisBlock] (cs1 ++ cs2) >=
  foldr take_better_alt [:: GenesisBlock] (cs1 ++ [:: bc] ++ cs2).
Proof.
rewrite !foldl_foldr_better=>H G.
rewrite (@foldl_better_comm_cat [:: GenesisBlock] cs1 ([:: bc] ++ cs2)).
rewrite (@foldl_cat _ _ _ [:: GenesisBlock] ([:: bc] ++ cs2)).
rewrite /= better_comm'.
have X: take_better_alt bc [:: GenesisBlock] = bc.
  by rewrite/take_better_alt H.
rewrite X.
rewrite -(@foldl_cat _ _ take_better_alt bc).
rewrite (@foldl_better_comm_cat bc cs2 cs1).
set cs := (cs1 ++ cs2) in G *.
rewrite (@foldl_better_reduce bc)=>//.
rewrite{2}/take_better_alt; case: ifP.
  by move=>G'; move: (FCR_nrefl (FCR_trans G G')).
  case/FCR_dual=>[Eq|_].
   by rewrite Eq in G; move: (FCR_nrefl G).
   by left.
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
  case/andP:H1; case/andP=>/good_init/FCR_dual; case=>//H _.
  subst bc; rewrite H in Gt.
  move: (btChain_in_good_chains Hib); rewrite /good_chains mem_filter.
  by case/andP; case/andP=>/good_init; rewrite Gt.
clear Vl Vhl Hil Ec. (* Let's forget about bt. *)
case: (btExtend_good_split V Vh Hib Hg Nb Hg')=>cs1[cs2][E1]E2.
rewrite !btChain_alt in Gt *; rewrite E1 in Gt; rewrite !E2 in H1 *.
have I: [:: GenesisBlock] \in cs1 ++ cs2.
- rewrite -E1 mem_filter/= eqxx/=; apply/andP; split=>//; last by apply:all_chains_init.
  exact: tx_valid_chain_init.
by apply: best_element_in.
Qed.

Lemma btExtend_with_new cbt bt bs b :
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
by move/FCR_dual: (btExtend_fold_sameOrBetter bs G1 G2 G3); rewrite Gt.
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

Lemma geq_genesis bt :
  btChain bt >= [:: GenesisBlock].
Proof. by rewrite btChain_alt; apply foldr_better_mono. Qed.

Lemma in_ext bt b : valid bt -> b ∈ btExtend bt b.
Proof.
by move=>V; rewrite/btHasBlock/btExtend; case: ifP=>//=;
   rewrite domPtUnE validPtUn V /==>H; apply/negP; rewrite H.
Qed.

Lemma btExtend_within cbt bt b bs :
  valid cbt -> validH cbt -> has_init_block cbt ->
  valid bt -> validH bt -> has_init_block bt ->
  good_bt cbt -> good_bt (btExtend cbt b) ->
  tx_valid_block (btChain bt) b ->
  btChain cbt >= btChain (btExtend bt b) ->
  prevBlockHash b = # last GenesisBlock (btChain bt) ->
  VAF (proof b) (btChain bt) (txs b) ->
  cbt = foldl btExtend bt bs ->
  btChain (btExtend cbt b) > btChain cbt -> False.
Proof.
move=>V Vh Hib Vl Vhl Hil Hg Hg' T Geq P Vf Ec Cont.
case Nb: (#b \in dom cbt); first by rewrite /btExtend Nb in Cont; apply: FCR_nrefl Cont.
case: (btExtend_good_split V Vh Hib Hg (negbT Nb) Hg')=>cs1[cs2][Eg][Eg'].
move: (btExtend_mint_good_valid Vl Vhl Hil T (btChain_good bt) P Vf)=>[Gb Tb].
move: (FCR_trans_eq2 Cont Geq)=>Gt'.

have v1': (valid (btExtend bt b)) by rewrite -btExtendV.
have v2': (validH (btExtend bt b)) by apply btExtendH.
have v3': (has_init_block (btExtend bt b)) by apply btExtendIB.

have R: (btChain (btExtend bt b) =
         foldr take_better_alt [:: GenesisBlock] (good_chains (btExtend bt b)))
  by rewrite btChain_alt.
rewrite !btChain_alt Eg Eg' -R in Geq Gt' Cont.

have H0: compute_chain (btExtend bt b) b \in good_chains (btExtend bt b).
  rewrite/good_chains mem_filter Gb Tb /=;
  rewrite/all_chains; apply/mapP; exists b=>//;
  apply/all_blocksP'; by [apply btExtendH| apply in_ext].
move: (btChain_is_largest H0)=>H; clear H0.
move: (FCR_trans_eq2 Gt' H)=>Gt; clear H.

have Eq: compute_chain (btExtend bt b) b = compute_chain (btExtend cbt b) b.
rewrite Ec -(@foldl1 _ _ btExtend (foldl _ _ _)) btExtend_fold_comm /= //.
apply/eqP; rewrite eq_sym; apply/eqP; apply btExtend_compute_chain_fold=>//.

rewrite Eq in Gt. move: Gt.
rewrite foldl_foldr_better.
rewrite (foldl_better_extract (compute_chain (btExtend cbt b) b) cs1 cs2).
rewrite catA (@foldl_cat _ _ _ [:: GenesisBlock] (cs1 ++ cs2)) /=.
rewrite{1}/take_better_alt; case: ifP=>//;
last by move=>_ X; apply (FCR_nrefl X).
rewrite -Eq in Gt' Cont *=>H; clear Eq; move=>_.

(* Cont and H are contradictory *)
move: Cont.
rewrite foldl_foldr_better.
rewrite (foldl_better_extract (compute_chain (btExtend bt b) b) cs1 cs2).
rewrite catA (@foldl_cat _ _ _ [:: GenesisBlock] (cs1 ++ cs2)) /=.
rewrite -foldl_foldr_better in H *.
rewrite{1}/take_better_alt; case: ifP.
by move=>_ X; apply (FCR_nrefl X).
by move=>_ H'; apply (FCR_nrefl (FCR_trans H H')).
Qed.

Lemma btExtend_can_eq cbt bt b bs :
  valid cbt -> validH cbt -> has_init_block cbt ->
  valid bt -> validH bt -> has_init_block bt ->
  good_bt cbt -> good_bt (btExtend cbt b) ->
  tx_valid_block (btChain bt) b ->
  btChain cbt >= btChain (btExtend bt b) ->
  prevBlockHash b = # last GenesisBlock (btChain bt) ->
  VAF (proof b) (btChain bt) (txs b) ->
  cbt = foldl btExtend bt bs ->
  btChain (btExtend cbt b) = btChain cbt.
Proof.
move=>V Vh Hib Vl Vhl Hil Hg Hg' T Geq P Vf Ec.
case: (btExtend_sameOrBetter b V Vh Hib)=>//H1.
by move: (btExtend_within V Vh Hib Vl Vhl Hil Hg Hg' T Geq P Vf Ec H1). 
Qed.

End BtChainProperties.
