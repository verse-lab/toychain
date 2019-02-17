From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Protocol Blocks Chains Parameters Forests States Network InvMisc.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************************************************************)
(* Global Invariant: Clique consensus. *)

(* Under assumption of a clique network topology (every node is
connected to every other node), ensures that any node's local
blockchain will become _exactly_ the "canonical" blokchain, once all
blocks towars it "in flight" are received and used to extend the local
block tree. *)
(*******************************************************************)

Module CliqueConsensus (P : ConsensusParams) (F : Forest P)
                       (Pr : ConsensusProtocol P F) (Ns : NetState P F Pr)
                       (C : ConsensusNetwork P F Pr Ns)
                       (Ip : InvProps P F Pr Ns C).
Import P F Pr Ns C Ip.

Definition GSyncing_clique w :=
  (* There exists a priviledged node, "canonical" blocktree and blockchain *)
  exists (bc : Blockchain) (bt : BlockTree) (n : Address),
    (* The priviledged node holds the canonical blockchain,
        BUT not neccessarily the canonical blocktree!
     *)
    (* "can_bc" has no meaning if can_bt is invalid. *)
  [/\ holds n w (has_chain bc) \/ ~~ valid bt,

   (* Either:
      a) the canonical chain is largest in the network, OR
      b) a hash collision has occured
    *)
   (valid_with_bc bt bc /\ largest_chain w bc) \/ ~~ valid bt,

   (* bt is complete *)
   good_bt bt,

   (* Clique topology *)
   forall n', holds n' w (fun st => {subset (dom (localState w)) <= peers st}) &

   (* Relating global and local block-trees *)
   forall n',
     holds n' w (fun st => bt = foldl btExtend (blockTree st) (blocksFor n' w))
  ].

Definition clique_inv (w : World) :=
  Coh w /\ GSyncing_clique w.

Lemma clique_eventual_consensus w :
  clique_inv w -> (forall n, blocksFor n w == [::]) ->
  exists bc, largest_chain w bc /\
  forall n, holds n w (fun st => (has_chain bc st)).
Proof.
case=>C; case=>[bc][bt][can_n] [H1 H2 H3 H4 H5]=>N; case: H2=>[[V Gt]|V].
exists bc; split=>// n st Fw; move: (N n)=>Na; move/eqP:Na=>Na.
move:(H5 n _ Fw); rewrite Na/= /has_chain=><-; rewrite eq_sym; apply/eqP.
by move: V; rewrite/valid_with_bc=>[] [] _.
(* After a hash collision, the GenesisBlock is the canonical chain. *)
(* Once this is propagated, it becomes the largest chain. *)
exists [::GenesisBlock]; split; last first.
move=>n st Fw; move: (N n)=>Na; move/eqP: Na=>Na; move:(H5 n _ Fw);
rewrite Na/= /has_chain=><-; rewrite eq_sym; apply/eqP.
by move/invalidE: V=>->; rewrite/btChain/all_chains/all_blocks dom_undef.
rewrite/largest_chain/has_chain=>n' bc'.
move: (H5 n'); rewrite/holds=>X st F; move: (X st F); move: (N n')=>/eqP-> //= <- /eqP;
move/invalidE: V=>->; rewrite/btChain/all_chains/all_blocks dom_undef //=.
by left.
Qed.

(*********************************************************)
(*                  Auxiliary Lemmas                     *)
(*********************************************************)

Lemma procMsg_nGetData_no_blocks st p q stPm ms n' :
  procMsg st (src p) (msg p) (ts q) = (stPm, ms) ->
  msg_type (msg p) != MGetData ->
  all (pred1 GenesisBlock) [seq msg_block (msg p0) | p0 <- ms & dst p0 == n'].
Proof.
rewrite [procMsg _ _ _ _]surjective_pairing; case=>_{stPm}<-{ms}.
case (msg p); rewrite /procMsg/=; case: st=>id ps bt tp GD/=.
- move=>pt; apply/allP=>m; rewrite !inE.
  move/mapP=>[z]; rewrite mem_filter/emitMany/emitBroadcast=>/andP[_].
  case filter => //= s l; rewrite inE;move/orP.
  case; first by move/eqP => H_eq; rewrite H_eq; move/eqP.
  by rewrite mem_cat=>/orP[]/=; move/mapP=>[y]_->->/=; rewrite eqxx.
- by apply/allP=>b; case: ifP=>//_; rewrite inE=>/eqP->/=;rewrite eqxx.
- move=>c; apply/allP=>b/mapP[z]; rewrite mem_filter=>/andP[_].
  by move/mapP=>[n]_->->/=; rewrite eqxx.
- move=>t; apply/allP=>z/mapP[y]; rewrite mem_filter=>/andP[_].
  by move/mapP=>[n]_->->/=; rewrite eqxx.
- move=>l; apply/allP=>z/mapP[y]; rewrite mem_filter=>/andP[_].
  by move/mapP=>[m]_->->/=; rewrite eqxx.
move=>t; apply/allP=>z/mapP[y]; case:ifP=>X//=.
Qed.

Lemma btExtend_foldG bt bs :
  has_init_block bt ->
  all (pred1 GenesisBlock) bs ->
  (foldl btExtend bt bs) = bt.
Proof.
move=>F; move/all_pred1P=>->; rewrite/nseq/ncons/iter/=.
elim: (size bs)=>//n Hi/=.
rewrite/has_init_block in F; move: (find_some F)=>D.
have H: (GenesisBlock ∈ bt) by rewrite/btHasBlock F D=>//=.
by move: (btExtend_withDup_noEffect H)=><-.
Qed.

Lemma foldl1 {A B : Type} (f : A -> B -> A) (init : A) (val : B) :
  foldl f init [:: val] = f init val.
Proof. done. Qed.

Lemma btExtend_undef b :
  btExtend um_undef b = um_undef.
Proof. by rewrite/btExtend dom_undef in_nil join_undefR. Qed.

Lemma btExtend_fold_undef bs :
  foldl btExtend um_undef bs = um_undef.
Proof.
elim/last_ind: bs=>//=bs b; rewrite -cats1 foldl_cat=>->//=; apply btExtend_undef.
Qed.

Lemma btChain_undef :
  btChain um_undef = [:: GenesisBlock].
Proof. by rewrite/btChain/all_chains/all_blocks dom_undef //=. Qed.

Lemma btChain_gt_valid bt0 b bt:
  btChain (btExtend bt0 b) > btChain bt ->
  valid (btExtend bt0 b).
Proof.
case V': (valid (btExtend bt0 b))=>//=.
case V: (valid bt); last first.
by move/negbT: V; move/invalidE=>->; move/negbT: V'; move/invalidE=>->;
   rewrite btChain_undef=>E; move: (FCR_nrefl E).
move/negbT: V'; move/invalidE=>->; rewrite btChain_undef.
move: (geq_genesis bt)=>Y X.
by move: (FCR_trans_eq2 X Y)=>E; move: (FCR_nrefl E).
Qed.

Lemma rem_non_block' w bt p :
  validH bt ->
  has_init_block bt -> (forall b : Block, msg p != BlockMsg b) ->
  foldl btExtend bt [seq msg_block (msg p0) |
                 p0 <- seq.rem p (inFlightMsgs w) & dst p0 == dst p] =
  foldl btExtend bt [seq msg_block (msg p0) |
                 p0 <- inFlightMsgs w & dst p0 == dst p].
Proof.
move=>Vh H Nb.
case B: (p \in (inFlightMsgs w)); last by move/negbT/rem_id: B=>->.
case: (in_seq_neq B)=>xs [ys][E]; rewrite E=>Ni{B}.
rewrite rem_elem// !filter_cat !map_cat !foldl_cat/= eqxx map_cons.
have X: msg_block (msg p) = GenesisBlock.
- by case: (msg p) Nb=>//b Nb; move: (Nb b); move/negbTE; rewrite eqxx.
rewrite X -cat1s foldl_cat; clear X.
have A : all (pred1 GenesisBlock) [:: GenesisBlock] by rewrite /=eqxx.
case V: (valid (foldl btExtend bt
          [seq msg_block (msg p0) | p0 <- xs & dst p0 == dst p])).
by rewrite (btExtend_foldG _ A)//; apply: btExtendIB_fold=>//=.
move: V; rewrite -Bool.negb_true_iff=>V; move/invalidE: V=>->.
by rewrite !btExtend_fold_undef.
Qed.

(* TODO: replace uses in invariant with above version*)
Lemma rem_non_block w bt p :
  valid (foldl btExtend bt [seq msg_block (msg p0) |
                 p0 <- inFlightMsgs w & dst p0 == dst p]) ->
  validH bt ->
  has_init_block bt -> (forall b : Block, msg p != BlockMsg b) ->
  foldl btExtend bt [seq msg_block (msg p0) |
                 p0 <- seq.rem p (inFlightMsgs w) & dst p0 == dst p] =
  foldl btExtend bt [seq msg_block (msg p0) |
                 p0 <- inFlightMsgs w & dst p0 == dst p].
Proof. by move=>V Vh Ib Nb; apply rem_non_block'. Qed.

Lemma rem_block w bt p b :
  valid bt ->
  validH bt ->
  p \in (inFlightMsgs w) ->
  msg p = BlockMsg b ->
  foldl btExtend (btExtend bt b)
       [seq msg_block (msg p0) | p0 <- seq.rem p (inFlightMsgs w) & dst p0 == dst p] =
  foldl btExtend bt
       [seq msg_block (msg p0) | p0 <- inFlightMsgs w & dst p0 == dst p].
Proof.
move=>V Vh B X.
case: (in_seq_neq B)=>xs [ys][E]; rewrite E=>Ni{B}.
rewrite rem_elem//; clear E Ni.
elim: xs; first by rewrite //= eq_refl -cat1s map_cat foldl_cat //= X.
move=>x xs H.
rewrite -cat1s -!catA !filter_cat !map_cat //= eq_refl.
case: ifP=>_; last first.
- have Q: [seq msg_block (msg p0) | p0 <- [::]] = [::] by [].
  by rewrite Q !cat0s -!map_cat -!filter_cat H {1}filter_cat {1}map_cat;
     rewrite map_cat -cat1s filter_cat map_cat //= eq_refl.

rewrite (foldl_cat _ (btExtend bt b) [seq msg_block (msg p0) | p0 <- [:: x]]).
rewrite (foldl_cat _ bt [seq msg_block (msg p0) | p0 <- [:: x]]).
rewrite btExtend_fold_comm.
rewrite (btExtend_fold_comm _ _ Vh).
by rewrite -map_cat -filter_cat H filter_cat map_cat -cat1s filter_cat map_cat //= eq_refl.
by apply btExtendH.
Qed.

Lemma foldl_btExtend_last bt ps b :
  valid (foldl btExtend bt (rcons ps b)) ->
  validH bt ->
  foldl btExtend bt (rcons ps b) = foldl btExtend (btExtend bt b) ps.
Proof.
move=>V Vh; rewrite -cats1 foldl_cat.
have V0: valid bt.
  by move: V; move/btExtendV_fold1; move/btExtendV_fold_xs.
elim: ps b bt V Vh V0=>//=x xs Hi b bt V Vh V0; rewrite btExtend_comm//.
rewrite Hi //=.
apply btExtendH=>//=;
move: V; rewrite -cats1 foldl_cat btExtendV_fold_comm.
by move: V; move/btExtendV_fold_xs.
move: V; rewrite -cats1 foldl_cat btExtendV_fold_comm.
by move/btExtendV_fold_xs=>//=; rewrite btExtendV_comm.
by apply btExtendH=>//=.
Qed.

Lemma broadcast_reduce id peers X n :
  n \in peers -> uniq peers ->
  [seq msg_block (msg p) | p <- emitBroadcast id peers X & dst p == n] =
    [:: msg_block X].
Proof.
rewrite /emitBroadcast/=; elim: peers=>//p ps Hi/=.
rewrite inE; case/orP.
- move/eqP=>->/andP[H1 H2]; rewrite eqxx/=.
  suff G: [seq msg_block (msg p0) | p0 <- [seq {| src := id; dst := to; msg := X |}
                                  | to <- ps] & dst p0 == p] = [::] by rewrite G.
  apply/nilP; rewrite /nilp; clear Hi; elim: ps H1 H2=>//x xs Hi G1 G2/=.
  rewrite inE in G1; case/norP: G1; move/negbTE; rewrite eq_sym=>->G1.
  by apply: Hi=>//; case/andP: G2.
- move=>G1/andP[G2 G3].
have N : (p == n) = false by apply/negP=>/eqP Z; subst p; rewrite G1 in G2.
by rewrite N; apply: Hi.
Qed.

Lemma find_upd_same {T : ordType} W k v (m : union_map T W):
  find k m = Some v -> upd k v m = m.
Proof.
move=>F; move/find_some: (F).
case: dom_find=>//v'; rewrite F; case=>Z; subst v'=>->_.
by rewrite updF eqxx updU eqxx.
Qed.

Lemma upd_nothing (n : Address) (st : State) (w : World) :
  find n (localState w) = Some st -> upd n st (localState w) = (localState w).
Proof. by apply find_upd_same. Qed.

(*********************************************************)
(*                 Invariant Tactics                     *)
(*********************************************************)

Ltac NBlockMsg_dest_bt q st p b Msg H :=
  (have: (forall b, msg p != BlockMsg b) by move=>b; rewrite Msg)=>H;
  move: (procMsg_non_block_nc_blockTree st (src p) (ts q) H).

Ltac NBlockMsg_dest_btChain q st p b Msg P H :=
  (have: (forall b, msg p != BlockMsg b) by move=>b; rewrite Msg)=>H;
  move: (procMsg_non_block_nc_btChain st (src p) (ts q) H);
  rewrite/has_chain Msg P /==><-.

Ltac BlockMsg_dest_btChain q st from b iF P Msg :=
  rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _;
  rewrite/has_chain (procMsg_block_btExtend_btChain st from b (ts q));
  move: (b_in_blocksFor iF Msg)=>iB.

Ltac BlockMsg_dest_bt P Msg :=
  rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=>P _;
  rewrite/has_bt -P Msg procMsg_block_btExtend_bt.

Ltac simplw w :=
have: ((let (_, inFlightMsgs, _) := w in inFlightMsgs) = inFlightMsgs w) by [];
have: ((let (localState, _, _) := w in localState) = localState w) by [].

Ltac procInt_clique_maintain proc n st w F Fn Cw Al PInt PInt' P' HCliq H1 H2 c1 z :=
  move=>n st; rewrite findU c1 /=; case: ifP;
  [ move/eqP=>Eq [stEq]; subst n st; move=>z /=;
    move: (HCliq proc _ F)=>/= H1 |
    move=>Neq Fn z /=; move: (HCliq n _ Fn)=>/= H1
  ];
  by move: (step_nodes (Intern Cw Al F P'))=>H2;
     rewrite PInt in P'; rewrite P' in H2; clear P'; specialize (H1 z);
     move: (H2 z); clear H2; rewrite/localState; simplw w=>-> _;
     case: PInt'=><- _ H2; rewrite H2 in H1.

Ltac no_change can_bc can_bt can_n w F F' HExt c5 :=
  case=><- <- /=; exists can_bc, can_bt, can_n; rewrite (upd_nothing F); split=>//;
    by move=>n st'; rewrite/localState; simplw w=>-> _ F';
       rewrite/blocksFor/inFlightMsgs; simplw w=>_ ->;
       rewrite -cat1s filter_cat /=; case: ifP; rewrite map_cat /=;
       do? rewrite -(btExtend_withDup_noEffect (find_some (c5 _ _ F')));
       move: (HExt _ _ F').

Lemma foldl_expand cbt bt bs :
  valid (foldl btExtend bt bs) ->
  validH bt ->
  cbt = foldl btExtend bt bs -> exists q, cbt = bt \+ q.
Proof.
move=>V Vh; move: (btExtendV_fold_xs V)=>V0.
elim: bs cbt V=>//=[|b bs Hi]cbt V E; first by by exists Unit; rewrite unitR.
have V': valid (foldl btExtend (btExtend bt b) bs) by [].
rewrite -foldl_btExtend_last//= in E V. rewrite -cats1 foldl_cat/= in E V.
have Vx: valid (foldl btExtend bt bs) by move/btExtendV: V.
case: (Hi (foldl btExtend bt bs) Vx (erefl _))=>q E'.
rewrite E' in E; subst cbt; rewrite /btExtend.
case:ifP=>X.
- case: ifP; first by exists q.
  by exists um_undef; rewrite join_undefR.
by exists (# b \\-> b \+ q); rewrite joinCA.
by rewrite -cats1 foldl_cat btExtendV_fold_comm.
Qed.

(********************************************************************)
(************* Invariant inductivity proof **************************)
(********************************************************************)

(** This would be _significantly_ shorter with good proof automation. **)
Lemma clique_inv_step w w' q :
  clique_inv w -> system_step w w' q -> clique_inv w'.
Proof.
move=>Iw S; rewrite/clique_inv; split; first by apply (Coh_step S).
case: S; first by elim; move=>_ <-; apply Iw.
(* Deliver *)
move=> p st Cw. assert (Cw' := Cw). case Cw'=>[c1 c2 c3 c4 c5] Al iF F.
case: Iw=>_ GSyncW.
case: GSyncW=>can_bc [can_bt] [can_n] []
             HHold C HGood HCliq HExt.
  move=>P; assert (P' := P).
  move: P; case P: (procMsg _ _ _ _)=>[stPm ms]; move=>->.
  exists can_bc, can_bt, can_n; case: C=>C; last first.
  (** Case 1: the global block forest is invalid. **)
  split=>//=.

   (* bt is still invalid *)
  + by right.
  + by right.

  (* clique topology is maintained *)
  (* literally copy/paste; TODO: remove duplication *)
  + move=>n' st'; rewrite findU c1 /=;
    move: (HCliq (dst p) _ F)=>H1;
    move: (step_nodes (Deliver Cw Al iF F P'))=>H2;
    simplw w=>H3 _;
    rewrite P in P'; rewrite P' /localState H3 in H2; clear P' H3.
    case: ifP.
    * move/eqP=>Eq [Eq']; subst n' stPm;
      move=>z; specialize (H1 z); specialize (H2 z).
      rewrite H2 in H1; move=>H3. specialize (H1 H3).
      case Msg: (msg p)=>[prs|||||]; rewrite Msg in P;
      rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _;
      destruct st; rewrite/procMsg/=; do? by [];
      do? rewrite /peers in H1.
      case filter => //= s l.
      by rewrite mem_undup mem_cat; apply/orP; left.
      by case: ifP=>_;
         [rewrite mem_undup|rewrite -cat1s mem_cat mem_undup; apply/orP; right].
    * case: ifP=>//_; first by case: ifP; move/eqP => //= H_eq; case ohead.
      move/eqP => H_neq.
      move => F'; clear H1; move: (HCliq n' _ F')=>H1.
      move=>z; specialize (H1 z); specialize (H2 z).
      by rewrite H2 in H1=>H3; specialize (H1 H3).

  (* applying is conserved *)
  + move=>n' st'; rewrite findU c1 /=; case: ifP; last first.
    * move=>NDst F'; move: (HExt _ st' F').
      rewrite/blocksFor{2}/inFlightMsgs.
      rewrite filter_cat map_cat foldl_cat.
      have X: [seq msg_block (msg p0) |
               p0 <- seq.rem p (inFlightMsgs w) & dst p0 == n']
              = [seq msg_block (msg p0) | p0 <- inFlightMsgs w & dst p0 == n'].
      - elim : (inFlightMsgs w)=>//x xs Hi/=.
        case:ifP=>[/eqP Z|_/=]; first by subst x; rewrite eq_sym NDst.
        by case: ifP=>///eqP Z; subst n'; rewrite/= Hi.
      by rewrite X=><-; move/invalidE: C=>->; rewrite btExtend_fold_undef.

    * move/eqP=>Eq [Eq']; subst n' stPm.
      rewrite/blocksFor/inFlightMsgs; simplw w=>_ ->; rewrite/procMsg.
      move: (P); rewrite [procMsg _ _ _ _] surjective_pairing; case=>Z1 Z2.
      rewrite filter_cat map_cat foldl_cat.
      case V0: (valid (blockTree st)); last first.
      (* Invalid block forests stay invalid *)
      - move: V0; rewrite -Bool.negb_true_iff=>V0.
        case Msg: (msg p)=>[||b|||];
        do? by[
          (have Nb: (forall b : block, (msg p) != BlockMsg b) by move=>b; rewrite Msg);
          rewrite -Z1 -(procMsg_non_block_nc_blockTree st (src p) (ts q)) ?Nb //=;
          move/invalidE: C=>->; move/invalidE: V0=>->; rewrite -foldl_cat;
          rewrite btExtend_fold_undef
        ].
        by BlockMsg_dest_bt P Msg;
           move/invalidE: C=>->; move/invalidE: V0=>->; rewrite -foldl_cat;
           rewrite btExtend_undef btExtend_fold_undef.

      - case Msg: (msg p)=>[||b|||];
        do?[
          (have Nb: (forall b : block, (msg p) != BlockMsg b) by move=>b; rewrite Msg);
          rewrite -Z1 -(procMsg_non_block_nc_blockTree st (src p) (ts q)) ?Nb //=;
          rewrite rem_non_block' ?Nb//=; do? by [move: (c3 _ _ F V0)|move: (c4 _ _ F V0)];
          by move: (HExt _ _ F); rewrite/blocksFor=><-; move/invalidE: C=>->;
             rewrite btExtend_fold_undef
        ].
        BlockMsg_dest_bt P Msg.
        rewrite rem_block ?V0 ?iF //=; last by move: (c3 _ _ F V0).
        by move: (HExt _ _ F); rewrite/blocksFor=><-; move/invalidE: C=>->;
           rewrite btExtend_fold_undef.

  (** Case 2: the global block forest is valid. **)
  case: C=>Vc HGt; split=>//.
  left; case: HHold; last by move: Vc; rewrite/valid_with_bc=>[][][]=>->.
  move=>HHold.
  (* can_n still retains can_bc *)
  + move=>st'; rewrite findU c1 /=;
    case: ifP; last by move=>_ F'; apply (HHold _ F').
    move/eqP=>Eq [Eq']; subst can_n stPm.
    case Msg: (msg p)=>[||b|||]; do? by
    [NBlockMsg_dest_bt q st p b Msg H; move/eqP: (HHold _ F);
      rewrite/has_chain P //==><-->].
    rewrite/has_chain; BlockMsg_dest_bt P Msg.
    move: (HHold _ F); rewrite/has_bt=>/eqP Eq.
    move: Vc; rewrite/valid_with_bc=>[[][]]Vc Vh Ib Cbc.
    move: (b_in_blocksFor iF Msg)=>iB.
    have V0: (valid (blockTree st)) by move: (HExt _ _ F) Vc=>->; move/btExtendV_fold_xs.
    rewrite -(btExtend_seq_same _ (c3 _ _ F V0) (c4 _ _ F V0) iB).
    by rewrite Eq.
    by move: (HExt _ _ F)=><-.
    by rewrite Eq Cbc; move: (HExt _ _ F)=>->.

  (* can_bc is still the largest chain *)
  left; split=>//=.
  + move=>n' bc'; rewrite/holds findU c1 /=; case: ifP.
    move/eqP=>Eq st' [Eq']; subst n' stPm.
    case Msg: (msg p)=>[||b|||]; rewrite Msg in P;
    do? by
    [NBlockMsg_dest_btChain q st p b Msg P H=>Hc; move: (HGt (dst p) bc' _ F Hc)].
    BlockMsg_dest_btChain q st (src p) b iF P Msg;
       move: (c3 (dst p) _ F) (c4 (dst p) _ F) (c5 (dst p) _ F)=>Vh Ib _;
       move/eqP=>Eq; subst bc';
       (have: (has_chain (btChain (blockTree st)) st)
          by rewrite/has_chain eqxx)=>O;
       move: (HGt (dst p) (btChain (blockTree st)) _ F O)=>Gt;
       move: (HExt (dst p) _ F)=>Ext;
       (have: (btChain can_bt =
               btChain (foldl btExtend (blockTree st) (blocksFor (dst p) w)))
        by rewrite Ext).
    move: Vc; rewrite/valid_with_bc=>[[][]]Vc' Vh' Ib' Cbc.
    have V0: valid (blockTree st) by move: Vc'; rewrite Ext; move/btExtendV_fold_xs.
    specialize (Vh V0); specialize (Ib V0).
    rewrite -Cbc; move=>Ext'; rewrite Ext in Vc'.
    by move: (btExtend_seq_sameOrBetter_fref' Vc' Vh Ib iB Gt Ext').
    by move=>_ st' F'; move: (HGt n' bc' st' F').

  (* clique topology is maintained *)
  + move=>n' st'; rewrite findU c1 /=;
    move: (HCliq (dst p) _ F)=>H1;
    move: (step_nodes (Deliver Cw Al iF F P'))=>H2;
    simplw w=>H3 _;
    rewrite P in P'; rewrite P' /localState H3 in H2; clear P' H3.
    case: ifP.
    * move/eqP=>Eq [Eq']; subst n' stPm;
      move=>z; specialize (H1 z); specialize (H2 z).
      rewrite H2 in H1; move=>H3. specialize (H1 H3).
      case Msg: (msg p)=>[prs|||||]; rewrite Msg in P;
      rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _;
      destruct st; rewrite/procMsg/=; do? by [];
      do? rewrite /peers in H1.
      case filter => //= s l.
      by rewrite mem_undup mem_cat; apply/orP; left.
      by case: ifP=>_;
         [rewrite mem_undup|rewrite -cat1s mem_cat mem_undup; apply/orP; right].
    * case: ifP=>//_; first by case: ifP; move/eqP => //= H_eq; case ohead.
      move/eqP => H_neq.
      move => F'; clear H1; move: (HCliq n' _ F')=>H1.
      move=>z; specialize (H1 z); specialize (H2 z).
      by rewrite H2 in H1=>H3; specialize (H1 H3).

  (* applying conserved *)
  + move=>n' st'; rewrite findU c1 /=; case: ifP; last first.
    * move=>NDst F'; move: (HExt _ st' F').
      rewrite/blocksFor{2}/inFlightMsgs.
      rewrite filter_cat map_cat foldl_cat.
      have X: [seq msg_block (msg p0) |
               p0 <- seq.rem p (inFlightMsgs w) & dst p0 == n']
              = [seq msg_block (msg p0) | p0 <- inFlightMsgs w & dst p0 == n'].
      - elim : (inFlightMsgs w)=>//x xs Hi/=.
        case:ifP=>[/eqP Z|_/=]; first by subst x; rewrite eq_sym NDst.
        by case: ifP=>///eqP Z; subst n'; rewrite/= Hi.

      case Msg: (msg p)=>[|||||hash];
      set old_msgs := [seq msg_block (msg p) | p <- inFlightMsgs w & dst p == n'];
      set bt := (foldl btExtend (blockTree st') old_msgs);
      move: (c3 _ _ F')=>h3; move: (c4 _ _ F')=>h4;
      move: Vc; rewrite/valid_with_bc=>[[][]]Vc' Vh' Ib' Cbc;
      (have V0: valid (blockTree st')
        by move: Vc'; move: (HExt _ _ F')=>->; move/btExtendV_fold_xs);
      specialize (h3 V0); specialize (h4 V0);
      (have h2:  valid (foldl btExtend (blockTree st') (blocksFor n' w))
        by rewrite (HExt _ _ F') in Vc');
      move: (btExtendIB_fold h3 h2 h4)=>hIB; rewrite-/bt in hIB;
      clear h2 h3 h4;
      rewrite X-/bt; clear X=>E;
      do? by [
        (have: (msg_type (msg p) != MGetData) by rewrite Msg)=>notGD;
        move: (procMsg_nGetData_no_blocks n' P notGD)=>allG;
        move: (btExtend_foldG hIB allG)=>->].
      (* procMsg GetDataMsg => BlockMsg in ms *)
      rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=>_ <-.
      case: st F P'=>id0 peers0 blockTree0 txPool0 F P'.
      rewrite/procMsg Msg /=; case: ifP=>/=; first by move: (find_some hIB)=>hG.
      move/eqP => H_neq.
      case: ifP=>//=; move=>/eqP En'.
      - rewrite/get_block. (* blockTree wrt. the state of (dst p) in w *)
        case X: (find hash blockTree0)=>[b|].
        -- case: ifP => //=; move/eqP => H_n'.
           rewrite -E; suff BIn: (b ∈ can_bt).
             by apply (btExtend_withDup_noEffect BIn).
           move: (HExt _ _ F)=>/= ->; apply btExtend_fold_preserve.
           by move: (HExt _ _ F)=><-.
           rewrite/btHasBlock; move: (find_some X)=>Dom.
           have V0': valid blockTree0.
            by move: Vc'; move: (HExt _ _ F)=>//=->; move/btExtendV_fold_xs.
           by move: (c3 _ _ F V0' _ _ X)=>Eq; subst hash; rewrite Dom X eq_refl.
        -- move: hIB; rewrite/has_init_block=>ibF.
           move: (find_some ibF)=>ibD.
           case: ifP => //=. move/eqP => H_n'.
           have hG: (GenesisBlock ∈ bt) by rewrite/btHasBlock ibF ibD eq_refl.
           by move: (btExtend_withDup_noEffect hG)=><-.
      - case ohead => [tx|] //=; by
         case: ifP => //=; move/eqP => H_eq;
         rewrite -E;
         (suff BIn: (GenesisBlock ∈ can_bt) by apply (btExtend_withDup_noEffect BIn));
         move: Ib'; rewrite/has_init_block=>ibF; move: (find_some ibF)=>ibD;
         rewrite/btHasBlock ibF ibD eq_refl.
    * move/eqP=>Eq [Eq']; subst n' stPm.
      rewrite/blocksFor/inFlightMsgs; simplw w=>_ ->; rewrite/procMsg.
      move: (P); rewrite [procMsg _ _ _ _] surjective_pairing; case=>Z1 Z2.
      move: Vc; rewrite/valid_with_bc=>[[][]]Vc' Vh' Ib' Cbc.
      rewrite filter_cat map_cat foldl_cat btExtend_fold_comm//.
      case Msg: (msg p)=>[||b|||h];
      do?[
        (have: (msg_type (msg p) != MGetData) by rewrite Msg)=>notGD;
        (have V: valid (blockTree st)
          by move: Vc'; move: (HExt _ _ F)=>->; move/btExtendV_fold_xs);
        move: (c3 _ _ F V) (c4 _ _ F V)=>Vh Ib;
        move: (procMsg_nGetData_no_blocks (dst p) P notGD)=>//allG;
        rewrite (btExtend_foldG _ allG)//= ;
        NBlockMsg_dest_bt q st p b Msg H;
        rewrite Z1=>Eq; last (by rewrite -Eq);
      (have V':  valid (foldl btExtend (blockTree st')
                [seq msg_block (msg p0) | p0 <- inFlightMsgs w & dst p0 == dst p]) by
        move: (HExt _ _ F); rewrite/blocksFor Eq=><-);
      rewrite Eq in Vh Ib;
      rewrite (rem_non_block V' Vh Ib H) -Eq;
      by move: (HExt _ _ F); rewrite/blocksFor].

      (* BlockMsg *)
      have Nmd: msg_type (msg p) != MGetData by case: (msg p) (Msg).
      (* rewrite (btExtend_foldG G' (procMsg_nGetData_no_blocks (dst p) P Nmd)). *)
      rewrite -Z1; case: (msg p) (Msg)=>//_[->]; rewrite /procMsg/=.
      destruct st=>//=; move: (HExt _ _ F)=>/=->.
      rewrite /blocksFor.
      case: (in_seq_neq iF)=>ps[qs][Eq]Np; rewrite Eq (rem_elem _ Np).
      (* Now we need to move p on the LHS to the beginning. *)
      rewrite -cat_rcons !filter_cat !map_cat !foldl_cat; congr foldl.
      rewrite filter_rcons eqxx/= map_rcons Msg/=.
      have Vc: valid can_bt by [].
      move: Vc; move: (HExt _ _ F)=>->//=; move/btExtendV_fold_xs=>V.
      move: (c3 _ _ F V) (c4 _ _ F V)=>//=Vh Ib.
      rewrite (foldl_btExtend_last _ _)?(c3 _ _ F)//.
      move: (@procMsg_nGetData_no_blocks _ p _ _ _ (dst p) P Nmd)=>Ag //=.
      rewrite (btExtend_foldG _ Ag)//.
      apply btExtendIB=>//=.
      have X: (msg_block (msg p) \in [seq msg_block (msg p0) |
                                p0 <- inFlightMsgs w & dst p0 == dst p]).
      move: iF Msg; elim: (inFlightMsgs w)=>//=[m msgs H].
      rewrite in_cons=>/orP; case.
      by move/eqP=>Ex; subst p; rewrite eq_refl -cat1s map_cat //=;
         rewrite in_cons eq_refl Bool.orb_true_l.
      by move=>A B; move: (H A B); case: ifP=>//=; rewrite -cat1s mem_cat=>_ ->;
        rewrite Bool.orb_true_r.
      have V': valid (foldl btExtend blockTree0
                [seq msg_block (msg p0) | p0 <- inFlightMsgs w & dst p0 == dst p])
      by move: (HExt _ _ F)=>//=<-.
      by move: (btExtendV_within Vh V' X); rewrite /msg_block Msg.
      by move: (HExt _ _ F) Vc'=>//=->; rewrite/blocksFor Eq;
         rewrite -cat1s !filter_cat !map_cat //= eq_refl //= Msg -cat1s catA;
         move/btExtendV_fold=>//=; rewrite foldl_cat //= -cats1 foldl_cat.

      (* GetDataMsg *)
      destruct st; rewrite -Z2 /procMsg Msg /=; case: ifP=>/=X;
      (have V0: valid blockTree0
        by move: Vc'; move: (HExt _ _ F)=>->//=; move/btExtendV_fold_xs).

      * move: (HExt _ _ F); rewrite/blocksFor=>-> /=;
        rewrite -Z1 /procMsg Msg X /= rem_non_block=>//=.
        by move: (HExt _ _ F); rewrite/blocksFor=><-.
        by move: (c3 _ _ F V0).
        by move: (c4 _ _ F V0).
        by move=>b; rewrite Msg.

      * case: ifP => H_neq //=.
        - case:ifP=> //= Y; first by move/eqP:Y=>Y; rewrite Y eq_sym (c2 _ _ F) in X.
          move: (HExt _ _ F); rewrite/blocksFor=>-> /=;
          rewrite -Z1 /procMsg Msg X /= H_neq;
          case: ohead=>[b|]//=;
          do? case: ohead=>[t|]//=;
          do? rewrite rem_non_block //=;
            do? by [move: (HExt _ _ F); rewrite/blocksFor=><-];
            do? by [move: (c3 _ _ F V0)];
            do? by [move: (c4 _ _ F V0)];
            do? by [move=>b'; rewrite Msg].
        - move/eqP: H_neq => H_neq //=;
          move: (HExt _ _ F); rewrite/blocksFor=>-> /=;
          rewrite -Z1 /procMsg Msg X /= H_neq eq_refl //=;
          (have G: (GenesisBlock ∈ blockTree0)
            by move: (c4 _ _ F V0)=>//= Hv; rewrite/has_init_block/btHasBlock;
              rewrite Hv (find_some Hv) eq_refl
          );
          case: ohead=>[tx|] //=;
          do? [case: ifP=>//=];
          do? rewrite rem_non_block //=;
            do? rewrite -(btExtend_withDup_noEffect G) //=;
            do? by [move: (HExt _ _ F); rewrite/blocksFor=><-];
            do? by [move: (c3 _ _ F V0)];
            do? by [move: (c4 _ _ F V0)];
            do? by [move=>b'; rewrite Msg].

    (* Remaining proof obligation from earlier *)
    have V0: valid (blockTree st)
      by move: Vc'; move: (HExt _ _ F)=>->//=; move/btExtendV_fold_xs.
    by rewrite -Z1; apply procMsg_validH=>//=; move: (c3 _ _ F V0).

(* Internal *)
move=>proc t st [c1 c2 c3 c4 c5] Al F.
move=>P; assert (P' := P); move: P.
case P: (procInt _ _ _)=>[stPt ms]; move=>->; case: Iw=>Cw GSyncW.
case: GSyncW=>can_bc [can_bt] [can_n] []
             HHold C HGood HCliq HExt.
case: t P P'=>[tx|] P P'.
(* Tx - invariant holds trivially *)
- exists can_bc, can_bt, can_n; destruct st; rewrite/procInt in P;
  case: P=><- <- /=; rewrite (upd_nothing F); split=>//.
  (* HExt *)
   move=>n st'; rewrite/localState; simplw w=>-> _ F';
     rewrite/blocksFor/inFlightMsgs; simplw w=>_ ->;
     rewrite filter_cat map_cat; move: (HCliq _ _ F)=>/=Cliq;
     rewrite (broadcast_reduce _ _ (Cliq n (find_some F')) (c5 _ _ F)) /=.
   case V': (valid (blockTree st')).
   by (have Ib: GenesisBlock ∈ (blockTree st')
      by move: (c4 _ _ F' V'); rewrite/has_init_block/btHasBlock=>X;
         rewrite X eq_refl; move: (find_some X)=>->
    );
    rewrite -(btExtend_withDup_noEffect Ib); move: (HExt _ _ F').
   case: C.
   by move=>[]; rewrite/valid_with_bc=>[][][];
      move: (HExt _ _ F'); move/negbT: V'; move/invalidE=>->->;
      move/btExtendV_fold_xs; rewrite valid_undef.
   by move/invalidE=>->; move/negbT: V'; move/invalidE=>->;
      rewrite btExtend_undef btExtend_fold_undef.

(* MintT - can_bc and can_n might change *)
- assert (PInt := P); move: P; destruct st; rewrite/procInt.
  case X: (genProof _)=>[[txs pf]|].
  case Z: (valid_chain_block _ _).
  (* This is the only interesting case - when a new block is minted *)
  set new_block :=
    {| prevBlockHash := # last GenesisBlock (btChain blockTree0);
       txs := txs;
       proof := pf
    |}.
  set new_txpool :=
    [seq t <- txPool0 | txValid t (btChain (btExtend blockTree0 new_block))].
  move=>P; assert (PInt' := P); move: P; case=><- <-.
  (* Either can_bc becomes greater, or it does not. *)
  case Gt: ((btChain (btExtend blockTree0 new_block)) > can_bc).

  (* Does this new block introduce a hash collision in can_bt? *)
  case V': (valid (btExtend can_bt new_block)).
  (** Case 1: no hash collision **)
  * exists (btChain (btExtend blockTree0 new_block)),
           (btExtend can_bt new_block), proc.

    case: C; last by move/btExtendV: V'=>->.
    move=>[][][]=>V Vh Ib Cbc HGt.
    have V0: (valid blockTree0) by move: (HExt _ _ F) V=>//=->; move/btExtendV_fold_xs.
    have Vh0: (validH blockTree0) by move: (c3 _ _ F V0).
    have V0': (valid (btExtend blockTree0 new_block)).
    move: (HExt _ _ F) V'=>//=;
    have Q: (btExtend can_bt new_block = foldl btExtend can_bt [:: new_block]) by [].
    rewrite Q=>->; rewrite btExtendV_fold_comm //=.
    by move/btExtendV_fold_xs.

    (* HGood *)
    have HGood': good_bt (btExtend can_bt new_block).
    - rewrite/good_bt in HGood *.
      move=>b; move/all_blocksP'=>InE.
      move: (@btExtendH _ new_block V Vh)=>/=Vh'; move: (InE Vh')=>InE'.
      case: (btExtend_in_either InE').
      move/all_blocksP'=>In; specialize (In Vh);
      specialize (HGood b In); move/andP in HGood.
      by move: (@btExtend_compute_chain _ new_block b V' Vh Ib (proj1 HGood))=>->;
         apply/andP; apply HGood.
      move/eqP=>Eq; subst b.
      set lst := last GenesisBlock (btChain blockTree0).
      (have:  prevBlockHash new_block = # lst by [])=>Hp.
      (have: btChain blockTree0 \in all_chains blockTree0 by move: (btChain_in_bt (c4 _ _ F V0)))=>InC.
      move: (btExtend_mint_good_valid V0' (c3 _ _ F V0) (c4 _ _ F V0)
                                      Z (btChain_good blockTree0) Hp)=>Gc.
      (* move: (@btExtend_mint_good_valid _ new_block (c3 _ _ F) (c4 _ _ F) *)
      (*         (c5 _ _ F) Z  (btChain_good blockTree) Hp)=>Gc. *)
      move: (HExt _ _ F)=>/= Eq; rewrite Eq.
      rewrite -(@foldl1 BlockTree Block btExtend (foldl _ _ _)) btExtend_fold_comm //=.
      have V1: (valid (foldl btExtend (btExtend blockTree0 new_block) (blocksFor proc w))).
      have Q: (btExtend blockTree0 new_block = foldl btExtend blockTree0 [:: new_block]) by [].
        by move: (HExt _ _ F); rewrite Q btExtendV_fold_comm //==><-.
      move: (@btExtendH _ new_block V0 Vh0)=>Vh0'.
      move: (btExtendIB Vh0 V0' (c4 _ _ F V0))=>Ib'.
      by move: (btExtend_compute_chain_fold V1 Vh0' Ib' (proj1 Gc))=>->; move/andP: Gc.

    split=>//.

    (* HHold *)
    left.
    rewrite/holds/localState findU c1 /=; case: ifP; last by move/eqP.
    move=>_ st [Eq]; subst st; rewrite/has_chain//=.

    left; split.
    (* valid with bc *)
    split.
    split=>//=; by [apply btExtendH | apply btExtendIB].
    case: HHold; last by rewrite V.
    move=>HBc; move: (HExt _ _ F)=>/=H; subst can_bt.
    rewrite -(foldl1 _ (foldl _ _ _)) btExtend_fold_comm ?(c3 _ _ F) //=.
    rewrite -foldl_btExtend_last ?(c3 _ _ F)// -cats1 foldl_cat//=.
    apply: btExtend_with_new=>//=.
    by move: (c4 _ _ F V0).
    by rewrite Cbc in Gt.

    (* HGt *)
    move: (HGt proc (btChain blockTree0) _ F); rewrite/has_chain eqxx.
    rewrite/largest_chain/holds/localState; simplw w=>-> _.
    move/(_ is_true_true)=>H0.
    move=>n bc st; rewrite findU c1 /=; case: ifP.
    by move/eqP=>Eq [stEq]; subst proc st;
        rewrite/has_chain/==>/eqP <-; left.
    move=>Neq Fn hbc; move: (HGt _ _ _ Fn hbc)=>H1.
    (have: (btChain (btExtend blockTree0 new_block) >= can_bc) by right)=>H2.
    by move: (Geq_trans H2 H1).

    (* HCliq *)
    procInt_clique_maintain proc n st w F Fn Cw Al PInt PInt' P' HCliq H1 H2 c1 z.

    (* HExt *)
    move=>n st; rewrite/localState; simplw w=>-> _.
    rewrite findU c1 /=; case: ifP;
    [move/eqP=>Eq [Eq']; assert (F' := F); rewrite -Eq in F' * | move=> _ F'];
    rewrite/blocksFor/inFlightMsgs; simplw w=>_ ->;
    rewrite filter_cat map_cat foldl_cat; do? [rewrite -Eq'];
    move: (HCliq proc _ F)=>/= Cliq;
    move: (HExt n _ F')=>/= Ext; rewrite/blocksFor in Ext; subst can_bc.
       by rewrite Ext -foldl1 (btExtend_fold_comm _ _ (c3 _ _ F' V0)) /=;
       rewrite (broadcast_reduce _ _ (Cliq n (find_some F')) (c5 _ _ F)) /=;
       rewrite -(btExtend_idemp V0').
    by
    (have v: (valid (blockTree st))
      by move: (HExt _ _ F') V=>/=->; move/btExtendV_fold_xs);
    rewrite Ext -foldl1 (btExtend_fold_comm _ _ (c3 _ _ F' v)) /=;
    rewrite (broadcast_reduce _ _ (Cliq n (find_some F')) (c5 _ _ F)) /=.

  (** Case 2: hash collision! **)
  (* We are entering the Twilight Zone... *)
  exists [:: GenesisBlock], um_undef, can_n; split.
  + by right; rewrite valid_undef.
  + by right; rewrite valid_undef.
  + by rewrite/good_bt=>b; rewrite/all_blocks dom_undef.
  + by procInt_clique_maintain proc n st w F Fn Cw Al PInt PInt' P' HCliq H1 H2 c1 z.
  (* When there's a hash collision, everything (eventually) breaks! *)
  have Break: (btExtend can_bt new_block = um_undef) by move/negbT: V'; move/invalidE.
  + move=>n st; rewrite/localState; simplw w=>-> _.
    rewrite findU c1 /=; case: ifP;
    [move/eqP=>Eq [Eq']; assert (F' := F); rewrite -Eq in F' * | move=> _ F'];
    rewrite/blocksFor/inFlightMsgs; simplw w=>_ ->;
    rewrite filter_cat map_cat foldl_cat; do? [rewrite -Eq'];
    move: (HCliq proc _ F)=>/= Cliq;
    move: (HExt n _ F')=>/= Ext; rewrite/blocksFor in Ext.
    - case V0: (valid blockTree0); last first.
      by move/negbT: V0; move/invalidE=>->; rewrite btExtend_undef !btExtend_fold_undef.
      case V: (valid (btExtend blockTree0 new_block)); last first.
      by move/negbT: V; move/invalidE=>->; rewrite !btExtend_fold_undef.
      by rewrite -Break Ext -foldl1 (btExtend_fold_comm _ _ (c3 _ _ F' V0)) /=;
         rewrite (broadcast_reduce _ _ (Cliq n (find_some F')) (c5 _ _ F)) /=;
         rewrite -(btExtend_idemp V).
    - case v: (valid (blockTree st)); last first.
      by move/negbT: v; move/invalidE=>->; rewrite !btExtend_fold_undef.
      by rewrite -Break Ext -foldl1 (btExtend_fold_comm _ _ (c3 _ _ F' v)) /=;
         rewrite (broadcast_reduce _ _ (Cliq n (find_some F')) (c5 _ _ F)) /=.

  (* The newly minted block doesn't extend the heaviest chain *)
  (* Does it introduce a hash collision, though? *)
  case V': (valid (btExtend can_bt new_block)); last first.
  (** Case 1: yes **)
  (* This is literally copy/paste from above. CODE SMELL! *)
  exists [:: GenesisBlock], um_undef, can_n; split.
  + by right; rewrite valid_undef.
  + by right; rewrite valid_undef.
  + by rewrite/good_bt=>b; rewrite/all_blocks dom_undef.
  + by procInt_clique_maintain proc n st w F Fn Cw Al PInt PInt' P' HCliq H1 H2 c1 z.
  (* When there's a hash collision, everything (eventually) breaks! *)
  have Break: (btExtend can_bt new_block = um_undef) by move/negbT: V'; move/invalidE.
  + move=>n st; rewrite/localState; simplw w=>-> _.
    rewrite findU c1 /=; case: ifP;
    [move/eqP=>Eq [Eq']; assert (F' := F); rewrite -Eq in F' * | move=> _ F'];
    rewrite/blocksFor/inFlightMsgs; simplw w=>_ ->;
    rewrite filter_cat map_cat foldl_cat; do? [rewrite -Eq'];
    move: (HCliq proc _ F)=>/= Cliq;
    move: (HExt n _ F')=>/= Ext; rewrite/blocksFor in Ext.
    - case V0: (valid blockTree0); last first.
      by move/negbT: V0; move/invalidE=>->; rewrite btExtend_undef !btExtend_fold_undef.
      case V: (valid (btExtend blockTree0 new_block)); last first.
      by move/negbT: V; move/invalidE=>->; rewrite !btExtend_fold_undef.
      by rewrite -Break Ext -foldl1 (btExtend_fold_comm _ _ (c3 _ _ F' V0)) /=;
         rewrite (broadcast_reduce _ _ (Cliq n (find_some F')) (c5 _ _ F)) /=;
         rewrite -(btExtend_idemp V).
    - case v: (valid (blockTree st)); last first.
      by move/negbT: v; move/invalidE=>->; rewrite !btExtend_fold_undef.
      by rewrite -Break Ext -foldl1 (btExtend_fold_comm _ _ (c3 _ _ F' v)) /=;
         rewrite (broadcast_reduce _ _ (Cliq n (find_some F')) (c5 _ _ F)) /=.

  (** Case 2: no hash collision **)
  case: HHold; last by move/invalidE=>E; move: E V'=>->; rewrite btExtend_undef valid_undef.
  move=>HHold.
  case: C; last by move/btExtendV: V'=>->.
  move=>[][][]=>V Vh Ib Cbc HGt.
  have V0: (valid blockTree0) by move: (HExt _ _ F) V=>//=->; move/btExtendV_fold_xs.
  have Vh0: (validH blockTree0) by move: (c3 _ _ F V0).
  have V0': (valid (btExtend blockTree0 new_block)).
  move: (HExt _ _ F) V'=>//=;
  have Q: (btExtend can_bt new_block = foldl btExtend can_bt [:: new_block]) by [].
  rewrite Q=>->; rewrite btExtendV_fold_comm //=.
  by move/btExtendV_fold_xs.

  * exists can_bc, (btExtend can_bt new_block), can_n.
    case Dst: (can_n == proc). (* Isn't true. *)
    contradict Gt; move/eqP in Dst; subst can_n.
    suff W: (btChain (btExtend blockTree0 new_block) > can_bc) by rewrite W.
    move: (HHold _ F); rewrite/has_chain/==>/eqP <-.
    apply: btExtend_mint=>//=.
    by move: (c4 _ _ F V0).

    (* HGood *)
    (* copy/paste again :-( *)
    have HGood': good_bt (btExtend can_bt new_block).
    - rewrite/good_bt in HGood *.
      move=>b; move/all_blocksP'=>InE.
      move: (@btExtendH _ new_block V Vh)=>/=Vh'; move: (InE Vh')=>InE'.
      case: (btExtend_in_either InE').
      move/all_blocksP'=>In; specialize (In Vh);
      specialize (HGood b In); move/andP in HGood.
      by move: (@btExtend_compute_chain _ new_block b V' Vh Ib (proj1 HGood))=>->;
         apply/andP; apply HGood.
      move/eqP=>Eq; subst b.
      set lst := last GenesisBlock (btChain blockTree0).
      (have:  prevBlockHash new_block = # lst by [])=>Hp.
      (have: btChain blockTree0 \in all_chains blockTree0 by move: (btChain_in_bt (c4 _ _ F V0)))=>InC.
      move: (btExtend_mint_good_valid V0' (c3 _ _ F V0) (c4 _ _ F V0)
                                      Z (btChain_good blockTree0) Hp)=>Gc.
      move: (HExt _ _ F)=>/= Eq; rewrite Eq.
      rewrite -(@foldl1 BlockTree Block btExtend (foldl _ _ _)) btExtend_fold_comm //=.
      have V1: (valid (foldl btExtend (btExtend blockTree0 new_block) (blocksFor proc w))).
      have Q: (btExtend blockTree0 new_block = foldl btExtend blockTree0 [:: new_block]) by [].
        by move: (HExt _ _ F); rewrite Q btExtendV_fold_comm //==><-.
      move: (@btExtendH _ new_block V0 Vh0)=>Vh0'.
      move: (btExtendIB Vh0 V0' (c4 _ _ F V0))=>Ib'.
      by move: (btExtend_compute_chain_fold V1 Vh0' Ib' (proj1 Gc))=>->; move/andP: Gc.

    split=>//.

    (* HHold *)
    left;
    move=>st; rewrite/localState; simplw w=>-> _;
    rewrite findU c1 /=; case: ifP; first by rewrite Dst.
    by move=>_ F'; move: (HHold _ F').

    left; split; last first.
    (* HGt *)
    move=>n bc st; rewrite/localState; simplw w=>-> _.
    rewrite findU c1 /=; case: ifP.
    by move/eqP=>Eq[Eq']; subst n st; rewrite/has_chain=>/eqP<-; apply FCR_dual.
    by move=>_ F'; move: (HGt n bc _ F').

    (* valid with bc *)
    split.
    split=>//=; by [apply btExtendH | apply btExtendIB].
    rewrite Cbc in Gt *.
    move: (HExt _ _ F)=>/= H; move/FCR_dual:Gt=>Gt.
    case: (btExtend_sameOrBetter V')=>//Gt1.
    have P : prevBlockHash new_block = # last GenesisBlock (btChain blockTree0) by [].
    by move: (btExtend_within V' Vh Ib V0' Vh0 (c4 _ _ F V0) HGood HGood' Z Gt P H Gt1).

    (* HCliq *)
    procInt_clique_maintain proc n st w F Fn Cw Al PInt PInt' P' HCliq H1 H2 c1 z.

    (* HExt *)
    move=>n st; rewrite/localState; simplw w=>-> _.
    rewrite findU c1 /=; case: ifP;
    [move/eqP=>Eq [Eq']; assert (F' := F); rewrite -Eq in F' * | move=> _ F'];
    rewrite/blocksFor/inFlightMsgs; simplw w=>_ ->;
    rewrite filter_cat map_cat foldl_cat; do? [rewrite -Eq'];
    move: (HCliq proc _ F)=>/= Cliq;
    move: (HExt n _ F')=>/= Ext; rewrite/blocksFor in Ext; subst can_bc.
       by rewrite Ext -foldl1 (btExtend_fold_comm _ _ (c3 _ _ F' V0)) /=;
       rewrite (broadcast_reduce _ _ (Cliq n (find_some F')) (c5 _ _ F)) /=;
       rewrite -(btExtend_idemp V0').
    by
    (have v: (valid (blockTree st))
      by move: (HExt _ _ F') V=>/=->; move/btExtendV_fold_xs);
    rewrite Ext -foldl1 (btExtend_fold_comm _ _ (c3 _ _ F' v)) /=;
    rewrite (broadcast_reduce _ _ (Cliq n (find_some F')) (c5 _ _ F)) /=.

  + no_change can_bc can_bt can_n w F F' HExt c5.
  + no_change can_bc can_bt can_n w F F' HExt c5.

Qed.
End CliqueConsensus.