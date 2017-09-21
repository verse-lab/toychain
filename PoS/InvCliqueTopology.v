From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap.
Require Import Blockchain Protocol Semantics States BlockchainProperties SeqFacts.
Require Import InvMisc.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************************************************************)
(* Global Invariant 2: Clique consensus. *)

(* Under assumption of a clique network topology (every node is
connected to every other node), ensures that any node's local
blockchain will become _exactly_ the "canonical" blokchain, once all
blocks towars it "in flight" are received and used to extend the local
block tree.  *)
(*******************************************************************)

Definition saturated_chain w bc :=
  (* For any tree that induces bc *)
  forall bt, bc = btChain bt ->
    (* For any node in the world *)
    forall (n : nid), holds n w
    (* For any block in its local BlockTree *)
    (fun st => forall b, b ∈ blockTree st ->
    (* This block is not going to affect the blockchain out of bt *)
    btChain (btExtend bt b) = bc).

Definition GSyncing_clique w :=
  exists (bc : Blockchain) (n : nid),
  [/\ holds n w (has_chain bc),

   (* The canonical chain is the largest in the network *)
   largest_chain w bc,

   (* Clique topology *)
   forall n', holds n' w (fun st => {subset (dom (localState w)) <= peers st}),

   (* Applying blocks in flight will induce either the canonical
      chain or a smaller one. *)
   forall n',
      holds n' w (fun st =>
        bc = btChain (foldl btExtend (blockTree st) (blocksFor n' w))) &

   (* Conservation of blocks in clique topology *)
   [/\ forall n1, holds n1 w (fun st => forall b, b ∈ (blockTree st) ->
        forall n2, holds n2 w (fun st' => b ∈ (blockTree st') \/ b \in blocksFor n2 w)) &

        forall p, p \in inFlightMsgs w -> forall b, msg p = BlockMsg b ->
          exists st', find (src p) (localState w) = Some st' /\
                 holds (src p) w (fun st => b ∈ (blockTree st))
   ]
  ].

Definition clique_inv (w : World) :=
  Coh w /\ [\/ GStable w | GSyncing_clique w].

Lemma clique_eventual_consensus w n :
  clique_inv w -> blocksFor n w == [::] ->
  holds n w (fun st => exists bc, (has_chain bc st) /\ largest_chain w bc).
Proof.
case=>C; case=>[H|[bc][can_n][H1 H2 H3 H4 H5]] Na st Fw.
- case: H=>cE[bc]H; exists bc; split=>//; first by move:(H _ _ Fw).
  move=>n' bc' st' Fw'/eqP Z.
  by move: (H n' _ Fw')=>/eqP; rewrite Z=>->; left.
exists bc; split=>//.
move/eqP:Na=>Na.
by rewrite (H4 n _ Fw); rewrite Na/= /has_chain eqxx.
Qed.

Ltac NBlockMsg_dest_bt q st p b Msg H :=
  (have: (forall b, msg p != BlockMsg b) by move=>b; rewrite Msg)=>H;
  move: (procMsg_non_block_nc_blockTree st (src p) (ts q) H).

Ltac NBlockMsg_dest_btChain q st p b Msg P H :=
  (have: (forall b, msg p != BlockMsg b) by move=>b; rewrite Msg)=>H;
  move: (procMsg_non_block_nc_btChain st (src p) (ts q) H);
  rewrite/has_chain Msg P /==><-.

Ltac BlockMsg_dest q st from b iF P Msg :=
  rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _;
  rewrite/has_chain (procMsg_block_btExtend_btChain st from b (ts q));
  move: (b_in_blocksFor iF Msg)=>iB.

Ltac simplw w :=
have: ((let (_, inFlightMsgs, _) := w in inFlightMsgs) = inFlightMsgs w) by [];
have: ((let (localState, _, _) := w in localState) = localState w) by [].

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
- by case: ifP=>//_; apply/allP=>m; rewrite inE=>/eqP->/=; rewrite eqxx.
- move=>pt; apply/allP=>m; rewrite !inE.
  move/mapP=>[z]; rewrite mem_filter/emitMany/emitBroadcast=>/andP[_].
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
  has_init_block bt -> all (pred1 GenesisBlock) bs -> (foldl btExtend bt bs) = bt.
Proof.
move=>hG; move/all_pred1P=>->; rewrite/nseq/ncons/iter/=.
elim: (size bs)=>//n Hi/=.
by rewrite/has_init_block in hG; move: (find_some hG)=>H;
   move: (btExtend_withDup_noEffect H)=><-.
Qed.

Lemma foldl1 {A B : Type} (f : A -> B -> A) (init : A) (val : B) :
  foldl f init [:: val] = f init val.
Proof. done. Qed.

Lemma rem_non_block w bt p :
  valid bt -> validH bt ->
  has_init_block bt -> (forall b : Block, msg p != BlockMsg b) ->         
  btChain (foldl btExtend bt [seq msg_block (msg p0) |
                 p0 <- seq.rem p (inFlightMsgs w) & dst p0 == dst p]) =
  btChain (foldl btExtend bt [seq msg_block (msg p0) |
                 p0 <- inFlightMsgs w & dst p0 == dst p]).
Proof.
move=>V Vh H Nb.
case B: (p \in (inFlightMsgs w)); last by move/negbT/rem_id: B=>->.
case: (in_seq_neq B)=>xs [ys][->]Ni{B}.
rewrite rem_elem// !filter_cat !map_cat !foldl_cat/= eqxx map_cons.
have X: msg_block (msg p) = GenesisBlock.
- by case: (msg p) Nb=>//b Nb; move: (Nb b); move/negbTE; rewrite eqxx.
rewrite X -cat1s foldl_cat; clear X.
have A : all (pred1 GenesisBlock) [:: GenesisBlock] by rewrite /=eqxx.
by rewrite (btExtend_foldG _ A)//; apply: btExtendIB_fold.
Qed.

(*********************************************************)

Lemma clique_inv_step w w' q :
  clique_inv w -> system_step w w' q -> clique_inv w'.
Proof.
move=>Iw S; rewrite/clique_inv; split; first by apply (Coh_step S).
case: S; first by elim; move=>_ <-; apply Iw.
(* Deliver *)
move=> p st Cw. assert (Cw' := Cw). case Cw'=>[c1 c2 c3 c4 c5] Al iF F;
case: Iw=>_ [GStabW|GSyncW].
- by case GStabW=>noPackets; contradict iF; rewrite noPackets.
- case: GSyncW=>can_bc [can_n] [] HHold HGt HCliq HExt [HCon1 HCon2].
  move=>P; assert (P' := P).
  move: P; case P: (procMsg _ _ _ _)=>[stPm ms]; move=>->; right.
  (* The canonical chain is guaranteed to remain the same for any Msg *)
  exists can_bc, can_n; split.

  (* can_n still retains can_bc *)
  + move=>st'; rewrite findU c1 /=; case: ifP.
    move/eqP=>Eq [Eq']; subst can_n stPm.
    case Msg: (msg p)=>[|||b|||]; rewrite Msg in P;
    do? by [NBlockMsg_dest_btChain q st p b Msg P H; move: (HHold _ F)].
    by BlockMsg_dest q st (src p) b iF P Msg; move: (c3 (dst p) _ F)=>V;
       move/eqP: (HHold _ F)=>Eq; subst can_bc;
       rewrite (btExtend_seq_same V iB); by [|move: (HExt (dst p) _ F)].
    by move=>_ F'; move: (HHold _ F').

  (* can_bc is still the largest chain *)
  + move=>n' bc'; rewrite/holds findU c1 /=; case: ifP.
    move/eqP=>Eq st' [Eq']; subst n' stPm.
    case Msg: (msg p)=>[|||b|||]; rewrite Msg in P;
    do? by
    [NBlockMsg_dest_btChain q st p b Msg P H=>Hc; move: (HGt (dst p) bc' _ F Hc)].
    by BlockMsg_dest q st (src p) b iF P Msg; move: (c3 (dst p) _ F)=>V;
       move/eqP=>Eq; subst bc';
       (have: (has_chain (btChain (blockTree st)) st)
          by rewrite/has_chain eqxx)=>O;
       move: (HGt (dst p) (btChain (blockTree st)) _ F O)=>Gt;
       move: (HExt (dst p) _ F)=>Ext;
       move: (btExtend_seq_sameOrBetter_fref' V iB Gt Ext).
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
      case Msg: (msg p)=>[|prs|||||]; rewrite Msg in P;
      rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _;
      destruct st; rewrite/procMsg/=; do? by [];
      do? rewrite /Protocol.peers in H1.
      by rewrite mem_undup mem_cat; apply/orP; left.
      by case: ifP=>_;
         [rewrite mem_undup|rewrite -cat1s mem_cat mem_undup; apply/orP; right].
    * case: ifP=>//_.
      by move=>_ F'; clear H1; move: (HCliq n' _ F')=>H1;
         move=>z; specialize (H1 z); specialize (H2 z);
         rewrite H2 in H1=>H3; specialize (H1 H3).

  (* applying conserved *)
  + move=>n' st'; rewrite findU c1 /=; case: ifP; last first.
    * move=>NDst F'; move: (HExt _ st' F').
      rewrite/blocksFor{2}/inFlightMsgs.
      rewrite filter_cat map_cat foldl_cat.
      have X: [seq msg_block (msg p0) | p0 <- seq.rem p (inFlightMsgs w) & dst p0 == n']
              = [seq msg_block (msg p0) | p0 <- inFlightMsgs w & dst p0 == n'].
      - elim : (inFlightMsgs w)=>//x xs Hi/=.
        case:ifP=>[/eqP Z|_/=]; first by subst x; rewrite eq_sym NDst.
        by case: ifP=>///eqP Z; subst n'; rewrite/= Hi.

      case Msg: (msg p)=>[||||||hash];
      set old_msgs := [seq msg_block (msg p) | p <- inFlightMsgs w & dst p == n'];
      set bt := (foldl btExtend (blockTree st') old_msgs);
      move: (c3 _ _ F')=>h3; move: (c4 _ _ F')=>h4; move: (c5 _ _ F')=>h5;
      move: (btExtendIB_fold old_msgs h3 h4 h5)=>hIB; rewrite-/bt in hIB;
      clear h3 h4 h5;
      rewrite X-/bt; clear X=>E;
      do? by [
        (have: (msg_type (msg p) != MGetData) by rewrite Msg)=>notGD;
        move: (procMsg_nGetData_no_blocks n' P notGD)=>allG;
        move: (btExtend_foldG hIB allG)=>->].
      (* procMsg GetDataMsg => BlockMsg in ms *)
      rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=>_ <-.
      case: st F P'=>id0 peers0 blockTree0 txPool0 F P';
      rewrite/procMsg Msg /=; case: ifP=>/=;
      first by case: ifP=>//=;
        by move: (find_some hIB)=>hG; move: (btExtend_withDup_noEffect hG)=><-.
      move=>Src; case: ifP=>//=; move=>/eqP En'; subst n'.
      rewrite/get_block. (* blockTree wrt. the state of (dst p) in w *)
      case X: (find hash blockTree0)=>[b|];
      last by move: (find_some hIB)=>hG;
              move: (btExtend_withDup_noEffect hG)=><-.
      set st := {| id := id0; peers := peers0;
                   blockTree := blockTree0; txPool := txPool0 |}.
      have: b ∈ Protocol.blockTree st.
      by rewrite/btHasBlock; move: (c4 _ _ F hash b X)=><-; move: (find_some X).

      move=>hB; move: (HCon1 (dst p) _ F b hB (src p) _ F');
      case=>[|iBF]; subst bt old_msgs.
      - rewrite -foldl1 btExtend_fold_comm /=.
        by rewrite/btHasBlock=>hB'; rewrite -(btExtend_withDup_noEffect hB').
        by move: (c3 _ _ F').
      - rewrite/blocksFor in iBF; move: (in_seq iBF)=>[fs] [ls]=>Eq.
        move: (c3 _ _ F')=>V.
        rewrite Eq -cat1s 2!foldl_cat btExtend_fold_comm /=.
        (have: valid (foldl btExtend (foldl btExtend (blockTree st') fs) ls)
        by rewrite -!btExtendV_fold)=>V'.
        rewrite -(btExtend_idemp b V'); clear V'.
        rewrite -foldl1 btExtend_fold_comm.
        by rewrite -foldl_cat cat1s -foldl_cat -Eq.
        by rewrite -btExtendV_fold.
        by rewrite -btExtendV_fold.

    * move/eqP=>Eq [Eq']; subst n' stPm.
      rewrite/blocksFor/inFlightMsgs; simplw w=>_ ->; rewrite/procMsg.
      move: (P); rewrite [procMsg _ _ _ _] surjective_pairing; case=>Z1 Z2.
      move: (procMsg_valid (src p) (msg p) (ts q) (c3 _ _ F))=>V'.
      move: (@procMsg_validH _ (src p) (msg p) (ts q) (c3 _ _ F) (c4 _ _ F))=>H'.
      move: (procMsg_has_init_block (src p) (msg p) (ts q) (c3 _ _ F) (c4 _ _ F) (c5 _ _ F))=>G'.
      rewrite ?Z1 ?Z2 in V' G'; rewrite filter_cat map_cat foldl_cat btExtend_fold_comm//.
      case Msg: (msg p)=>[|||b|||h];
      do? [(have: (msg_type (msg p) != MGetData) by rewrite Msg)=>notGD;
           move: (procMsg_nGetData_no_blocks (dst p) P notGD)=>//allG;
           rewrite (btExtend_foldG _ allG)//;
           NBlockMsg_dest_bt q st p b Msg H;
           rewrite Z1=>Eq; rewrite -Eq in V' G' *;
           rewrite (rem_non_block w V' (c4 _ _ F) (c5 _ _ F))//; apply: HExt=>//].      

      (* BlockMsg *)
      admit.
      (* move: (HExt _ _ F); rewrite/blocksFor=>->. *)
      (* destruct st; rewrite -Z1 /procMsg Msg /=. *)
      (* rewrite -(foldl1 btExtend) -foldl_cat. *)

      (* GetDataMsg *)
      destruct st; rewrite -Z2 /procMsg Msg /=; case: ifP=>/=X.
      * by case: ifP=>/=?;
        do? [rewrite/has_init_block /= in G';
             move: (btExtend_withDup_noEffect (find_some G'))=><-];
        move: (HExt _ _ F); rewrite/blocksFor=>-> /=;
        do [rewrite Z1 in H'; rewrite (rem_non_block w V')//; last by case: (msg p) Msg];
        by rewrite -Z1 Msg/=; case: ifP.
      rewrite Z1 in H'; case:ifP=>Y; first by move/eqP:Y=>Y; rewrite Y eq_sym (c2 _ _ F) in X.
      rewrite (rem_non_block w V')//; last by case: (msg p) Msg.
      by rewrite -Z1 Msg/=; case: ifP=>_/=; apply: (HExt _ _ F).
      

   (***************************************************)    
   (* conservation of blocks *)
   split.
   + rewrite!/holds!/localState=>n1 st1; rewrite findU c1 /=; case: ifP.
     * move/eqP=>Eq [Eq']; subst n1 stPm.
       move=>b iB1 n2 st2; rewrite findU c1 /=; case: ifP.
        - by move/eqP=>Eq [Eq']; subst n2 st2; left.
        - move=>X; simplw w=>-> _ F2.
          case Msg: (msg p)=>[|||mb|||]; rewrite Msg in P;
          rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=>P1 P2;
          (* non-block msg => blockTree st1 = blockTree st *)
          do? [
            NBlockMsg_dest_bt q st p b' Msg H; rewrite Msg P1=>Eq;
            rewrite -Eq in iB1; case: (HCon1 (dst p) _ F b iB1 n2 _ F2)=>[|biF]
          ]; do? [by left]; do? [
            right; rewrite/blocksFor/inFlightMsgs mem_undup; simplw w=>_ ->;
            rewrite/blocksFor mem_undup in biF; move:biF; move/mapP=>[p'] H1 H2;
            apply/mapP; exists p'; last done
          ]; do? [
            move: H1; rewrite mem_filter; move/andP=>[Dst] iF';
            rewrite mem_filter in_rem_msg;
            by [|rewrite Dst|
                rewrite eq_sym in Dst; move/eqP in Dst; rewrite Dst in X;
                move/eqP; move/eqP=>Eq'; subst p'; contradict X; rewrite eqxx
            ]
          ].
          (* BlockMsg mb => blocktree st1 = btExtend (blockTree st) mb *)
          move: (procMsg_block_btExtend_bt st mb (ts q)); rewrite P1=>Eq.
          (* Is b something n1 just received (i.e. mb) or something it had? *)
          rewrite Eq in iB1. move: (c3 (dst p) _ F)=>V.
