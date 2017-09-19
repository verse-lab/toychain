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


Definition GSyncing_clique w :=
  exists (bc : Blockchain) (n : nid),
  [/\ holds n w (has_chain bc),

   (* The canonical chain is the largest in the network *)
   largest_chain w bc,

   (* Clique topology *)
   forall n', holds n' w (fun st => {subset (dom (localState w)) <= peers st}) &

   (* Applying blocks in flight will induce either the canonical
      chain or a smaller one. *)
   forall n',
      holds n' w (fun st =>
       bc = btChain (foldl btExtend (blockTree st) (blocksFor n' w)))].

Definition clique_inv (w : World) :=
  Coh w /\ [\/ GStable w | GSyncing_clique w].

Lemma clique_eventual_consensus w n :
  clique_inv w -> blocksFor n w == [::] ->
  holds n w (fun st => exists bc, (has_chain bc st) /\ largest_chain w bc).
Proof.
case=>C; case=>[H|[bc][can_n][H1 H2 H3 H5]] Na st Fw.
- case: H=>cE[bc]H; exists bc; split=>//; first by move:(H _ _ Fw).
  move=>n' bc' st' Fw'/eqP Z.
  by move: (H n' _ Fw')=>/eqP; rewrite Z=>->; left.
exists bc; split=>//.
move/eqP:Na=>Na.
by rewrite (H5 n _ Fw); rewrite Na/= /has_chain eqxx.
Qed.

Ltac NBlockMsg_dest_bt q st p b Msg H :=
  (have: (forall b, msg p != BlockMsg b) by move=>b; rewrite Msg)=>H;
  move: (procMsg_non_block_nc_blockTree st (ts q) H).

Ltac NBlockMsg_dest_btChain q st p b Msg P H :=
  (have: (forall b, msg p != BlockMsg b) by move=>b; rewrite Msg)=>H;
  move: (procMsg_non_block_nc_btChain st (ts q) H);
  rewrite/has_chain Msg P /==><-.

Ltac BlockMsg_dest q st b iF P Msg :=
  rewrite [procMsg _ _ _] surjective_pairing in P; case: P=><- _;
  rewrite/has_chain (procMsg_block_btExtend_btChain st b (ts q));
  move: (b_in_blocksFor iF Msg)=>iB.

Ltac simplw w :=
have: ((let (_, inFlightMsgs, _) := w in inFlightMsgs) = inFlightMsgs w) by [];
have: ((let (localState, _, _) := w in localState) = localState w) by [].

(* TODO: Now the inductive version. *)
Lemma clique_inv_step w w' q :
  clique_inv w -> system_step w w' q -> clique_inv w'.
Proof.
move=>Iw S; rewrite/clique_inv; split; first by apply (Coh_step S).
case: S; first by elim; move=>_ <-; apply Iw.
(* Deliver *)
move=> p st Cw. assert (Cw' := Cw). case Cw'=>[c1 c2 c3 c4 c5] Al iF F;
case: Iw=>_ [GStabW|GSyncW].
- by case GStabW=>noPackets; contradict iF; rewrite noPackets.
- case: GSyncW=>can_bc [can_n] [] HHold HGt HCliq (*[HCon1 HCon2]*) HExt.
  move=>P; assert (P' := P).
  move: P; case P: (procMsg _ _ _)=>[stPm ms]; move=>->; right.
  (* The canonical chain is guaranteed to remain the same for any Msg *)
  exists can_bc, can_n; split.

  (* can_n still retains can_bc *)
  + move=>st'; rewrite findU c1 /=; case: ifP.
    move/eqP=>Eq [Eq']; subst can_n stPm.
    case Msg: (msg p)=>[|||b|||]; rewrite Msg in P;
    do? by [NBlockMsg_dest_btChain q st p b Msg P H; move: (HHold _ F)].
    by BlockMsg_dest q st b iF P Msg; move: (c3 (dst p) _ F)=>V;
       move/eqP: (HHold _ F)=>Eq; subst can_bc;
       rewrite (btExtend_seq_same V iB); by [|move: (HExt (dst p) _ F)].
    by move=>_ F'; move: (HHold _ F').

  (* can_bc is still the largest chain *)
  + move=>n' bc'; rewrite/holds findU c1 /=; case: ifP.
    move/eqP=>Eq st' [Eq']; subst n' stPm.
    case Msg: (msg p)=>[|||b|||]; rewrite Msg in P;
    do? by
    [NBlockMsg_dest_btChain q st p b Msg P H=>Hc; move: (HGt (dst p) bc' _ F Hc)].
    by BlockMsg_dest q st b iF P Msg; move: (c3 (dst p) _ F)=>V;
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
      case Msg: (msg p)=>[|n prs|pr||||]; rewrite Msg in P;
      rewrite [procMsg _ _ _] surjective_pairing in P; case: P=><- _;
      destruct st; rewrite/procMsg/=; do? by [];
      do? rewrite /Protocol.peers in H1.
      by rewrite mem_undup mem_cat; apply/orP; left.
      by case: ifP=>_;
         [rewrite mem_undup|rewrite -cat1s mem_cat mem_undup; apply/orP; right].
    * by move=>_ F'; clear H1; move: (HCliq n' _ F')=>H1;
         move=>z; specialize (H1 z); specialize (H2 z);
         rewrite H2 in H1=>H3; specialize (H1 H3).

  (* applying conserved *)
  + move=>n' st'; rewrite findU c1 /=; case: ifP; last first.
    * move=>NDst F'; move: (HExt _ st' F')=>->.
      rewrite/blocksFor{2}/inFlightMsgs.
      admit.
    * move/eqP=>Eq [Eq']; subst n' stPm.
      case Msg: (msg p)=>[|||b|||]; rewrite Msg in P;
      rewrite [procMsg _ _ _] surjective_pairing in P; case: P=>_ <-;
      rewrite/blocksFor/inFlightMsgs; simplw w=>_ ->; rewrite/procMsg.
      destruct st=>/=; case: ifP.
      move=>_.
