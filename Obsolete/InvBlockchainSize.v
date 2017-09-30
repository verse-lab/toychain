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
(* Global Invariant 1: Blockchain Cost Monotonicity. *)

(* Under assumption of a clique network topology (every node is
connected to every other node), ensures that any node's local
blockchain is no more expensive than the "canonical" blokchain, even
if all blocks "in flight" are received and used to extend the local
block tree.  *)
(*******************************************************************)

Definition GSyncing_size w :=
  exists (bc : Blockchain) (n : nid),
  [/\ holds n w (has_chain bc),

   (* The canonical chain is the largest in the network *)
   largest_chain w bc,

   (* Clique topology *)
   forall n', holds n' w (fun st => peers st =i dom (localState w)) &

   (* Applying blocks in flight will induce either the canonical
      chain or a smaller one. *)
   forall n',
      holds n' w (fun st =>
       bc >= btChain (foldl btExtend (blockTree st) (blocksFor n' w)))].

(*
(* If you've received all blocks, you have the canonical chain *)
   forall n',
     holds n' w (fun st =>
      (~exists b, available b n' w) /\ blocksFor n' w == [::] -> has_chain bc st)
*)

Definition BT_size_inv (w : World) :=
  Coh w /\ [\/ GStable w | GSyncing_size w].

Lemma BT_size_inv_init N : BT_size_inv (initWorld N).
Proof.
split; do? by apply Coh_init. left; split; do? by [].
exists (btChain (blockTree (Init 0)))=>/=.
rewrite /holds/has_chain; move=>n st; elim: N=>[|n' Hi].
  by move/find_some; rewrite dom0 inE.
  rewrite findUnL; last first.
  - case: validUn; rewrite ?um_validPt ?valid_initState//.
    move=>k; rewrite um_domPt !inE=>/eqP Z; subst k.
    by rewrite dom_initState mem_iota addnC addn1 ltnn andbC.
  - case: ifP=>//; rewrite um_domPt inE=>/eqP<-.
    by rewrite um_findPt; case=><-.
Qed.

Ltac NBlockMsg_dest q st1 p b Msg H :=
(have: (forall b, msg p != BlockMsg b) by move=>b; rewrite Msg)=>H;
      move=>Eq [] <-; move: (procMsg_non_block_nc_btChain st1 (ts q) H).

Ltac BlockMsg_dest w q can_n can_bc st1 p iF Fw P Msg b X HHold HInFlight :=
    move=>_ [] <-; rewrite [procMsg _ _ _] surjective_pairing in P; case: P;
    rewrite -X in Fw; move=><- _; move: (HHold st1 Fw); rewrite/has_chain eq_sym;
    specialize (HInFlight can_n); move/eqP=>?; subst can_n can_bc;
    rewrite (procMsg_block_btExtend st1 b (ts q));
    move/HInFlight : (Fw)=>[|]/=;
    move: (b_in_blocksFor iF Msg)=>X.

Lemma BT_size_inv_step w w' q :
  BT_size_inv w -> system_step w w' q -> BT_size_inv w'.
Proof.
move=>Iw S; rewrite/BT_size_inv; split; first by apply: (Coh_step S).
case: S=>[|p st1 [c1 c2 c3] _ iF Fw|proc t st1 [c1 c2 c3] _ Fw];
  first by elim=>_ <-; move: Iw=>[].
case: Iw=>_ [GStabW|GSyncW].
- by case GStabW=>noPackets; contradict iF; rewrite noPackets.
- case GSyncW=>can_bc [can_n] [] HHold HGt HInFlight HDiff.
  case P: (procMsg _ _ _)=>[stPm ms]; move=>->; right.
  (* The canonical chain is guaranteed to remain the same for any msg:
   *  - for non-block messages, this holds by procMsg_non_block_nc_btChain
   *  - for block messages, it holds by HInFlight *)
  exists can_bc; exists can_n; split.

  (* ... the original node still retains it *)
  + case Msg: (msg p)=>[|||b|||]; rewrite Msg in P;
    rewrite/holds/localState/has_chain=>st';
    case X: (can_n == dst p); move/eqP in X;
    (* All cases except BlockMsg *)
    do? [subst can_n; rewrite findU c1=>/=; case: ifP;
      by [move/eqP |
        NBlockMsg_dest q st1 p b Msg H; rewrite Msg P=><-; apply (HHold st1 Fw)
    ]];
    do? [rewrite findU c1=>/=; case: ifP=>/=;
      by [move/eqP | move=>_ Fc; move: (HHold st' Fc)]
    ].
    (* BlockMsg *)
    rewrite findU c1=>/=; case: ifP=>/=; last by move/eqP.
    BlockMsg_dest w q can_n can_bc st1 p iF Fw P Msg b X HHold HInFlight.
    move: (c3 (dst p) _ Fw)=>V.
    * by move=>H; move: (btExtend_seq_same V X H); move/eqP; rewrite eq_sym.
    * by move=>Con; contradict Con; apply btExtend_fold_not_worse.

 (* ... it's still the largest *)
  + case Msg: (msg p)=>[|||b|||]; rewrite Msg in P;
    (* All cases except BlockMsg *)
    rewrite/holds/localState/has_chain=>n' bc' st';
    case X: (can_n == dst p); move/eqP in X;
    rewrite findU c1=>/=; case: ifP=>/=; move/eqP;
    do? by [
      move=>_ Fc; move: (HGt n' bc' st' Fc) |
      NBlockMsg_dest q st1 p b Msg H; rewrite /has_chain Msg P=><-;
      rewrite -Eq in Fw=>Hc; move: (HGt n' bc' st1 Fw Hc)].
    (* BlockMsg *)
    BlockMsg_dest w q can_n can_bc st1 p iF Fw P Msg b X HHold HInFlight.
    move: (c3 (dst p) _ Fw)=>V.
    * by move=>H; move: (btExtend_seq_same V X H)=><-/eqP->; left.
    * by move=>Con; contradict Con; apply btExtend_fold_not_worse.

    (* TODO: Make this shorter! *)
    move=>Dst [] Eq; subst stPm; subst n'=>Hc.
    rewrite/has_chain in Hc; move/eqP in Hc; subst bc'.
    rewrite [procMsg _ _ _] surjective_pairing in P; case: P; move=><- _.
    rewrite (procMsg_block_btExtend st1 b (ts q)); clear X.
    move: (b_in_blocksFor iF Msg)=>X.
    specialize (HInFlight (dst p) _ Fw); simpl in HInFlight.
    specialize (HGt (dst p) (btChain (blockTree st1)) _ Fw).
    rewrite/has_chain eqxx in HGt.
    (have: (is_true true) by done)=>Obvs; specialize (HGt Obvs); clear Obvs.
    move: (c3 (dst p) _ Fw)=>V.
    by move: (btExtend_seq_sameOrBetter_fref V X HGt HInFlight).

  (* ... no surprise blocks in the packet soup *)
  (* Only two kinds of messages impact blocksFor X:
     1) BlockMsg b -> removed when it is delivered to X
     2) GetDataMsg X #b -> when delivered to Y, might send a new BlockMsg b to X

     For all other kinds of messages:
      forall n, blocksFor n w = blocksFor n w'

     For (1), applying a subset of blocksFor gives bc <= than applying all
     For (2), b is not magical (how do we know this?)
      - Y has it & Y's bc <= can_bc
      - need to use conjunct 4 to relate this to X's state
        i.e. b comes from a process that "conserves" overall information
        * b moves from available to blocksFor
        * ISSUE: C4 doesn't say that applying diffInFlight induces
            can_bc, just that the local bc becomes can_bc when diffInFlight = 0
   *)
   + case Msg: (msg p)=>[|||b|||]; rewrite Msg in P;
    (* All cases except BlockMsg *)
    rewrite/holds/localState/has_chain=>n' bc' st';
    case X: (can_n == dst p); move/eqP in X;
    rewrite findU c1=>/=; case: ifP=>/=; move/eqP;
    do? by [
      move=>_ Fc; move: (HGt n' bc' st' Fc) |
      NBlockMsg_dest q st1 p b Msg H; rewrite /has_chain Msg P=><-;
      rewrite -Eq in Fw=>Hc; move: (HGt n' bc' st1 Fw Hc)].
     


(* the canonical chain can only change throught a MintT transition *)
(* TODO: refactor it into a lemma *)
- admit.
Admitted
