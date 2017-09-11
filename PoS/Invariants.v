From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap.
Require Import Blockchain Protocol Semantics States BlockchainProperties SeqFacts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(***************************************************)
(*        Some useful facts about lists            *)
(***************************************************)

Lemma in_rem_msg p0 p ms w :
  p0 \in inFlightMsgs w -> p0 <> p ->
  p0 \in ms ++ seq.rem p (let (_, inFlightMsgs, _) := w in inFlightMsgs).
Proof.
move=>iF0 E; rewrite mem_cat orbC; apply/orP; left.
case: (w) iF0=>_ ifM _/= Hi.
suff N : (p0 != p) by rewrite (rem_neq N Hi).
by apply/negP=>/eqP Z; subst p0.
Qed.

Lemma ohead_hash b0 bt:
  b0 \in bt ->
  ohead [seq b <- bt | hashB b == hashB b0] = Some b0.
Proof.
elim: bt=>//=h bt Hi; rewrite inE; case/orP=>[/eqP Z|/Hi H]/=.
- by subst b0; rewrite eqxx.
by case: ifP=>C//=; move/eqP/hashB_inj: C=>->.
Qed.

(***************************************************)

(* Invariants of the execution regarding the blockchain *)
(* Properties *)

Definition has_chain (bc : Blockchain) (st : State) : Prop :=
  btChain (blockTree st) == bc.

Definition exists_and_holds (n : nid) (w : World) (cond : State -> Prop) :=
  exists (st : State),
    find n (localState w) = Some st /\ cond st.

Definition chain_sync_agreement (w w' : World) :=
  forall (n n' : nid) (bc bc' : Blockchain),
    holds n w (has_chain bc) ->
    reachable w w' ->
    holds n' w' (has_chain bc') ->
    size bc' == size bc ->
    bc == bc'.

Lemma has_chain_func n w (bc bc' : Blockchain):
  n \in dom (localState w) ->
  holds n w (has_chain bc) ->
  holds n w (has_chain bc') -> bc = bc'.
Proof.
case/um_eta=>st[Sf]_ nbc nbc'.
by move: (nbc st Sf) (nbc' st Sf)=>/eqP<-/eqP->.
Qed.

(* TODO: More complicated -- the "rollback" is no more than a contstant;
 *)

Lemma local_chain_grows_fork_step (w w' : World) q n bc bc':
  n \in dom (localState w) ->
  holds n w (has_chain bc) ->
  system_step w w' q ->
  holds n w' (has_chain bc') ->
  bc = bc' \/ (([bc <<< bc'] \/ fork bc bc') /\ bc' > bc).
Proof.
move=>D H1 S H2; move: (Coh_step S)=>C2.
case: S=>[[C]Z|p [n' prs bt pool] C _ _ F|
          proc t s1 C _ F].

(* 0 steps *)
- by subst w'; rewrite (has_chain_func D H1 H2); left.
(* Step is procedding a message *)

(* Receiving a message *)
- have E: (n' = (dst p)) by case:C=>_/(_ (dst p) _ F)/eqP. subst n'.

  (* Two sub-cases: (dst p) =? n *)
  case N : (n == dst p);[move/eqP:N=>N; subst n|]; last first.
  (* Message not to us: don't really care about the outcome of procMsg! *)
  + set pms := (procMsg _ _); case: pms=>st' ms Z; subst w'.
    rewrite /holds/= findU N/= in H2.
    by rewrite -(has_chain_func D H1 H2); left.
  rewrite [procMsg _ _ _]surjective_pairing=>Z;
  (* Avoiding premature unfolding. *)
  set Pm := nosimpl (procMsg _ _ _) in Z; subst w'.
  rewrite /holds/= findU eqxx/= (proj1 (C)) in H2.
  move/(H2 Pm.1): (erefl (Some Pm.1))=>{H2} H2.
  move: (H1 _ F)=>{H1 C2 F}/=H1.
  by apply: (@procMsg_bc_prefix_or_fork bc bc'
        {| id := dst p; peers := prs; blockTree := bt; txPool := pool |}
        (msg p) (ts q)); move/eqP: H2; move/eqP: H1.

(* Internal transition *)
(* Two sub-cases: proc =? n *)
case N : (n == proc);[move/eqP:N=>N; subst n|]; last first.
- set pms := (procInt _ _ _). case: pms=>st' ms Z. subst w'.
  rewrite /holds/= findU N/= in H2.
  by left; rewrite -(has_chain_func D H1 H2).

(* Another interesting part of the proof: n == proc.
   Consider all branches of procInt and proof the property for each one.
   Don't hesitate to introduce auxiliary lemmas. *)
rewrite [procInt _ _ _]surjective_pairing=>Z.
set Pi := nosimpl (procInt _ _ _) in Z; subst w'.
rewrite /holds/= findU eqxx/= (proj1 (C)) in H2. rewrite /holds F in H1.
have: (Some s1 = Some s1). by []. move=> eq. move: (H1 s1 eq)=>hbc. clear eq.
have: (Some Pi.1 = Some Pi.1). by []. move=> eq. move: (H2 Pi.1 eq)=>hbc'. clear eq.
rewrite /has_chain in hbc hbc'. move/eqP in hbc. move/eqP in hbc'.
specialize (procInt_bc_same_or_extension s1 t (ts q))=>/=.
case=>/=; rewrite -hbc -hbc'; first by left.
move=>Pf; right; split; first by left.
by move: Pf=>[] eh [] et ->; apply CFR_ext.
Qed.

(* Big-step case, proven by induction *)
Lemma local_chain_grows_fork (w w' : World) n bc bc':
  n \in dom (localState w) ->
  holds n w (has_chain bc) ->
  reachable w w' ->
  holds n w' (has_chain bc') ->
  bc = bc' \/ (([bc <<< bc'] \/ fork bc bc') /\ bc' > bc).
Proof.
move=>D H1 [m]R H2.
elim: m w' R bc' H2=>/=[w'<-|q m Hi w' [via][R S]] bc' H2.
- by left; move/(has_chain_func D H1 (bc':=bc')):H2=><-.
have D': n \in dom (localState via).
- suff R' : reachable w via by rewrite -(steps_nodes R').
  by exists m.
suff X : exists bc1, holds n via (has_chain bc1).
- case: X=>bc1 H; move: (Hi _ R _ H)=>P1.
  move: (local_chain_grows_fork_step D' H S H2)=>P2.
  case P1; case P2; clear P1 P2.
  - by move=><-<-; left.
  - case; case=> HH Gt Eq; right; split; rewrite -Eq in Gt; do? by [].
      by rewrite -Eq in HH; left.
      by rewrite -Eq in HH; right.

  - move=> Eq; case; case=> HH Gt; right; split; rewrite Eq in Gt; do? by [].
      by rewrite Eq in HH; left.
      by rewrite Eq in HH; right.

  (* Reasoning about forks *)
  case; case=> HH Gt; case; case=>HH' Gt';
  right; split; do? by move: (CFR_trans Gt Gt').
  (* --bc---bc1---bc' *)
  by left; move: (bc_spre_trans HH' HH).

  (*   /--bc
   * --
   *   \-----bc1---bc'
   *)
  by right; move: (bc_fork_prefix HH' (bc_spre_pre HH)).

  (*      /-- bc1                /---bc--bc1
   * --bc-               OR   ---
   *      \------- bc'           \-------------bc'
   *)
  case: (bc_relP bc bc').
  - by move/eqP=>Eq; subst bc'; contradict HH; move/norP=>[] _=>/norP;
       move/sprefixP in HH'; rewrite HH'=>/andP.
  - by move=>F; right.
  - by move=>Spf; left; apply/sprefixP.
  - by move/sprefixP=>Spf; move/sprefixP:(bc_spre_trans Spf HH')=>C;
       contradict HH; move/norP=>[] _=>/norP; rewrite C=>/andP.

  (*  /-bc                      /--bc-----------bc'
   *---------bc1          OR  --
   *      \---------bc'         \-------bc1
   * This is the most interesting case -- only provable if respecting CFR *)
  case: (bc_relP bc bc').
  - by move/eqP=>Eq; subst bc'; move: (CFR_trans Gt' Gt)=>C;
       contradict C; apply: CFR_nrefl.
  - by move=> F; right.
  - by move=>Spf; left; apply/sprefixP.
  - by move/sprefixP=>[b][ext] Eq; subst bc; move: (CFR_trans Gt Gt')=>C;
       move: (CFR_ext bc' b ext)=>C'; move: (CFR_excl C C').

rewrite /holds/has_chain.
move/um_eta: D';case; case=>id ps bt t [][->]_.
by exists (btChain (blockTree {|
    id := id; peers := ps; blockTree := bt; txPool := t |}))=>st[]<-.
Qed.

(*
* For simplicity, we assume all nodes are directly connected.
* This could be changed to incorporate a more realistic broadcast setting.
*)
Definition available_rel (b : Block) (n : nid) (w : World) :=
  exists (p : Packet),
    p \in inFlightMsgs w /\
    [\/ exists (peer : nid) (sh : seq Hash),
         msg p = InvMsg peer sh /\ dst p = n /\ hashB b \in sh |
       exists (hash : Hash),
         msg p = GetDataMsg n hash /\ src p = n /\ hashB b = hash
    ].

Definition all_available (n : nid) (w : World) : seq Hash :=
  let invs :=
    flatten [seq msg_hashes (msg p) |
      p <- inFlightMsgs w & (dst p == n) && (msg_type (msg p) == MInv)] in
  let gds :=
    flatten [seq msg_hashes (msg p) |p <- inFlightMsgs w &
      (src p == n) && (msg_type (msg p) == MGetData) && (n \in msg_from (msg p))] in
  undup (invs ++ gds).

Definition available b n w := hashB b \in all_available n w.

Lemma availableP b n w :
  reflect (available_rel b n w) (available b n w).
Proof.
case A: (available b n w); [constructor 1 | constructor 2]; move: A;
rewrite/available/all_available mem_undup -flatten_cat.
move/flattenP; case=>h0; rewrite mem_cat; move/orP; case;
move/mapP; case=>p0; rewrite mem_filter; rewrite/available_rel.
- move/andP=>[]/andP[] H1 H2 H3 H4 H5;
  exists p0; split; first done.
  case Msg: (msg p0)=>[|||||pr sh|]; do? by contradict H2; rewrite/msg_type Msg.
  left. exists pr, sh. split; first done. split; first by move/eqP in H1.
  by move: H5; rewrite H4 /msg_hashes Msg.
- move/andP=>[]/andP[]/andP[] H1 H2 H3 H4 H5 H6;
  exists p0; split; first done.
  case Msg: (msg p0)=>[||||||pr h]; do? by contradict H2; rewrite/msg_type Msg.
  right. exists h. split.
  by move: H3; rewrite /msg_from Msg mem_seq1; move/eqP=><-.
  split.
  by move/eqP in H1.
  by move: H6; rewrite H5 /msg_hashes Msg mem_seq1; move/eqP.
(* available b n w = false *)
move/flattenP. apply impliesPn; constructor.
case=>p [] iF; case.
- move=>[pr] [sh] [H1] [H2] H3. exists sh; last done.
  rewrite mem_cat; apply/orP. left.
  apply/mapP. exists p. rewrite mem_filter; apply/andP; split; last done.
  apply/andP; split; by [move/eqP in H2 | rewrite/msg_type H1].
  by rewrite /msg_hashes H1.
- move=>[hash] [H1] [H2] H3. exists [:: hash]; last first.
  by rewrite mem_seq1; move/eqP in H3.
  rewrite mem_cat; apply/orP. right.
  apply/mapP. exists p. rewrite mem_filter; apply/andP; split; last done.
  apply/andP; split.
    apply/andP; split; by [move/eqP in H2 | rewrite/msg_type H1].
    by rewrite/msg_from H1 mem_seq1.
  by rewrite /msg_hashes H1.
Qed.

Definition blocksFor n' w :=
  [seq msg_block (msg p) | p <- inFlightMsgs w & dst p == n'].

Lemma b_in_blocksFor p b w :
    p \in inFlightMsgs w -> (msg p = BlockMsg b) -> b \in blocksFor (dst p) w.
Proof.
move=>iF Msg.
rewrite/blocksFor; apply/mapP; exists p.
by rewrite mem_filter eqxx.
by rewrite/msg_block Msg.
Qed.

Definition largest_chain (w : World) (bc : Blockchain) :=
   forall (n' : nid) (bc' : Blockchain),
    holds n' w (fun st => has_chain bc' st -> bc >= bc').

Definition GStable w :=
  inFlightMsgs w = [::] /\
  exists (bc : Blockchain), forall (n : nid),
    holds n w (has_chain bc).

Definition GSyncing w :=
  exists (bc : Blockchain) (n : nid),
  [/\ holds n w (has_chain bc),

   (* The canonical chain is the largest in the network *)
   largest_chain w bc,

   (* Applying blocks in flight will induce either the canonical
      chain or a smaller one. *)
   forall n',
      holds n' w (fun st =>
         bc >= btChain (foldl btExtend (blockTree st) (blocksFor n' w))) &

   (* All blocks (in any BlockTree) are available to every node *)
   forall n',
     holds n' w (fun st =>
      (~exists b, available b n' w) /\ blocksFor n' w == [::] -> has_chain bc st)].

Definition Inv (w : World) :=
  Coh w /\ [\/ GStable w | GSyncing w].

Lemma Eventual_Consensus w n :
  Inv w -> (~exists b, available b n w) /\ blocksFor n w == [::] ->
  holds n w (fun st => exists bc, (has_chain bc st) /\ largest_chain w bc).
Proof.
case=>C; case=>[H|[bc][can_n][H1 H2 H3 H4]] Na st Fw.
- case: H=>cE[bc]H; exists bc; split=>//; first by move:(H _ _ Fw).
  move=>n' bc' st' Fw'/eqP Z.
  by move: (H n' _ Fw')=>/eqP; rewrite Z=>->; left.
by exists bc; split=>//; move: (H4 n _ Fw Na)=>Hc.
Qed.

Variable N : nat.

Lemma Inv_init : Inv (initWorld N).
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

Lemma Inv_step w w' q :
  Inv w -> system_step w w' q -> Inv w'.
Proof.
move=>Iw S; rewrite/Inv; split; first by apply: (Coh_step S).
case: S=>[|p st1 Cw _ iF Fw|proc t st1 Cw _ Fw]; first by elim=>_ <-; move: Iw=>[].
case: Iw=>_ [GStabW|GSyncW].
- by case GStabW=>noPackets; contradict iF; rewrite noPackets.
- case GSyncW=>can_bc [can_n] [] HHold HGt HInFlight HDiffAv.
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
    do? [subst can_n; rewrite findU (proj1 Cw)=>/=; case: ifP;
      by [move/eqP |
        NBlockMsg_dest q st1 p b Msg H; rewrite Msg P=><-; apply (HHold st1 Fw)
    ]];
    do? [rewrite findU (proj1 Cw)=>/=; case: ifP=>/=;
      by [move/eqP | move=>_ Fc; move: (HHold st' Fc)]
    ].
    (* BlockMsg *)
    rewrite findU (proj1 Cw)=>/=; case: ifP=>/=; last by move/eqP.
    BlockMsg_dest w q can_n can_bc st1 p iF Fw P Msg b X HHold HInFlight.
    * by move=>H; move: (btExtend_seq_same X H); move/eqP; rewrite eq_sym.
    * by move=>Con; contradict Con; apply btExtend_fold_not_worse.

 (* ... it's still the largest *)
  + case Msg: (msg p)=>[|||b|||]; rewrite Msg in P;
    (* All cases except BlockMsg *)
    rewrite/holds/localState/has_chain=>n' bc' st';
    case X: (can_n == dst p); move/eqP in X;
    rewrite findU (proj1 Cw)=>/=; case: ifP=>/=; move/eqP;
    do? by [
      move=>_ Fc; move: (HGt n' bc' st' Fc) |
      NBlockMsg_dest q st1 p b Msg H; rewrite /has_chain Msg P=><-;
      rewrite -Eq in Fw=>Hc; move: (HGt n' bc' st1 Fw Hc)].
    (* BlockMsg *)
    BlockMsg_dest w q can_n can_bc st1 p iF Fw P Msg b X HHold HInFlight.
    * by move=>H; move: (btExtend_seq_same X H)=><-/eqP->; left.
    * by move=>Con; contradict Con; apply btExtend_fold_not_worse.

    move=>Dst [] Eq; subst stPm; subst n'=>Hc.
    rewrite/has_chain in Hc; move/eqP in Hc; subst bc'.
    rewrite [procMsg _ _ _] surjective_pairing in P; case: P; move=><- _.
    rewrite (procMsg_block_btExtend st1 b (ts q)); clear X.
    move: (b_in_blocksFor iF Msg)=>X.
    specialize (HInFlight (dst p) _ Fw); simpl in HInFlight.
    case: (btExtend_fold_sameOrBetter (blockTree st1) (blocksFor (dst p) w)).
    * move=>->.

(* the canonical chain can only change throught a MintT transition *)
(* TODO: refactor it into a lemma *)
- admit.
Admitted.