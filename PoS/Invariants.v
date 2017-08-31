From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap.
Require Import Blockchain Protocol Semantics States BlockchainProperties.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

(*
TODO:

2. More complicated: the "rollback" is no more than a contstant;

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
Definition available (blocks : seq Block) n w :=
  forall (b : Block),
  b \in blocks ->
  exists (p : Packet) (peer : nid) (sh : seq Hash),
    p \in inFlightMsgs w /\ msg p = InvMsg peer sh /\ dst p = n /\ hashB b \in sh.

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

   (* Blocks in flight induce either the canonical chain  or a smaller one
    * In other words, no BlockMsg will change the canonical chain. *)
   forall (p : Packet) (b : Block) (n' : nid) (bc' : Blockchain),
     p \in inFlightMsgs w -> msg p = BlockMsg b -> n' = dst p ->
     holds n' w (fun st => bc >= btChain (btExtend (blockTree st) b)) &

   (* The difference needed to obtain the canonical chain is available *)
   forall (n' : nid) (bc' : Blockchain),
     holds n' w (has_chain bc') -> available (bc_diff bc' bc) n' w
].
(* TODO: prove that applying difference results in canonical chain *)

Definition Inv (w : World) :=
  Coh w /\
  [\/ GStable w | GSyncing w].

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

Lemma Inv_step w w' q :
  Inv w -> system_step w w' q -> Inv w'.
Proof.
move=>Iw S; rewrite/Inv; split; first by apply: (Coh_step S).
case: S=>[|p st1 Cw _ iF Fw|proc t st1 Cw _ Fw]; first by elim=>_ <-; move: Iw=>[].
case: Iw=>_ [GStabW|GSyncW].
- by case GStabW=>noPackets; contradict iF; rewrite noPackets.
- case GSyncW=>can_bc [can_n] [] HHold HGt HInFlight HDiffAv.
  case P: (procMsg _ _ _)=>[stPm ms]; move=>->; right.
  case Msg: (msg p)=>[|||b|||]; rewrite Msg in P.
  (* For non-block messages, the canonical chain is guaranteed to remain the same *)
  assert (forall b, msg p != BlockMsg b) by (move=>b; rewrite Msg; by []).
  exists can_bc; exists can_n; split.
  (* ... the original node still retains it *)
  + rewrite/holds/localState/has_chain=>st'; case X: (can_n == dst p); move/eqP in X.
    * subst can_n; rewrite findU (proj1 Cw)=>/=; case: ifP; do? by [move/eqP].
      by move=>_ [] <-; move: (procMsg_non_block_nc_btChain st1 (ts q) H);
         rewrite Msg P=><-; apply (HHold st1 Fw).
    * rewrite findU (proj1 Cw)=>/=; case: ifP=>/=; do? by[move/eqP].
      by move=>_ Fc; move: (HHold st' Fc).
  (* ... it's still the largest *)
  + rewrite/holds/localState/has_chain=>n' bc' st';
    case X: (can_n == dst p); move/eqP in X;
    rewrite findU (proj1 Cw)=>/=; case: ifP=>/=; move/eqP;
    by [
      move=>_ Fc; move: (HGt n' bc' st' Fc) |
      move=>Eq [] <-; move: (procMsg_non_block_nc_btChain st1 (ts q) H);
      rewrite /has_chain Msg P=><-; rewrite -Eq in Fw=>Hc; move: (HGt n' bc' st1 Fw Hc)
    ].
  (* ... no surprise blocks in the packet soup *)
  + move=>/==>p0 b0 n' bc'; rewrite mem_cat orbC; case/orP.
    (* p0 is already in the packet soup *)
    * move/mem_rem=> iF0 bM0 dst0 st'; rewrite/localState.
      case X: (dst p0 == dst p); subst n'; last first.
        (* trivial case, no change from last state *)
        rewrite findU ?(proj1 Cw)=>//; case: ifP.
        by move/eqP in X; move/eqP=>Con; contradict Con.
        by move=>_ F0; have: (dst p0 = dst p0) by []=>Obvs;
           apply (HInFlight p0 b0 (dst p0) bc' iF0 bM0 Obvs st' F0).
        (* inductive case -- msg p is applied, THEN b0 is applied *)
        rewrite findU X/= ?(proj1 Cw)=>//[][]<-.
        have: (dst p0 = dst p0) by []=>Obvs; move/eqP in X; rewrite -X in Fw.
        move: (HInFlight p0 b0 (dst p0) bc' iF0 bM0 Obvs st1 Fw).
        by move: (procMsg_non_block_nc_blockTree st1 (ts q) H); rewrite Msg P=>/= <-.
    (* p0 is a newly emitted message *)
    * case: st1 P Fw=>/=id peers bt tp[]-> Z2 F; subst ms; rewrite inE=>/eqP=>Z.
      subst p0=>Bm[s]/=[F']H'; by contradict Bm.
  (* ... the difference is still in flight *)
  +

Admitted.