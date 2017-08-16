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

Definition node_with_chain n w bc :=
  n \in dom (localState w) /\ holds n w (has_chain bc).

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

1. Simple property: local BC only grows with stepping;
2. More complicated: the "rollback" is no more than a contstant;

 *)

Lemma local_chain_grows_fork_step (w w' : World) n bc bc':
  n \in dom (localState w) -> 
  holds n w (has_chain bc) ->
  system_step w w' ->
  holds n w' (has_chain bc') ->
  [bc <<= bc'] \/ fork bc bc'.
Proof.
move=>D H1 S H2; move: (Coh_step S)=>C2.
case: S=>[[C]Z|p [n' prs bt pool a i] C _ F|
          proc t [n' prs bt pool a i] C F].

(* 0 steps *)
- by subst w'; rewrite (has_chain_func D H1 H2); apply or_introl; apply: bc_pre_refl.
(* Step is procedding a message *)

(* Receiving a message *)
- have E: (n' = (dst p)) by case:C=>_/(_ (dst p) _ F)/eqP. subst n'.

  (* Two sub-cases: (dst p) =? n *)
  case N : (n == dst p);[move/eqP:N=>N; subst n|]; last first.
  (* Message not to us: don't really care about the outcome of procMsg! *)
  + set pms := (procMsg _ _); case: pms=>st' ms Z; subst w'.
    rewrite /holds/= findU N/= in H2.
    by rewrite -(has_chain_func D H1 H2); apply or_introl; apply: bc_pre_refl.
  rewrite [procMsg _ _]surjective_pairing=>Z;
  (* Avoiding premature unfolding. *)
  set Pm := nosimpl (procMsg _ _) in Z; subst w'. 
  rewrite /holds/= findU eqxx/= (proj1 (C)) in H2.
  move/(H2 Pm.1): (erefl (Some Pm.1))=>{H2} H2.
  move: (H1 _ F)=>{H1 C2 F}/=H1. 
  by apply: (@procMsg_bc_prefix_or_fork bc bc'
        {| id := dst p; peers := prs; blockTree := bt; txPool := pool; addr := a; inv := i |}
        (msg p)); move/eqP: H2; move/eqP: H1.

(* Internal transition *)
(* Two sub-cases: proc =? n *)
case N : (n == proc);[move/eqP:N=>N; subst n|]; last first.
- set pms := (procInt _ _); case: pms=>st' ms Z; subst w'.
  rewrite /holds/= findU N/= in H2.
  by left; rewrite -(has_chain_func D H1 H2); apply: bc_pre_refl.

(* Another interesting part of the proof: n == proc.
   Consider all branches of procInt and proof the property for each one.
   Don't hesitate to introduce auxiliary lemmas. *)  
rewrite [procInt _ _]surjective_pairing=>Z.
set Pi := nosimpl (procInt _ _) in Z; subst w'.
rewrite /holds/= findU eqxx/= (proj1 (C)) in H2.

  
Admitted.

(* Big-step case, proven by induction *)
Lemma local_chain_only_grows (w w' : World) n bc bc':
  n \in dom (localState w) -> 
  holds n w (has_chain bc) ->
  reachable w w' ->
  holds n w' (has_chain bc') ->
  [bc <<= bc'].
Proof.
move=>D H1 [m]R H2.
elim: m w' R bc' H2=>/=[w'<-|m Hi w' [via][R S]]bc' H2.
- by move/(has_chain_func D H1 (bc':=bc')):H2=><-; apply bc_pre_refl.
have D': n \in dom (localState via).
- suff R' : reachable w via by rewrite -(steps_nodes R').
  by exists m. 
suff X : exists bc1, holds n via (has_chain bc1).
- case: X=>bc1 H; move: (Hi _ R _ H)=>P.
  apply: (bc_pre_trans P).
  apply: (local_chain_only_grows_step D' H S H2).
rewrite /holds/has_chain.
move/um_eta: D';case; case=>id ps bt t a i[][->]_.
by exists (btChain (blockTree {|
    id := id; peers := ps; blockTree := bt; txPool := t;
    addr := a; inv := i |}))=>st[]<-. 
Qed.  

(* Sketch of global invariant
 * For simplicity, the predicate available assumes all nodes are directly connected,
 * but this could be changed to incorporate a more realistic broadcast setting.
 *)

Definition available b n w :=
  exists (p : Packet) (peer : nid) (sh : seq Hash),
    p \in inFlightMsgs w /\ msg p = InvMsg peer sh /\ dst p = n /\ hashB b \in sh.

Definition GAligned w :=
  forall (n n' : nid) (bc bc' : Blockchain),
    node_with_chain n w bc ->
    node_with_chain n' w bc ->
    bc = bc'.

Definition GBehindWithDiffAvailable w :=
  exists (n : nid) (bc : Blockchain),
    node_with_chain n w bc /\
    forall (n' : nid) (bc': Blockchain),
      node_with_chain n' w bc' ->
      [bc' <<= bc] /\
      forall (b : Block),
        b \in prefix_diff bc' bc ->
        available b n w.

Definition Inv (w : World) :=
  Coh w /\
  [\/ GAligned w | GBehindWithDiffAvailable w].

Variable N : nat.
Lemma Inv_init : Inv (initWorld N).
Proof.
split. by apply Coh_init. apply or_introl. case=> n' bc bc'.
Admitted.
