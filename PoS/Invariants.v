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
(*
Definition holds (n : nid) (w : World) (cond : State -> Prop) :=
  forall (st : State),
    find n (localState w) = Some st -> cond st.
*)

Definition has_chain (bc : Blockchain) (st : State) : Prop :=
  btChain (blockTree st) == bc.

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

Lemma local_chain_only_grows_step (w w' : World) n bc bc':
  n \in dom (localState w) -> 
  holds n w (has_chain bc) ->
  system_step w w' ->
  holds n w' (has_chain bc') ->
  [bc <<= bc'].
Proof.
move=>D H1 S H2; move: (Coh_step S)=>C2.
case: S=>[[C]Z|
          p [n' prs bt pool a i] C If F|
          proc t [n' prs bt pool a i] C F].
(* 0 steps *)
- by subst w'; rewrite (has_chain_func D H1 H2); apply: bc_pre_refl.
(* Step is procedding a message *)

(* Receiving a message *)
- have E: (n' = (dst p)) by case:C=>_/(_ (dst p) _ F)/eqP. subst n'.

  (* Two sub-cases: (dst p) =? n *)
  case N : (n == dst p);[move/eqP:N=>N; subst n|]; last first.
  (* Message not to us: don't really care about the outcome of procMsg! *)
  + set pms := (procMsg _ _); case: pms=>st' ms Z; subst w'.
    rewrite /holds/= findU N/= in H2.
    by rewrite -(has_chain_func D H1 H2); apply: bc_pre_refl.

    (* Now the interesting case: consider all possible messages, i.e. do
     case: (msg p). 
     and prove for each subcase. Perhaps, you might move
     some parts into lemmas 
     THIS is the main part of the proof! *)
  admit.

(* Internal transition *)
(* Two sub-cases: proc =? n *)
  case N : (n == proc);[move/eqP:N=>N; subst n|]; last first.
  set pms := (procInt _ _); case: pms=>st' ms Z; subst w'.
  rewrite /holds/= findU N/= in H2.
  by rewrite -(has_chain_func D H1 H2); apply: bc_pre_refl.

(* Another interesting part of the proof:
   consider all branches in procInt and proof for each one.
   Don't hesitate to introduce auxiliary lemmas. *)  

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

