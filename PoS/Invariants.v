From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Blockchain Protocol Semantics States.
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

Lemma has_chain_inj :
  forall (n : nid) (st: State) (w : World) (bc bc' : Blockchain),
  find n (localState w) = Some st ->
  holds n w (has_chain bc) -> holds n w (has_chain bc') -> bc = bc'.
Proof.
move=> n st w bc bc' sF nbc nbc'.
rewrite /holds/has_chain in nbc nbc'.
specialize (nbc st). specialize (nbc' st). rewrite sF in nbc nbc'.
assert (Some st = Some st). by [].
pose proof (nbc H) as nbc. pose proof (nbc' H) as nbc'. clear H.
move/eqP in nbc. move/eqP in nbc'. rewrite nbc in nbc'. by [].
Qed.

Definition chain_sync_agreement (w w' : World) :=
  forall (n n' : nid) (bc bc' : Blockchain),
    holds n w (has_chain bc) ->
    reachable w w' ->
    holds n' w' (has_chain bc') ->
    size bc' == size bc ->
    bc == bc'.

(*
TODO: 

1. Simple property: local BC only grows with stepping;
2. More complicated: the "rollback" is no more than a contstant;

*)

Lemma local_chain_only_grows (w w' : World) :
  forall (n : nid) (st st' : State) (bc : Blockchain),
    let: bc' := btChain (blockTree st') in
    find n (localState w) = Some st ->
    holds n w (has_chain bc) ->
    reachable w w' ->
    find n (localState w') = Some st' ->
    holds n w' (has_chain bc') ->
    size bc' <= size bc.
Proof.
move=> n st st' bc sF nbc R sF'.
elim: R st st' bc nbc sF sF' => [|via z S R Hi] st st' bc nbc sF sF' nbc'.
(* 0 steps *)
- by pose proof (has_chain_inj sF nbc nbc'); rewrite -H; apply leqnn.
(* Induction over system_steps *)
- specialize (steps_nodes sF R)=>sFV.
  specialize (gen_eta sFV). elim. move=> sv. elim. move=> svF _.
  specialize (Hi st sv bc nbc sF svF). clear st nbc sF sFV.
  case S. (* Prove for ONE system_step *)
  + elim. move=> _ vzEq. rewrite vzEq in Hi svF. rewrite svF in sF'.
    by case: sF'=>eq; rewrite eq in Hi; specialize (Hi nbc').
  + move=> p ost _ _ _. case (procMsg ost (msg p)).
    specialize (system_step_local_step S svF sF').
    (* Prove for induced local transitions *)
    move=> LS _ _ _. case LS; clear LS ost p.
    * move=> eq. rewrite eq in svF.
      specialize (no_change_has_held svF S nbc' sF').
      move=> h. rewrite -eq in h. specialize (Hi h). rewrite eq in Hi.
      by apply Hi.
    (* TODO: Write lemmas for procMsg and procInt *)
Qed.