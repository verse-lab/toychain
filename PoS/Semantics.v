From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Relations.
Require Import Protocol Blockchain States.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Semantics.

(* Number of nodes *)
Definition PacketSoup := seq Packet.

Record World :=
  mkW {
    localState : StateMap;
    inFlightMsgs : PacketSoup;
    consumedMsgs : PacketSoup;
  }.

(* Network semantics *)
Definition holds (n : nid) (w : World) (cond : State -> Prop) :=
  forall (st : State),
    find n (localState w) = Some st -> cond st.

Definition Coh (w : World) :=
  (* No duplicating nodes *)
  valid (localState w) /\
  forall (n : nid),
    (* IDs match *)
    holds n w (fun st => id st == n).

(* Don't you worry about uniqueness of the messages? *)
Inductive system_step (w w' : World) : Prop :=
| Idle of Coh w /\ w = w'

| Deliver (p : Packet) (st : State) of
      Coh w & p \in inFlightMsgs w &
      find (dst p) (localState w) = Some st &
      let: (st', ms) := procMsg st (msg p) in
      w' = mkW (upd (dst p) st' (localState w))
               (ms ++ seq.rem p (inFlightMsgs w))
               (rcons (consumedMsgs w) p)

| Intern (proc : nid) (t : InternalTransition) (st : State) of
      Coh w & find proc (localState w) = Some st &
      let: (st', ms) := procInt st t in
      w' = mkW (upd proc st' (localState w))
               (ms ++ (inFlightMsgs w))
               (consumedMsgs w).

Definition system_step_star := clos_refl_trans_n1 _ system_step.

Fixpoint reachable' n (w w' : World) : Prop :=
  if n is n'.+1
  then exists via, reachable' n' w via /\ system_step via w'
  else w = w'.
    
Definition reachable (w w' : World) :=
  exists n, reachable' n w w'.

(* TODO: define a relation that "reconstructs" an "ideal" blockchain *)
(* from a given world, and prove its properties (e.g., functionality, *)
(* meaning that one world corresponds to one blobkchain *)
(* precisely). This might require to state additional "coherence" *)
(* properties of the world, such as block-trees of the majority of
involved peers are not _too different_. *)

Variable N : nat.

Definition initWorld := mkW (initState N) [::] [::].

Lemma Coh_init : Coh initWorld.
Proof.
rewrite /initWorld/initState/localState/=; split.
- by apply: valid_initState.
(* Since the state is constructed inductively, use induction on N *)
move=>n st; elim: N=>//=[|n' Hi].
  by move/find_some; rewrite dom0 inE.
(* The main induction transition. *)
rewrite findUnL; last first.
- case: validUn; rewrite ?um_validPt ?valid_initState//.
  move=>k; rewrite um_domPt !inE=>/eqP Z; subst k.
  by rewrite dom_initState mem_iota addnC addn1 ltnn andbC. 
case: ifP=>//; rewrite um_domPt inE=>/eqP<-. 
by rewrite um_findPt; case=><-.  
Qed.  

(* Stepping does not remove or add nodes *)
Lemma step_nodes w w' :
  system_step w w' ->
  dom (localState w) =i dom (localState w').
Proof.
case: w w'=>sm f c [sm'] f' c'; case=>/=; first by case=>C; case=>->/=.
- move=>p st1 C pf F; case: (procMsg st1 (msg p))=>st2 ms[]->{sm'}Z1 Z2.
  subst f' c'=>z; rewrite domU inE/=; case: ifP=>///eqP->{z}.
  by move/find_some: F->; case: C.
move=>p t st1 C F; case: (procInt st1 t)=>st2 ms[]->{sm'}Z1 Z2.
subst f' c'=>z; rewrite domU inE/=; case: ifP=>///eqP->{z}.
by move/find_some: F->; case: C.
Qed.

Lemma steps_nodes (w w' : World):
  reachable w w' ->
  dom (localState w) =i dom (localState w').
Proof.
move=>[n] R; elim: n w' R=>/=[w'->|n Hi w' [via][R S]]//z. 
by move: (Hi via R)->; rewrite (step_nodes S).
Qed.

Lemma system_step_local_step w w' :
  forall (n : nid) (st st' : State),
    system_step w w' ->
    find n (localState w) = Some st ->
    find n (localState w') = Some st' ->
    local_step st st'.
Proof.
move=> n st st'.
case.
(* Idle *)
- by move=>[] cW<-->[]->; constructor 1.
(* Deliver *)
- move=> p old_st cW pIF osF.
  case P: (procMsg old_st (msg p)). case: w'. move=> sm' f' c'. case.
  move=> A B C. subst sm' f' c'. move=> sF. rewrite /localState findU=>/=.
  case B: (n == dst p); last first.
    (* n != dst p -- node n is Idle => st st' *)
    + move=> F. rewrite F in sF. case: sF=>stEq. rewrite stEq. by constructor 1.
    (* When n == dst p, notice that st = old_st
     * and st and st' are related by procMsg *)
    + move/eqP in B. rewrite -B in osF. rewrite sF in osF. case: osF.
      move=> stEq. rewrite -stEq in P. clear stEq old_st.
      case: ifP; last first.
        by move=> _ con; contradict con.
        move=> _ sEq. case: sEq=>stEq. rewrite stEq in P.
        by constructor 2 with (msg p); rewrite P.
(* Intern *)
- move=> proc t old_st cW osF.
  case P: (procInt old_st t). case: w'. move=> sm' f' c'. case.
  move=> A B C. subst sm' f' c'. move=> sF. rewrite /localState findU=>/=.
  case B: (n == proc); last first.
    (* n != proc -- node n is Idle => st st' *)
    + move=> F. rewrite F in sF. case: sF=>stEq. rewrite stEq. by constructor 1.
    (* n == proc => update; akin to Deliver *)
    + move/eqP in B. rewrite -B in osF. rewrite sF in osF. case: osF.
      move=> stEq. rewrite -stEq in P. clear stEq old_st.
      case: ifP; last first.
        by move=> _ con; contradict con.
        move=> _ sEq. case: sEq=> stEq. rewrite stEq in P.
        by constructor 3 with t; rewrite P.
Qed.

Lemma no_change_still_holds (w w' : World) (n : nid) st cond:
  find n (localState w) = Some st ->
  holds n w cond ->
  system_step w w' ->
  find n (localState w') = Some st ->
  holds n w' cond.
Proof.
move=>f h S sF st' s'F; rewrite s'F in sF; case: sF=>->.
by move: (h st f).
Qed.

Lemma no_change_has_held (w w' : World) (n : nid) st cond:
  find n (localState w) = Some st ->
  system_step w w' ->
  holds n w' cond ->
  find n (localState w') = Some st ->
  holds n w cond.
Proof.
move=> f S h sF st' s'F.
by rewrite f in s'F; case: s'F=><-; move: (h st sF).
Qed.

Lemma Coh_step w w' :
  system_step w w' -> Coh w'.
Proof.
case: w w'=>sm f c [sm'] f' c'. case=>/=.
(* Idle *)
- by case=>Cw []<-<-<-.
(* Deliver *)
- move=> p st Cw iF sF. case P: (procMsg st (msg p)).
  case. move=> A B C. subst sm' f' c'. split.
  + rewrite /localState validU=>/=. apply Cw.
  + rewrite /holds/localState. move=> n stN. rewrite findU=>/=.
    case B: (n == dst p); last first.
    by move=> F; apply Cw; rewrite /localState; apply F.
    case: ifP; last first.
      by move=> _ con; contradict con.
      move=> vsm sEq. case: sEq=>stEq. rewrite stEq in P. clear stEq.
      move/eqP in B. rewrite -B in sF.
      (* Coh w => id st = n *)
      move: Cw. elim. move=> _. rewrite /holds/localState. move=> idN.
      apply idN in sF. move/eqP in sF. rewrite -sF.
      rewrite eq_sym. apply /eqP. apply id_constant.
      by constructor 2 with (msg p); rewrite P.
(* Intern *)
- move=> proc t st Cw sF. case P: (procInt st t).
  case. move=> A B C. subst sm' f' c'. split.
  + rewrite /localState validU=>/=. apply Cw.
  + rewrite /holds/localState. move=>n stN. rewrite findU=>/=.
    case B: (n == proc); last first.
    by move=> F; apply Cw; rewrite /localState; apply F.
    case: ifP; last first.
      by move=> _ con; contradict con.
      move=> vsm sEq. case: sEq=>stEq. rewrite stEq in P. clear stEq.
      move/eqP in B.
      (* Coh w => id st = n *)
      move: Cw. elim. move=> _. rewrite /holds/localState. move=> idN.
      apply idN in sF. move/eqP in sF. rewrite -B in sF.
      rewrite -sF. rewrite eq_sym. apply /eqP. apply id_constant.
      by constructor 3 with t; rewrite P.
Qed.

End Semantics.
