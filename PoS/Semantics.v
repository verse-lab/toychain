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
  [/\ valid (localState w),
     forall (n : nid),
       holds n w (fun st => id st == n),
     forall (n : nid),
       holds n w (fun st => valid (blockTree st)),
     forall (n : nid),
       holds n w (fun st => validH (blockTree st)),
     forall (n : nid),
       holds n w (fun st => has_init_block (blockTree st)) &
     forall (n : nid),
       holds n w (fun st => uniq (peers st))
  ].

Record Qualifier := Q { ts: Timestamp; allowed: nid; }.

(* Don't you worry about uniqueness of the messages? *)
Inductive system_step (w w' : World) (q : Qualifier) : Prop :=
| Idle of Coh w /\ w = w'

| Deliver (p : Packet) (st : State) of
      Coh w & (dst p) = allowed q &
      p \in inFlightMsgs w &
      find (dst p) (localState w) = Some st &
      let: (st', ms) := procMsg st (src p) (msg p) (ts q) in
      w' = mkW (upd (dst p) st' (localState w))
               (seq.rem p (inFlightMsgs w) ++ ms)
               (rcons (consumedMsgs w) p)

| Intern (proc : nid) (t : InternalTransition) (st : State) of
      Coh w & proc = allowed q &
      find proc (localState w) = Some st &
      let: (st', ms) := (procInt st t (ts q)) in
      w' = mkW (upd proc st' (localState w))
               (ms ++ (inFlightMsgs w))
               (consumedMsgs w).

Definition Schedule := seq Qualifier.

Fixpoint reachable' (s : Schedule) (w w' : World) : Prop :=
  if s is (ins :: insts)
  then exists via, reachable' insts w via /\ system_step via w' ins
  else w = w'.

Definition reachable (w w' : World) :=
  exists s, reachable' s w w'.

(* TODO: define a relation that "reconstructs" an "ideal" blockchain *)
(* from a given world, and prove its properties (e.g., functionality, *)
(* meaning that one world corresponds to one blobkchain *)
(* precisely). This might require to state additional "coherence" *)
(* properties of the world, such as block-trees of the majority of
involved peers are not _too different_. *)

Variable N : nat.

Definition initWorld := mkW (initState N) [::] [::].

Ltac InitState_induction :=
move=>n st; elim: N=>//=[|n' Hi];
do? [by move/find_some; rewrite dom0 inE];
do? [
  rewrite findUnL; last by [
    case: validUn; rewrite ?um_validPt ?valid_initState//;
    move=>k; rewrite um_domPt !inE=>/eqP <-;
    rewrite dom_initState mem_iota addnC addn1 ltnn andbC
  ]
];
case: ifP=>//; rewrite um_domPt inE=>/eqP<-.

Ltac Coh_step_case n d H F :=
  case B: (n == d);
  do? [by move=>F; move: (H n _ F) |
    case: ifP; last done
  ]; move=>_ [] <-.

Lemma Coh_init : Coh initWorld.
Proof.
rewrite /initWorld/initState/localState/=; split;
do? InitState_induction; do? [rewrite um_findPt; case=><-].
- by apply: valid_initState.
- by rewrite/Init/id.
- by rewrite /Init/blockTree gen_validPt.
- by rewrite/Init/validH/blockTree=>h b H;
     move: (um_findPt_inv H); elim=>->->.
- by rewrite/Init/has_init_block/blockTree um_findPt.
- by rewrite/Init/peers.
Qed.

Lemma Coh_step w w' q:
  system_step w w' q -> Coh w'.
Proof.
move=>S; (have: system_step w w' q by done)=>S'.
case: S'.
(* Idle *)
by case=>Cw <-.
(* Deliver *)
- move=> p st [H1 H2 H3 H4 H5 H6] _ iF sF; case P: (procMsg _ _ _)=>[st' ms].
  move=>->; split;
    do? [rewrite /holds/localState; move=> n stN; rewrite findU=>/=].
  + rewrite /localState validU=>/=; apply H1.
  + Coh_step_case n (dst p) H2 F; move/eqP: (H2 (dst p) _ sF)=>Id.
    move: (procMsg_id_constant st (src p) (msg p) (ts q)).
    by move/eqP in B; subst n; rewrite Id=>->; rewrite P.
  + Coh_step_case n (dst p) H3 F; move: (H3 (dst p) _ sF)=>V.
    by move: (procMsg_valid (src p) (msg p) (ts q) V); rewrite P.
  + Coh_step_case n (dst p) H4 F;
    move: (H3 (dst p) _ sF)=>V; move: (H4 (dst p) _ sF)=>VH;
    rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _;
    by apply procMsg_validH.
  + Coh_step_case n (dst p) H5 F.
    move: (H3 (dst p) _ sF)=>V; move: (H4 (dst p) _ sF)=>VH;
    rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _;
    by move: (H5 (dst p) _ sF); apply procMsg_has_init_block.
  + Coh_step_case n (dst p) H6 F.
    move: (H3 (dst p) _ sF)=>V; move: (H4 (dst p) _ sF)=>VH;
    rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _.
    by move: (H6 (dst p) _ sF); apply procMsg_peers_uniq.

(* Intern *)
- move=> proc t st [H1 H2 H3 H4 H5 H6] _ sF. case P: (procInt _ _ _)=>[st' ms].
  move=>->; split;
    do? [rewrite /holds/localState; move=> n stN; rewrite findU=>/=].
  + rewrite /localState validU=>/=; apply H1.
  + Coh_step_case n proc H2 F; move/eqP: (H2 proc _ sF)=>Id.
    move: (procInt_id_constant st t (ts q)).
    by move/eqP in B; subst n; rewrite Id=>->; rewrite P.
  + Coh_step_case n proc H3 F; move: (H3 proc _ sF)=>V.
    by move: (procInt_valid st t (ts q)); rewrite P/==><-.
  + Coh_step_case n proc H4 F;
    move: (H3 proc _ sF)=>V; move: (H4 proc _ sF)=>VH;
    rewrite [procInt _ _ _] surjective_pairing in P; case: P=><- _;
    by apply procInt_validH.
  + Coh_step_case n proc H5 F.
    move: (H3 proc _ sF)=>V; move: (H4 proc _ sF)=>VH;
    rewrite [procInt _ _ _] surjective_pairing in P; case: P=><- _;
    by move: (H5 proc _ sF); apply procInt_has_init_block.
  + Coh_step_case n proc H6 F.
    move: (H3 proc _ sF)=>V; move: (H4 proc _ sF)=>VH;
    rewrite [procInt _ _ _] surjective_pairing in P; case: P=><- _.
    by move: (H6 proc _ sF); apply procInt_peers_uniq.
Qed.

(* Stepping does not remove or add nodes *)
Lemma step_nodes w w' q :
  system_step w w' q ->
  dom (localState w) =i dom (localState w').
Proof.
case: w w'=>sm f c [sm'] f' c'; case=>/=; first by case=>C; case=>->/=.
- move=>p st1 C iq pf F; case: (procMsg st1 (src p) (msg p))=>st2 ms[]->{sm'}Z1 Z2.
  subst f' c'=>z; rewrite domU inE/=; case: ifP=>///eqP->{z}.
  by move/find_some: F->; case: C.
move=>p t st1 C iq F; case: (procInt st1 t)=>st2 ms[]->{sm'}Z1 Z2.
subst f' c'=>z; rewrite domU inE/=; case: ifP=>///eqP->{z}.
by move/find_some: F->; case: C.
Qed.

Lemma steps_nodes (w w' : World):
  reachable w w' ->
  dom (localState w) =i dom (localState w').
Proof.
move=>[sch] R. elim: sch w' R=>/=[w'->|q qs Hi w' [via] [R S]]//z.
by move: (Hi via R)->; rewrite (step_nodes S).
Qed.

Lemma system_step_local_step w w' q:
  forall (n : nid) (st st' : State),
    system_step w w' q ->
    find n (localState w) = Some st ->
    find n (localState w') = Some st' ->
    local_step st st'.
Proof.
move=> n st st'.
case.
(* Idle *)
- by move=>[] cW<-->[]->; constructor 1.
(* Deliver *)
- move=> p old_st cW _ pIF osF.
  case P: (procMsg _ _ _). case: w'. move=> sm' f' c'. case.
  move=> A B C. subst sm' f' c'. move=> sF. rewrite /localState findU=>/=.
  case B: (n == dst p); last first.
    (* n != dst p -- node n is Idle => st st' *)
    + move=> F. rewrite F in sF. case: sF=>stEq. rewrite stEq. by constructor 1.
    (* When n == dst p, notice that st = old_st
     * and st and st' are related by procMsg *)
    + move/eqP in B. rewrite -B in osF. rewrite sF in osF. case: osF=>->.
      case: ifP; last first.
        by move=> _ con; contradict con.
        move=> _ sEq. case: sEq=>stEq. rewrite stEq in P.
        by constructor 2 with (src p) (msg p) (ts q); rewrite P.
(* Intern *)
- move=> proc t old_st cW _ osF.
  case P: (procInt _ _ _). case: w'. move=> sm' f' c'. case.
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
        by constructor 3 with t (ts q); rewrite P.
Qed.

Lemma no_change_still_holds (w w' : World) (n : nid) q st cond:
  find n (localState w) = Some st ->
  holds n w cond ->
  system_step w w' q ->
  find n (localState w') = Some st ->
  holds n w' cond.
Proof.
move=>f h S sF st' s'F; rewrite s'F in sF; case: sF=>->.
by move: (h st f).
Qed.

Lemma no_change_has_held (w w' : World) (n : nid) q st cond:
  find n (localState w) = Some st ->
  system_step w w' q->
  holds n w' cond ->
  find n (localState w') = Some st ->
  holds n w cond.
Proof.
move=> f S h sF st' s'F.
by rewrite f in s'F; case: s'F=><-; move: (h st sF).
Qed.

End Semantics.
