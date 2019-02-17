From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep Relations.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import Protocol Chains Parameters Forests States.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module Type ConsensusNetwork
       (P : ConsensusParams) (F : Forest P)
       (Pr : ConsensusProtocol P F) (Ns : NetState P F Pr).
Import P Pr Ns F.


Definition PacketSoup := seq Packet.

Record World :=
  mkW {
    localState : StateMap;
    inFlightMsgs : PacketSoup;
    consumedMsgs : PacketSoup;
  }.

(* Network semantics *)
Definition holds (n : Address) (w : World) (cond : State -> Prop) :=
  forall (st : State),
    find n (localState w) = Some st -> cond st.

Definition Coh (w : World) :=
  [/\ valid (localState w),
     forall (n : Address),
       holds n w (fun st => id st == n),
     (* forall (n : Address), *)
     (*   holds n w (fun st => valid (blockTree st)), *)
     forall (n : Address),
       holds n w (fun st => valid (blockTree st) -> validH (blockTree st)),
     forall (n : Address),
       holds n w (fun st => valid (blockTree st) -> has_init_block (blockTree st)) &
     forall (n : Address),
       holds n w (fun st => uniq (peers st))
  ].

Record Qualifier := Q { ts: Timestamp; allowed: Address; }.

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

| Intern (proc : Address) (t : InternalTransition) (st : State) of
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

Definition initWorld := mkW initState [::] [::].

Ltac Coh_step_case n d H F :=
  case B: (n == d);
  do? [by move=>F; move: (H n _ F) |
    case: ifP; last done
  ]; move=>_ [] <-.

Lemma holds_Init_state : forall (P : State -> Prop) n, P (Init n) ->
  holds n {| localState := initState; inFlightMsgs := [::]; consumedMsgs := [::] |} (fun st : State => P st).
Proof.
move => P n H_P; rewrite /initState.
have H_in: n \in enum Address by rewrite mem_enum.
have H_un: uniq (enum Address) by apply enum_uniq.
move: H_in H_un; elim: (enum Address) => //=.
move => a s IH; rewrite inE; move/orP; case.
* move/eqP => H_eq /=.
  rewrite H_eq; move/andP => [H_in H_u].
  rewrite /holds /= => st; rewrite findPtUn; first by case => H_i; rewrite -H_i -H_eq.
  by case: validUn; rewrite ?validPt ?valid_initState'//;
   move=>k; rewrite domPt !inE=>/eqP <-;
   rewrite dom_initState' //; move/negP: H_in.
* move => H_in; move/andP => [H_ni H_u].
  have H_neq: n <> a by move => H_eq; rewrite -H_eq in H_ni; move/negP: H_ni.
  move: H_in; move/IH {IH} => IH.
  have H_u' := H_u.
  move: H_u'; move/IH {IH}.
  rewrite /holds /= => IH st; rewrite findUnL.
  + case: ifP; last by move => H_in H_f; exact: IH.
    by rewrite domPt inE eq_sym; move/eqP.
  + by case: validUn; rewrite ?validPt ?valid_initState'//;
     move=>k; rewrite domPt !inE=>/eqP <-;
     rewrite dom_initState' //; move/negP: H_ni.
Qed.

Lemma Coh_init : Coh initWorld.
Proof.
rewrite /initWorld/localState/=; split.
- apply: valid_initState'.
  exact: enum_uniq.
- by move => n; exact: holds_Init_state.
(* - move => n; apply: holds_Init_state. *)
(*   by rewrite /blockTree /= validPt. *)
- move => n; apply: holds_Init_state.
  rewrite/validH/blockTree /= => h b b' H.
  by move: (findPt_inv H); elim=>->->.
- move => n; apply: holds_Init_state.
  by rewrite/has_init_block/blockTree findPt.
- move => n; exact: holds_Init_state.
Qed.

Lemma Coh_step w w' q:
  system_step w w' q -> Coh w'.
Proof.
move=>S; (have: system_step w w' q by done)=>S'.
case: S'.
(* Idle *)
by case=>Cw <-.
(* Deliver *)
- move=> p st [H1 H2 (* H3 *) H4 H5 H6] _ iF sF;
  case P: (procMsg _ _ _)=>[st' ms].
  move=>->; split;
    do? [rewrite /holds/localState; move=> n stN; rewrite findU=>/=].
  + rewrite /localState validU=>/=; apply H1.
  + Coh_step_case n (dst p) H2 F; move/eqP: (H2 (dst p) _ sF)=>Id.
    move: (procMsg_id_constant st (src p) (msg p) (ts q)).
    by move/eqP in B; subst n; rewrite Id=>->; rewrite P.
  (* + Coh_step_case n (dst p) H3 F; move: (H3 (dst p) _ sF)=>V. *)
  (*   by move: (procMsg_valid (src p) (msg p) (ts q) V); rewrite P. *)
  + Coh_step_case n (dst p) H4 F.
    move: (H4 (dst p) _ sF)=>VH;
    rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _.
    move=>V; move: (procMsg_valid V)=>v; specialize (VH v).
    by apply procMsg_validH.
  + Coh_step_case n (dst p) H5 F.
    move=>V; move: (H4 (dst p) _ sF)=>VH;
    rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=>Eq _.
    rewrite -Eq in V *; move: (procMsg_valid V)=>v.
    move: (H5 (dst p) _ sF v); move: (VH v).
    by apply procMsg_has_init_block=>//=.
  + Coh_step_case n (dst p) H6 F.
    move: (H4 (dst p) _ sF)=>VH;
    rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _.
    by move: (H6 (dst p) _ sF); apply procMsg_peers_uniq.

(* Intern *)
- move=> proc t st [H1 H2 (* H3 *) H4 H5 H6] _ sF.
  case P: (procInt _ _ _)=>[st' ms].
  move=>->; split;
    do? [rewrite /holds/localState; move=> n stN; rewrite findU=>/=].
  + rewrite /localState validU=>/=; apply H1.
  + Coh_step_case n proc H2 F; move/eqP: (H2 proc _ sF)=>Id.
    move: (procInt_id_constant st t (ts q)).
    by move/eqP in B; subst n; rewrite Id=>->; rewrite P.
  (* + Coh_step_case n proc H3 F; move: (H3 proc _ sF)=>V. *)
  (*   by move: (procInt_valid st t (ts q)); rewrite P/==><-. *)
  + Coh_step_case n proc H4 F;
    move=>V; move: (H4 proc _ sF)=>VH;
    rewrite [procInt _ _ _] surjective_pairing in P; case: P=>Eq _.
    rewrite -Eq in V *; move: (procInt_valid V)=>v; move: (VH v).
    by apply procInt_validH.
  + Coh_step_case n proc H5 F.
    move=>V; move: (H4 proc _ sF)=>VH;
    rewrite [procInt _ _ _] surjective_pairing in P; case: P=>Eq _;
    rewrite -Eq in V *; move: (procInt_valid V)=>v; move: (VH v)=>vh.
    by move: (H5 proc _ sF v); apply procInt_has_init_block.
  + Coh_step_case n proc H6 F.
    move: (H4 proc _ sF)=>VH;
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
  forall (n : Address) (st st' : State),
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

Lemma no_change_still_holds (w w' : World) (n : Address) q st cond:
  find n (localState w) = Some st ->
  holds n w cond ->
  system_step w w' q ->
  find n (localState w') = Some st ->
  holds n w' cond.
Proof.
move=>f h S sF st' s'F; rewrite s'F in sF; case: sF=>->.
by move: (h st f).
Qed.

Lemma no_change_has_held (w w' : World) (n : Address) q st cond:
  find n (localState w) = Some st ->
  system_step w w' q->
  holds n w' cond ->
  find n (localState w') = Some st ->
  holds n w cond.
Proof.
move=> f S h sF st' s'F.
by rewrite f in s'F; case: s'F=><-; move: (h st sF).
Qed.

End ConsensusNetwork.

Module Network (P : ConsensusParams) (F : Forest P)
       (Pr : ConsensusProtocol P F) (Ns : NetState P F Pr)
        <: ConsensusNetwork P F Pr Ns.

Include ConsensusNetwork P F Pr Ns.
End Network.