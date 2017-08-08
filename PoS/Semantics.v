From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Relations.
Require Import Protocol Blockchain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Number of nodes *)
Parameter N : nat.

(* Network semantics *)
Definition PacketSoup := seq Packet.

Definition StateMap := union_map [ordType of nid] State.

Fixpoint initState' n : StateMap :=
  if n is n'.+1 then (n \\-> Init n) \+ (initState' n') else Unit.

(* Master-lemma, proving a conjunction of two mutually-necessary facts *)
Lemma initStateValidDom n : dom (initState' n) =i iota 1 n /\ valid (initState' n).
Proof.
elim: n=>/=[|n [H1 H2]]; first by rewrite valid_unit dom0.
split; last first.
- case: validUn; rewrite ?um_validPt ?H2//. 
  move=>k; rewrite um_domPt inE=>/eqP Z; subst k.
  by rewrite H1 mem_iota=>/andP[_]; rewrite add1n ltnn. 
move=>z; rewrite domUn !inE !um_domPt !inE.
case B: (z == 1)=>//=.
- move/eqP: B=>B; subst z=>/=; apply/andP; split; last first.
  + by rewrite orbC H1 mem_iota/= addnC addn1; case: n {H1 H2}=>//.
  case: validUn; rewrite ?um_validPt ?H2//. 
  move=>k; rewrite um_domPt inE=>/eqP Z; subst k.
  by rewrite H1 mem_iota=>/andP[_]; rewrite add1n ltnn. 
case C: (z \in iota 2 n).
- apply/andP; split; last first.
  + rewrite orbC H1 mem_iota/= addnC addn1; rewrite mem_iota in C.
    case/andP: C=>H3 H4; rewrite eq_sym.
    rewrite addnC addn2 in H4; clear B.
    case B: (z == n.+1); rewrite orbC//=.
    rewrite ltnS leq_eqVlt B/= in H4.
    by rewrite H4 andbC/=; by case: {B H4} z H3.
  case: validUn; rewrite ?um_validPt ?H2//. 
  move=>k; rewrite um_domPt inE=>/eqP Z; subst k. 
  by rewrite H1 mem_iota=>/andP[_]; rewrite add1n ltnn. 
rewrite H1; apply/negP=>/andP[_]/orP[].
- move/eqP=>Z; subst z; rewrite mem_iota in C.
  move/negP: C=>C; apply: C; rewrite addnC addn2.
  rewrite andbC ltnSn/=; clear H1 H2.
  by move/negbT: B; case: n.
rewrite !mem_iota in C *=>/andP[]H3 H4.
move/negP: C=>C; apply: C; apply/andP; split.
- by clear H4; case: z H3 B=>//z _; case: z=>//.
rewrite addnC addn1 in H4; rewrite addnC.
by rewrite addn2 -[n.+2]addn1; apply: ltn_addr. 
Qed.

Lemma valid_initState n : valid (initState' n).
Proof. by case: (initStateValidDom n). Qed.

Lemma dom_initState n : dom (initState' n) =i iota 1 n.
Proof. by case: (initStateValidDom n). Qed.

Definition initState := initState' N.

Record World :=
  mkW {
    localState : StateMap;
    inFlightMsgs : PacketSoup;
    consumedMsgs : PacketSoup;
  }.

Definition initWorld := mkW initState [::] [::].

(* Don't you worry about uniqueness of the messages? *)
Inductive system_step (w w' : World) : Prop :=
| Idle of w = w'

| Deliver (p : Packet) (st : State) of
      p \in inFlightMsgs w &
      find (dst p) (localState w) = Some st &
      let: (st', ms) := procMsg st (msg p) in
      w' = mkW (upd (dst p) st' (localState w))
               (ms ++ seq.rem p (inFlightMsgs w))
               (rcons (consumedMsgs w) p)

| Intern (proc : nid) (t : InternalTransition) (st : State) of
      find proc (localState w) = Some st &
      let: (st', ms) := procInt st t in
      w' = mkW (upd proc st' (localState w))
               (ms ++ (inFlightMsgs w))
               (consumedMsgs w).

Definition system_step_star := clos_refl_trans_n1 _ system_step.

Definition reachable (w w' : World) := system_step_star w w'.

(* TODO: define a relation that "reconstructs" an "ideal" blockchain *)
(* from a given world, and prove its properties (e.g., functionality, *)
(* meaning that one world corresponds to one blobkchain *)
(* precisely). This might require to state additional "coherence" *)
(* properties of the world, such as block-trees of the majority of
involved peers are not _too different_. *)

Definition holds (n : nid) (w : World) (cond : State -> Prop) :=
  forall (st : State),
    find n (localState w) = Some st -> cond st.

Definition Coh (w : World) :=
  forall (n : nid),
    (* IDs match *)
    holds n w (fun st => id st == n).

Lemma Coh_init : Coh initWorld.
Proof.
move=>n st.
rewrite /initWorld/initState/localState/=.
(* Since the state is constructed inductively, use induction on N *)
elim: N=>//=[|n' Hi].
  (* Using facts about union-maps. *)
- Search _ (find) (Some).
  move/find_some.
  (* Domain of an empty map should be empty, right? *)
  Search _ (dom _) (Unit).
  rewrite dom0.
  (* Fiddling with \in predicate *)
  rewrite inE.
  done.

(* The main induction transition. *)
(* Can we doe somthingabout find of a union? *)
Search _ (find) (_ \+ _).
rewrite findUnL; last first.
- case: validUn; rewrite ?um_validPt ?valid_initState//.
  move=>k; rewrite um_domPt !inE=>/eqP Z; subst k.
  by rewrite dom_initState mem_iota addnC addn1 ltnn andbC. 
case: ifP=>//D.
rewrite um_domPt inE in D; move/eqP:D=>D; subst n.
by rewrite um_findPt; case=><-.  
Qed.  
  